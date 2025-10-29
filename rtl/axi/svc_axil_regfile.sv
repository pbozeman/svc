`ifndef SVC_AXIL_REGFILE_SV
`define SVC_AXIL_REGFILE_SV

`include "svc.sv"
`include "svc_skidbuf.sv"
`include "svc_unused.sv"

//
// This module implements a generic AXI-Lite register file.
//
// It's main use case is for CSRs (control & status registers)
//
// The DATA_WIDTH and AXIL_DATA_WIDTH are separate params in the event that
// the registers are smaller than the data bus.
//
// Using this when the inputs are not dynamic, i.e. they are just whatever is
// in the reg, is fairly straight forward. When the register is a read-only
// that is based on a computation, the usage is a bit weird and maybe
// the interface should change to better accommodate it (or maybe split
// computed r/o regs into their own module. See svc-examples/rtl/axi_perf
// for a dynamic example.)
//
module svc_axil_regfile #(
    parameter         N               = 5,
    parameter         DATA_WIDTH      = 32,
    parameter         AXIL_ADDR_WIDTH = 32,
    parameter         AXIL_DATA_WIDTH = 32,
    parameter         AXIL_STRB_WIDTH = AXIL_DATA_WIDTH / 8,
    parameter [N-1:0] REG_WRITE_MASK  = '1
) (
    input logic clk,
    input logic rst_n,

    input  logic [N-1:0][DATA_WIDTH-1:0] r_val,
    output logic [N-1:0][DATA_WIDTH-1:0] r_val_next,

    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic                       s_axil_bvalid,
    output logic [                1:0] s_axil_bresp,
    input  logic                       s_axil_bready,

    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,
    output logic                       s_axil_rvalid,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    input  logic                       s_axil_rready
);
  // Convert byte address to word address (reg idx)
  localparam R_ADDRLSB = $clog2(AXIL_DATA_WIDTH) - 3;
  localparam R_W = $clog2(N);

  localparam R_DW = DATA_WIDTH;
  localparam A_DW = AXIL_DATA_WIDTH;
  localparam A_SW = AXIL_STRB_WIDTH;

  //--------------------------------------------------------------------------
  // Write path
  //--------------------------------------------------------------------------
  logic            sb_awvalid;
  logic [ R_W-1:0] sb_wreg;
  logic            sb_awready;

  // TODO: sb_wdata and sb_wstrb could be reduced in size when the reg size is
  // smaller than the axil bus. If/when this is changed, remove the casts
  // when assigning the reg.
  logic            sb_wvalid;
  logic [A_DW-1:0] sb_wdata;
  logic [A_SW-1:0] sb_wstrb;
  logic            sb_wready;

  logic            s_axil_bvalid_next;
  logic [     1:0] s_axil_bresp_next;

  // Skid buffer for write address channel
  svc_skidbuf #(
      .DATA_WIDTH(R_W)
  ) svc_skidbuf_aw (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_awvalid),
      .i_data (R_W'(s_axil_awaddr[AXIL_ADDR_WIDTH-1:R_ADDRLSB])),
      .o_ready(s_axil_awready),

      .o_valid(sb_awvalid),
      .o_data (sb_wreg),
      .i_ready(sb_awready)
  );

  // Skid buffer for write data channel
  svc_skidbuf #(
      .DATA_WIDTH(AXIL_DATA_WIDTH + AXIL_STRB_WIDTH)
  ) svc_skidbuf_w (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_wvalid),
      .i_data ({s_axil_wstrb, s_axil_wdata}),
      .o_ready(s_axil_wready),

      .o_valid(sb_wvalid),
      .o_data ({sb_wstrb, sb_wdata}),
      .i_ready(sb_wready)
  );

  //
  // Write handling
  //
  always_comb begin
    sb_awready         = 1'b0;
    sb_wready          = 1'b0;

    s_axil_bvalid_next = s_axil_bvalid && !s_axil_bready;
    s_axil_bresp_next  = s_axil_bresp;

    r_val_next         = r_val;

    // do both an incoming check and outgoing check here,
    // since we are going to set bvalid
    if (sb_awvalid && sb_wvalid && (!s_axil_bvalid || s_axil_bready)) begin
      sb_awready         = 1'b1;
      sb_wready          = 1'b1;
      s_axil_bvalid_next = 1'b1;

      // Check if this is a valid register address
      if (sb_wreg < N) begin
        if (!REG_WRITE_MASK[sb_wreg]) begin
          // SLVERR - register is read-only
          s_axil_bresp_next = 2'b10;
        end else if (sb_wstrb != '1) begin
          // SLVERR - partial writes not supported
          s_axil_bresp_next = 2'b10;
        end else begin
          // TODO: remove this cast when the sb changes size. See TODO up at
          // the declaration of sb_wdata.
          r_val_next[sb_wreg] = R_DW'(sb_wdata);
          s_axil_bresp_next   = 2'b00;
        end
      end else begin
        // DECERR - invalid register address
        s_axil_bresp_next = 2'b11;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axil_bvalid <= 1'b0;
      s_axil_bresp  <= 2'b00;
    end else begin
      s_axil_bvalid <= s_axil_bvalid_next;
      s_axil_bresp  <= s_axil_bresp_next;
    end
  end

  //--------------------------------------------------------------------------
  // Read path
  //--------------------------------------------------------------------------
  logic            sb_arvalid;
  logic [ R_W-1:0] sb_rreg;
  logic            sb_arready;

  logic            s_axil_rvalid_next;
  logic [A_DW-1:0] s_axil_rdata_next;
  logic [     1:0] s_axil_rresp_next;

  // Skid buffer for read address channel
  svc_skidbuf #(
      .DATA_WIDTH(R_W)
  ) svc_skidbuf_ar (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_arvalid),
      .i_data (R_W'(s_axil_araddr[AXIL_ADDR_WIDTH-1:R_ADDRLSB])),
      .o_ready(s_axil_arready),

      .o_valid(sb_arvalid),
      .o_data (sb_rreg),
      .i_ready(sb_arready)
  );

  //
  // Read handling
  //
  always_comb begin
    sb_arready         = 1'b0;
    s_axil_rvalid_next = s_axil_rvalid && !s_axil_rready;
    s_axil_rdata_next  = s_axil_rdata;
    s_axil_rresp_next  = s_axil_rresp;

    // do both an incoming check and outgoing check here,
    // since we are going to set rvalid
    if (sb_arvalid && (!s_axil_rvalid || s_axil_rready)) begin
      sb_arready         = 1'b1;
      s_axil_rvalid_next = 1'b1;

      // Check if this is a valid register address
      if (sb_rreg < N) begin
        s_axil_rdata_next = A_DW'(r_val[sb_rreg]);
        s_axil_rresp_next = 2'b00;
      end else begin
        // DECERR - invalid register address
        s_axil_rresp_next = 2'b11;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axil_rvalid <= 1'b0;
      s_axil_rdata  <= '0;
      s_axil_rresp  <= 2'b00;
    end else begin
      s_axil_rvalid <= s_axil_rvalid_next;
      s_axil_rdata  <= s_axil_rdata_next;
      s_axil_rresp  <= s_axil_rresp_next;
    end
  end

  `SVC_UNUSED({s_axil_araddr[R_ADDRLSB-1:0], s_axil_awaddr[R_ADDRLSB-1:0],
               sb_wdata[A_DW-R_DW]});

  // TODO: formal

endmodule
`endif
