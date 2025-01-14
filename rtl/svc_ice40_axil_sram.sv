`ifndef SVC_ICE40_AXIL_SRAM_SV
`define SVC_ICE40_AXIL_SRAM_SV

`include "svc.sv"
`include "svc_axil_sram_if.sv"
`include "svc_ice40_sram_io_if.sv"

module svc_ice40_axil_sram #(
    parameter AXIL_ADDR_WIDTH = 4,
    parameter AXIL_DATA_WIDTH = 16,
    parameter AXIL_STRB_WIDTH = (AXIL_DATA_WIDTH / 8),
    parameter LSB             = $clog2(AXIL_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXIL_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXIL_DATA_WIDTH,
    parameter SRAM_STRB_WIDTH = AXIL_STRB_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI-Lite subordinate interface
    //
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic [                1:0] s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    //
    // io to/from the async sram chip
    //
    output logic [SRAM_ADDR_WIDTH-1:0] sram_io_addr,
`ifndef FORMAL
    inout  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`else
    input  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data,
`endif
    output logic                       sram_io_we_n,
    output logic                       sram_io_oe_n,
    output logic                       sram_io_ce_n
);
  logic                       sram_cmd_valid;
  logic                       sram_cmd_ready;
  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr;
  logic                       sram_cmd_wr_en;
  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data;
  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb;

  logic                       sram_resp_rd_valid;
  logic                       sram_resp_rd_ready;
  logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data;

  svc_axil_sram_if #(
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH)
  ) svc_axil_sram_if_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_awaddr (s_axil_awaddr),
      .s_axil_awvalid(s_axil_awvalid),
      .s_axil_awready(s_axil_awready),
      .s_axil_wdata  (s_axil_wdata),
      .s_axil_wstrb  (s_axil_wstrb),
      .s_axil_wvalid (s_axil_wvalid),
      .s_axil_wready (s_axil_wready),
      .s_axil_bresp  (s_axil_bresp),
      .s_axil_bvalid (s_axil_bvalid),
      .s_axil_bready (s_axil_bready),

      .s_axil_arvalid(s_axil_arvalid),
      .s_axil_araddr (s_axil_araddr),
      .s_axil_arready(s_axil_arready),
      .s_axil_rdata  (s_axil_rdata),
      .s_axil_rresp  (s_axil_rresp),
      .s_axil_rvalid (s_axil_rvalid),
      .s_axil_rready (s_axil_rready),

      .sram_cmd_valid    (sram_cmd_valid),
      .sram_cmd_ready    (sram_cmd_ready),
      .sram_cmd_addr     (sram_cmd_addr),
      .sram_cmd_wr_en    (sram_cmd_wr_en),
      .sram_cmd_wr_data  (sram_cmd_wr_data),
      .sram_cmd_wr_strb  (sram_cmd_wr_strb),
      .sram_resp_rd_valid(sram_resp_rd_valid),
      .sram_resp_rd_ready(sram_resp_rd_ready),
      .sram_resp_rd_data (sram_resp_rd_data)
  );

  svc_ice40_sram_io_if #(
      .SRAM_ADDR_WIDTH(SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH(SRAM_DATA_WIDTH)
  ) svc_ice40_sram_io_if_i (
      .clk  (clk),
      .rst_n(rst_n),

      .sram_cmd_valid  (sram_cmd_valid),
      .sram_cmd_ready  (sram_cmd_ready),
      .sram_cmd_addr   (sram_cmd_addr),
      .sram_cmd_wr_en  (sram_cmd_wr_en),
      .sram_cmd_wr_data(sram_cmd_wr_data),
      .sram_cmd_wr_strb(sram_cmd_wr_strb),

      .sram_resp_rd_valid(sram_resp_rd_valid),
      .sram_resp_rd_ready(sram_resp_rd_ready),
      .sram_resp_rd_data (sram_resp_rd_data),

      .sram_io_addr(sram_io_addr),
      .sram_io_data(sram_io_data),
      .sram_io_we_n(sram_io_we_n),
      .sram_io_oe_n(sram_io_oe_n),
      .sram_io_ce_n(sram_io_ce_n)
  );

`ifdef FORMAL
`ifdef FORMAL_SVC_ICE40_AXIL_SRAM
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

`ifdef FORMAL_SVC_ICE40_AXIL_SRAM
  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  //
  // assumptions
  //
  //
  // assumptions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (s_axil_wvalid) begin
        `ASSUME(am_strb, s_axil_wstrb == 0);
      end
    end
  end

  faxil_slave #(
      .C_AXI_DATA_WIDTH  (AXIL_DATA_WIDTH),
      .C_AXI_ADDR_WIDTH  (AXIL_ADDR_WIDTH),
      .F_AXI_MAXWAIT     (4),
      .F_AXI_MAXDELAY    (8),
      .F_AXI_MAXRSTALL   (0),
      .F_OPT_INITIAL     (0),
      .F_OPT_ASSUME_RESET(1)
  ) faxil_subordinate_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      // Write address channel
      .i_axi_awvalid(s_axil_awvalid),
      .i_axi_awready(s_axil_awready),
      .i_axi_awaddr (s_axil_awaddr),
      .i_axi_awprot (0),

      // Write data
      .i_axi_wready(s_axil_wready),
      .i_axi_wdata (s_axil_wdata),
      .i_axi_wstrb (s_axil_wstrb),
      .i_axi_wvalid(s_axil_wvalid),

      // Write response
      .i_axi_bresp (s_axil_bresp),
      .i_axi_bvalid(s_axil_bvalid),
      .i_axi_bready(s_axil_bready),

      // Read address
      .i_axi_arvalid(s_axil_arvalid),
      .i_axi_arready(s_axil_arready),
      .i_axi_araddr (s_axil_araddr),
      .i_axi_arprot (0),

      // Read data return
      .i_axi_rvalid(s_axil_rvalid),
      .i_axi_rready(s_axil_rready),
      .i_axi_rdata (s_axil_rdata),
      .i_axi_rresp (s_axil_rresp),

      // Formal check variables
      .f_axi_rd_outstanding (),
      .f_axi_wr_outstanding (),
      .f_axi_awr_outstanding()
  );
`endif
`endif

endmodule

`endif
