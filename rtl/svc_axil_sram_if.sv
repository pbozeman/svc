`ifndef SVC_AXIL_SRAM_IF_SV
`define SVC_AXIL_SRAM_IF_SV

// verilator lint_off: UNUSEDSIGNAL

`include "svc.sv"
`include "svc_axil_sram_if_rd.sv"
`include "svc_axil_sram_if_wr.sv"

// This is a lightweight wrapper to convert byte based AXI-Lite to an SRAM
// interface. It arbitrates between reads and writes, as the SRAM can only
// do 1 at a time. It also converts the addresses to be word rather than byte
// based. rresp and bresp are always marked as success.
module svc_axil_sram_if #(
    parameter AXIL_ADDR_WIDTH = 20,
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
    // SRAM interface
    //
    output logic                       sram_cmd_valid,
    input  logic                       sram_cmd_ready,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    output logic                       sram_cmd_wr_en,
    output logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    output logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,
    input  logic                       sram_rd_resp_valid,
    output logic                       sram_rd_resp_ready,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_rd_resp_data
);
  typedef enum {
    STATE_IDLE,
    STATE_READ,
    STATE_READ_RESP,
    STATE_WRITE,
    STATE_WRITE_RESP
  } state_t;

  state_t                       state;
  state_t                       state_next;

  logic                         sram_wr_cmd_valid;
  logic                         sram_wr_cmd_ready;
  logic   [SRAM_ADDR_WIDTH-1:0] sram_wr_cmd_addr;
  logic   [SRAM_DATA_WIDTH-1:0] sram_wr_cmd_data;

  logic                         sram_rd_cmd_valid;
  logic                         sram_rd_cmd_ready;
  logic   [SRAM_ADDR_WIDTH-1:0] sram_rd_cmd_addr;

  svc_axil_sram_if_wr #(
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH)
  ) svc_axil_sram_if_wr_i (
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

      .sram_wr_cmd_valid(sram_wr_cmd_valid),
      .sram_wr_cmd_ready(sram_wr_cmd_ready),
      .sram_wr_cmd_addr (sram_wr_cmd_addr),
      .sram_wr_cmd_data (sram_cmd_wr_data),
      .sram_wr_cmd_strb (sram_cmd_wr_strb)
  );

  svc_axil_sram_if_rd #(
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH)
  ) svc_axil_sram_if_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_arvalid(s_axil_arvalid),
      .s_axil_arready(s_axil_arready),
      .s_axil_araddr (s_axil_araddr),
      .s_axil_rdata  (s_axil_rdata),
      .s_axil_rresp  (s_axil_rresp),
      .s_axil_rvalid (s_axil_rvalid),
      .s_axil_rready (s_axil_rready),

      .sram_rd_cmd_valid (sram_rd_cmd_valid),
      .sram_rd_cmd_ready (sram_rd_cmd_ready),
      .sram_rd_cmd_addr  (sram_rd_cmd_addr),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_data (sram_rd_resp_data)
  );

  //
  // next read/write logic with fairness
  //
  logic   pri_read;
  state_t fair_state;
  always_comb begin
    if (pri_read) begin
      if (sram_rd_cmd_valid) begin
        fair_state = STATE_READ;
      end else if (sram_wr_cmd_valid) begin
        fair_state = STATE_WRITE;
      end else begin
        fair_state = STATE_IDLE;
      end
    end else begin
      if (sram_wr_cmd_valid) begin
        fair_state = STATE_WRITE;
      end else if (sram_rd_cmd_valid) begin
        fair_state = STATE_READ;
      end else begin
        fair_state = STATE_IDLE;
      end
    end
  end

  //
  // State machine
  //
  always_comb begin
    pri_read   = 1'b0;
    state_next = state;

    case (state)
      STATE_IDLE: begin
        state_next = fair_state;
      end

      STATE_READ: begin
        if (sram_cmd_ready) begin
          if (!s_axil_rready) begin
            state_next = STATE_READ_RESP;
          end else begin
            state_next = fair_state;
          end
        end
      end

      STATE_READ_RESP: begin
        if (s_axil_rready) begin
          state_next = fair_state;
        end
      end

      STATE_WRITE: begin
        if (sram_cmd_ready) begin
          if (!s_axil_bready) begin
            state_next = STATE_WRITE_RESP;
          end else begin
            pri_read   = 1'b1;
            state_next = fair_state;
          end
        end
      end

      STATE_WRITE_RESP: begin
        if (s_axil_bready) begin
          pri_read   = 1'b1;
          state_next = fair_state;
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  //
  // Mux the signals
  //
  always_comb begin
    sram_cmd_valid    = 1'b0;
    sram_cmd_addr     = '0;
    sram_cmd_wr_en    = 1'b0;

    sram_rd_cmd_ready = 1'b0;
    sram_wr_cmd_ready = 1'b0;

    case (state_next)
      STATE_READ: begin
        sram_cmd_valid    = 1'b1;
        sram_cmd_addr     = sram_rd_cmd_addr;
        sram_rd_cmd_ready = sram_cmd_ready;
      end

      STATE_WRITE: begin
        sram_cmd_valid    = 1'b1;
        sram_cmd_addr     = sram_wr_cmd_addr;
        sram_cmd_wr_en    = 1'b1;
        sram_wr_cmd_ready = sram_cmd_ready;
      end
    endcase
  end

`ifdef FORMAL
  localparam F_LGDEPTH = 4;

  // verilator lint_off: UNUSEDSIGNAL
  wire [F_LGDEPTH-1:0] f_axil_rd_outstanding;
  wire [F_LGDEPTH-1:0] f_axil_wr_outstanding;
  wire [F_LGDEPTH-1:0] f_axil_awr_outstanding;
  // verilator lint_on: UNUSEDSIGNAL

  faxil_slave #(
      .C_AXI_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(AXIL_DATA_WIDTH),
      .F_LGDEPTH       (F_LGDEPTH)
  ) faxil_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      .i_axi_awready(s_axil_awready),
      .i_axi_awaddr (s_axil_awaddr),
      .i_axi_awvalid(s_axil_awvalid),
      .i_axi_awprot ('0),

      .i_axi_wready(s_axil_wready),
      .i_axi_wdata (s_axil_wdata),
      .i_axi_wstrb (s_axil_wstrb),
      .i_axi_wvalid(s_axil_wvalid),

      .i_axi_bready(s_axil_bready),
      .i_axi_bvalid(s_axil_bvalid),
      .i_axi_bresp (s_axil_bresp),

      .i_axi_araddr (s_axil_araddr),
      .i_axi_arvalid(s_axil_arvalid),
      .i_axi_arready(s_axil_arready),
      .i_axi_arprot ('0),

      .i_axi_rvalid(s_axil_rvalid),
      .i_axi_rready(s_axil_rready),
      .i_axi_rdata (s_axil_rdata),
      .i_axi_rresp (s_axil_rresp),

      .f_axi_rd_outstanding (f_axil_rd_outstanding),
      .f_axi_wr_outstanding (f_axil_wr_outstanding),
      .f_axi_awr_outstanding(f_axil_awr_outstanding)
  );

  // Look into properties to use induction and an unbounded check
  // see
  //   https://zipcpu.com/blog/2020/03/08/easyaxil.html
  // and
  //   https://github.com/ZipCPU/wb2axip/blob/master/rtl/demoaxi.v
`endif

endmodule
`endif
