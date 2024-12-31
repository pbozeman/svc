`ifndef SVC_AXI_SRAM_IF_SV
`define SVC_AXI_SRAM_IF_SV

`include "svc.sv"
`include "svc_axi_sram_if_rd.sv"
`include "svc_axi_sram_if_wr.sv"

// TODO: this only hooks up the write side and doesn't arbitrate yet

// This is a lightweight wrapper to convert byte based AXI to an SRAM
// interface. It arbitrates between reads and writes, as the SRAM can only
// do 1 at a time. It also converts the addresses to be word rather than byte
// based. rresp and bresp are always marked as success.
module svc_axi_sram_if #(
    parameter AXI_ADDR_WIDTH  = 20,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_ID_WIDTH    = 4,
    parameter AXI_STRB_WIDTH  = (AXI_DATA_WIDTH / 8),
    parameter LSB             = $clog2(AXI_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXI_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXI_DATA_WIDTH,
    parameter SRAM_ID_WIDTH   = AXI_ID_WIDTH,
    parameter SRAM_STRB_WIDTH = AXI_STRB_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_awvalid,
    output logic                      s_axi_awready,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [               7:0] s_axi_awlen,
    input  logic [               2:0] s_axi_awsize,
    input  logic [               1:0] s_axi_awburst,
    input  logic                      s_axi_wvalid,
    output logic                      s_axi_wready,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                      s_axi_wlast,
    output logic                      s_axi_bvalid,
    input  logic                      s_axi_bready,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [               1:0] s_axi_bresp,

    // verilator lint_off: UNUSEDSIGNAL
    // verilator lint_off: UNDRIVEN
    input  logic                      s_axi_arvalid,
    output logic                      s_axi_arready,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [               7:0] s_axi_arlen,
    input  logic [               2:0] s_axi_arsize,
    input  logic [               1:0] s_axi_arburst,
    output logic                      s_axi_rvalid,
    input  logic                      s_axi_rready,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic                      s_axi_rlast,
    // verilator lint_on: UNUSEDSIGNAL
    // verilator lint_on: UNDRIVEN

    //
    // SRAM interface
    //
    output logic                       sram_cmd_valid,
    input  logic                       sram_cmd_ready,
    output logic [  SRAM_ID_WIDTH-1:0] sram_cmd_id,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    output logic                       sram_cmd_wr_en,
    output logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    output logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,
    // verilator lint_off: UNUSEDSIGNAL
    // verilator lint_off: UNDRIVEN
    input  logic                       sram_rd_resp_valid,
    output logic                       sram_rd_resp_ready,
    input  logic [  SRAM_ID_WIDTH-1:0] sram_rd_resp_id,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_rd_resp_data
    // verilator lint_on: UNUSEDSIGNAL
    // verilator lint_on: UNDRIVEN
);
  logic                       sram_wr_cmd_valid;
  logic                       sram_wr_cmd_ready;
  logic [SRAM_ADDR_WIDTH-1:0] sram_wr_cmd_addr;

  // verilator lint_off: UNUSEDSIGNAL
  // verilator lint_off: UNDRIVEN
  logic                       sram_rd_cmd_valid;
  logic                       sram_rd_cmd_ready;
  logic [SRAM_ADDR_WIDTH-1:0] sram_rd_cmd_addr;
  // verilator lint_on: UNUSEDSIGNAL
  // verilator lint_on: UNDRIVEN

  // TODO: muxing between reads and writes. For now, just try to get
  // the formal verifier to validate the write path.
  assign sram_cmd_valid    = sram_wr_cmd_valid;
  assign sram_cmd_addr     = sram_wr_cmd_addr;
  assign sram_cmd_wr_en    = 1'b1;
  assign sram_wr_cmd_ready = sram_cmd_ready;

  svc_axi_sram_if_wr #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_axi_sram_if_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awready(s_axi_awready),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wready (s_axi_wready),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bready (s_axi_bready),
      .s_axi_bid    (s_axi_bid),

      .sram_wr_cmd_valid(sram_wr_cmd_valid),
      .sram_wr_cmd_ready(sram_wr_cmd_ready),
      .sram_wr_cmd_addr (sram_wr_cmd_addr),
      .sram_wr_cmd_data (sram_cmd_wr_data),
      .sram_wr_cmd_strb (sram_cmd_wr_strb)
  );

  svc_axi_sram_if_rd #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_axi_sram_if_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arready(s_axi_arready),
      .s_axi_arid   (s_axi_arid),
      .s_axi_araddr (s_axi_araddr),
      .s_axi_arlen  (s_axi_arlen),
      .s_axi_arsize (s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_rvalid (s_axi_rvalid),
      .s_axi_rready (s_axi_rready),
      .s_axi_rid    (s_axi_rid),
      .s_axi_rdata  (s_axi_rdata),
      .s_axi_rresp  (s_axi_rresp),
      .s_axi_rlast  (s_axi_rlast),

      .sram_rd_cmd_valid (sram_rd_cmd_valid),
      .sram_rd_cmd_ready (sram_rd_cmd_ready),
      .sram_rd_cmd_id    (sram_cmd_id),
      .sram_rd_cmd_addr  (sram_rd_cmd_addr),
      .sram_rd_resp_valid(sram_rd_resp_valid),
      .sram_rd_resp_ready(sram_rd_resp_ready),
      .sram_rd_resp_id   (sram_rd_resp_id),
      .sram_rd_resp_data (sram_rd_resp_data)
  );

`ifdef FORMAL_BUT_FAXI_SLAVE_IS_BROKEN_SO_DONT_DO_THIS
  // try to run read only at first
  always_comb assume (s_axi_arvalid == 0);

  faxi_slave #(
      .C_AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .C_AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .C_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH)
  ) faxi_slave_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      .i_axi_awvalid(s_axi_awvalid),
      .i_axi_awready(s_axi_awready),
      .i_axi_awid   (s_axi_awid),
      .i_axi_awaddr (s_axi_awaddr),
      .i_axi_awlen  (s_axi_awlen),
      .i_axi_awsize (s_axi_awsize),
      .i_axi_awburst(s_axi_awburst),
      .i_axi_awlock (1'b0),
      .i_axi_awcache('0),
      .i_axi_awprot ('0),
      .i_axi_awqos  ('0),

      // Write Data
      .i_axi_wdata (s_axi_wdata),
      .i_axi_wstrb (s_axi_wstrb),
      .i_axi_wlast (s_axi_wlast),
      .i_axi_wvalid(s_axi_wvalid),
      .i_axi_wready(s_axi_wready),

      // Write response
      .i_axi_bvalid(s_axi_bvalid),
      .i_axi_bready(s_axi_bready),
      .i_axi_bid   (s_axi_bid),
      .i_axi_bresp (s_axi_bresp),

      // Read address channel
      .i_axi_arvalid(s_axi_arvalid),
      .i_axi_arready(s_axi_arready),
      .i_axi_arid   (s_axi_arid),
      .i_axi_araddr (s_axi_araddr),
      .i_axi_arlen  (s_axi_arlen),
      .i_axi_arsize (s_axi_arsize),
      .i_axi_arburst(s_axi_arburst),
      .i_axi_arlock (1'b0),
      .i_axi_arcache('0),
      .i_axi_arprot ('0),
      .i_axi_arqos  ('0),

      // Read data return channel
      .i_axi_rvalid(s_axi_rvalid),
      .i_axi_rready(s_axi_rready),
      .i_axi_rid   (s_axi_rid),
      .i_axi_rdata (s_axi_rdata),
      .i_axi_rresp (s_axi_rresp),
      .i_axi_rlast (s_axi_rlast)
  );
`endif

endmodule
`endif
