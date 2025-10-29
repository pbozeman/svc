`ifndef SVC_AXI_TGEN_SV
`define SVC_AXI_TGEN_SV

`include "svc.sv"
`include "svc_axi_tgen_rd.sv"
`include "svc_axi_tgen_wr.sv"

// AXI traffic generator

module svc_axi_tgen #(
    parameter AXI_ADDR_WIDTH = 20,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    input logic clk,
    input logic rst_n,

    input logic w_start,
    input logic r_start,

    output logic busy,

    input logic [AXI_ADDR_WIDTH-1:0] w_base_addr,
    input logic [  AXI_ID_WIDTH-1:0] w_burst_id,
    input logic [               7:0] w_burst_beats,
    input logic [AXI_ADDR_WIDTH-1:0] w_burst_stride,
    input logic [               2:0] w_burst_awsize,
    input logic [              15:0] w_burst_num,

    input logic [AXI_ADDR_WIDTH-1:0] r_base_addr,
    input logic [  AXI_ID_WIDTH-1:0] r_burst_id,
    input logic [               7:0] r_burst_beats,
    input logic [AXI_ADDR_WIDTH-1:0] r_burst_stride,
    input logic [               2:0] r_burst_arsize,
    input logic [              15:0] r_burst_num,

    output logic                      m_axi_awvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    output logic [               1:0] m_axi_awburst,
    input  logic                      m_axi_awready,
    output logic                      m_axi_wvalid,
    output logic [AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    output logic                      m_axi_wlast,
    input  logic                      m_axi_wready,
    input  logic                      m_axi_bvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [               1:0] m_axi_bresp,
    output logic                      m_axi_bready,

    output logic                      m_axi_arvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic                      m_axi_rlast,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [               1:0] m_axi_rresp,
    output logic                      m_axi_rready
);
  logic w_busy;
  logic r_busy;

  assign busy = w_busy || r_busy;

  svc_axi_tgen_wr #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .AXI_STRB_WIDTH(AXI_STRB_WIDTH)
  ) svc_axi_tgen_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .start(w_start),
      .busy (w_busy),

      .base_addr   (w_base_addr),
      .burst_id    (w_burst_id),
      .burst_beats (w_burst_beats),
      .burst_stride(w_burst_stride),
      .burst_awsize(w_burst_awsize),
      .burst_num   (w_burst_num),

      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awlen  (m_axi_awlen),
      .m_axi_awsize (m_axi_awsize),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awready(m_axi_awready),
      .m_axi_wvalid (m_axi_wvalid),
      .m_axi_wdata  (m_axi_wdata),
      .m_axi_wstrb  (m_axi_wstrb),
      .m_axi_wlast  (m_axi_wlast),
      .m_axi_wready (m_axi_wready),
      .m_axi_bvalid (m_axi_bvalid),
      .m_axi_bid    (m_axi_bid),
      .m_axi_bresp  (m_axi_bresp),
      .m_axi_bready (m_axi_bready)
  );

  svc_axi_tgen_rd #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_tgen_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .start(r_start),
      .busy (r_busy),

      .base_addr   (r_base_addr),
      .burst_id    (r_burst_id),
      .burst_beats (r_burst_beats),
      .burst_stride(r_burst_stride),
      .burst_arsize(r_burst_arsize),
      .burst_num   (r_burst_num),

      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arid   (m_axi_arid),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arready(m_axi_arready),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rlast  (m_axi_rlast),
      .m_axi_rid    (m_axi_rid),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rready (m_axi_rready)
  );

endmodule
`endif
