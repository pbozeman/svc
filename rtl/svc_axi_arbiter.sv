`ifndef SVC_AXI_ARBITER_SV
`define SVC_AXI_ARBITER_SV

`include "svc.sv"
`include "svc_axi_arbiter_rd.sv"
`include "svc_axi_arbiter_wr.sv"

//
// AXI arbiter from N managers to 1 subordinate.
//
module svc_axi_arbiter #(
    parameter NUM_M          = 2,
    parameter AXI_ADDR_WIDTH = 8,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH   = 4,
    parameter M_AXI_ID_WIDTH = AXI_ID_WIDTH + $clog2(NUM_M)
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface for N managers
    //
    input  logic [NUM_M-1:0]                     s_axi_awvalid,
    input  logic [NUM_M-1:0][AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [NUM_M-1:0][               7:0] s_axi_awlen,
    input  logic [NUM_M-1:0][               2:0] s_axi_awsize,
    input  logic [NUM_M-1:0][               1:0] s_axi_awburst,
    output logic [NUM_M-1:0]                     s_axi_awready,
    input  logic [NUM_M-1:0]                     s_axi_wvalid,
    input  logic [NUM_M-1:0][AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [NUM_M-1:0][AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic [NUM_M-1:0]                     s_axi_wlast,
    output logic [NUM_M-1:0]                     s_axi_wready,
    output logic [NUM_M-1:0]                     s_axi_bvalid,
    output logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [NUM_M-1:0][               1:0] s_axi_bresp,
    input  logic [NUM_M-1:0]                     s_axi_bready,

    input  logic [NUM_M-1:0]                     s_axi_arvalid,
    input  logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [NUM_M-1:0][AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [NUM_M-1:0][               7:0] s_axi_arlen,
    input  logic [NUM_M-1:0][               2:0] s_axi_arsize,
    input  logic [NUM_M-1:0][               1:0] s_axi_arburst,
    output logic [NUM_M-1:0]                     s_axi_arready,
    output logic [NUM_M-1:0]                     s_axi_rvalid,
    output logic [NUM_M-1:0][  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [NUM_M-1:0][AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [NUM_M-1:0][               1:0] s_axi_rresp,
    output logic [NUM_M-1:0]                     s_axi_rlast,
    input  logic [NUM_M-1:0]                     s_axi_rready,

    //
    // Manager interface to our subordinate
    //
    output logic                      m_axi_awvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [M_AXI_ID_WIDTH-1:0] m_axi_awid,
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
    input  logic [M_AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [               1:0] m_axi_bresp,
    output logic                      m_axi_bready,

    output logic                      m_axi_arvalid,
    output logic [M_AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [M_AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready

);
  svc_axi_arbiter_wr #(
      .NUM_M         (NUM_M),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_arbiter_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awready(s_axi_awready),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wready (s_axi_wready),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bid    (s_axi_bid),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_bready (s_axi_bready),

      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awaddr (m_axi_awaddr),
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

  svc_axi_arbiter_rd #(
      .NUM_M         (NUM_M),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_arbiter_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arid   (s_axi_arid),
      .s_axi_araddr (s_axi_araddr),
      .s_axi_arlen  (s_axi_arlen),
      .s_axi_arsize (s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_arready(s_axi_arready),
      .s_axi_rvalid (s_axi_rvalid),
      .s_axi_rid    (s_axi_rid),
      .s_axi_rdata  (s_axi_rdata),
      .s_axi_rresp  (s_axi_rresp),
      .s_axi_rlast  (s_axi_rlast),
      .s_axi_rready (s_axi_rready),

      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_arid   (m_axi_arid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arready(m_axi_arready),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rid    (m_axi_rid),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rlast  (m_axi_rlast),
      .m_axi_rready (m_axi_rready)
  );

endmodule
`endif
