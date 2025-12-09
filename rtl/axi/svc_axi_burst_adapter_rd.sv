`ifndef SVC_AXI_BURST_ADAPTER_RD_SV
`define SVC_AXI_BURST_ADAPTER_RD_SV

`include "svc.sv"
`include "svc_axi_burst_iter_ax.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

// AXI to AXI burst adapter where n beat bursts are split into 1 beat bursts.
//
// This is useful as an adapter step prior to feeding a bursting master into
// an arbiter, preventing starvation of others masters while the burst is
// ongoing.
//
// Like the _wr version, this has very similar structure to it's adapter
// counter part. Decide later if they should get refactored into a common
// implementation.

module svc_axi_burst_adapter_rd #(
    parameter AXI_ADDR_WIDTH          = 8,
    parameter AXI_DATA_WIDTH          = 16,
    parameter AXI_ID_WIDTH            = 4,
    parameter OUTSTANDING_READS_WIDTH = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_arvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [               7:0] s_axi_arlen,
    input  logic [               2:0] s_axi_arsize,
    input  logic [               1:0] s_axi_arburst,
    output logic                      s_axi_arready,
    output logic                      s_axi_rvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic                      s_axi_rlast,
    input  logic                      s_axi_rready,

    //
    // AXI manager interface
    //
    output logic                      m_axi_arvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready
);
  localparam AW = AXI_ADDR_WIDTH;
  localparam IW = AXI_ID_WIDTH;

  logic          split_arvalid;
  logic [AW-1:0] split_araddr;
  logic [IW-1:0] split_arid;
  logic [   7:0] split_arlen;
  logic [   2:0] split_arsize;
  logic [   1:0] split_arburst;
  logic          split_last;
  logic          split_arready;

  logic          fifo_r_w_full;

  //-------------------------------------------------------------------------
  //
  // AR channel
  //
  //-------------------------------------------------------------------------

  // split the burst
  //
  // This already registers its signals, so we don't need an incoming sb.
  svc_axi_burst_iter_ax #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_burst_iter_ar_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_valid(s_axi_arvalid),
      .s_addr (s_axi_araddr),
      .s_id   (s_axi_arid),
      .s_len  (s_axi_arlen),
      .s_size (s_axi_arsize),
      .s_burst(s_axi_arburst),
      .s_ready(s_axi_arready),

      .m_valid(split_arvalid),
      .m_addr (split_araddr),
      .m_id   (split_arid),
      .m_len  (split_arlen),
      .m_size (split_arsize),
      .m_burst(split_arburst),
      .m_last (split_last),
      .m_ready(split_arready)
  );

  assign split_arready = m_axi_arready && !fifo_r_w_full;

  assign m_axi_arvalid = split_arvalid && !fifo_r_w_full;
  assign m_axi_araddr  = split_araddr;
  assign m_axi_arid    = split_arid;
  assign m_axi_arlen   = split_arlen;
  assign m_axi_arsize  = split_arsize;
  assign m_axi_arburst = split_arburst;

  //-------------------------------------------------------------------------
  //
  // R channel
  //
  //-------------------------------------------------------------------------

  // r_last propagation
  svc_sync_fifo #(
      .DATA_WIDTH(1),
      .ADDR_WIDTH(OUTSTANDING_READS_WIDTH)
  ) svc_sync_fifo_r_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (1'b0),

      .w_inc      (split_arvalid && split_arready),
      .w_data     (split_last),
      .w_full     (fifo_r_w_full),
      .w_half_full(),
      .r_inc      (s_axi_rvalid && s_axi_rready),
      .r_data     (s_axi_rlast),
      .r_empty    ()
  );

  assign s_axi_rvalid = m_axi_rvalid;
  assign s_axi_rid    = m_axi_rid;
  assign s_axi_rdata  = m_axi_rdata;
  assign s_axi_rresp  = m_axi_rresp;

  // unlike the _wr version of this, we don't need to include fifo empty in
  // rready condition because the read response will always follow the AR
  // handshake.
  assign m_axi_rready = s_axi_rready;

  `SVC_UNUSED(m_axi_rlast);

endmodule
`endif
