`ifndef SVC_AXI_BURST_ADAPTER_WR_SV
`define SVC_AXI_BURST_ADAPTER_WR_SV

`include "svc.sv"
`include "svc_axi_burst_iter_ax.sv"
`include "svc_skidbuf.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

// AXI to AXI burst adapter where n beat bursts are split into 1 beat bursts.
//
// This is useful as an adapter step prior to feeding a bursting master into
// an aribiter, preventing starvation of others masters while the burst is
// onging.
//
// Note: this has very similar functionality to axi_axil_adapter and
// axi_axil_reflector, but with a slightly different implementation of how
// last tracking is done for the b-channel. The axil adapter could possibly
// be redone using this module.
//
// TODO: once everything settles down, decide if the potential refactor
// described above is worth it.

module svc_axi_burst_adapter_wr #(
    parameter AXI_ADDR_WIDTH           = 8,
    parameter AXI_DATA_WIDTH           = 16,
    parameter AXI_STRB_WIDTH           = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH             = 4,
    parameter OUTSTANDING_WRITES_WIDTH = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_awvalid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [               7:0] s_axi_awlen,
    input  logic [               2:0] s_axi_awsize,
    input  logic [               1:0] s_axi_awburst,
    output logic                      s_axi_awready,
    input  logic                      s_axi_wvalid,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                      s_axi_wlast,
    output logic                      s_axi_wready,
    output logic                      s_axi_bvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [               1:0] s_axi_bresp,
    input  logic                      s_axi_bready,

    //
    // AXI manager interface
    //
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
    output logic                      m_axi_bready
);
  localparam AW = AXI_ADDR_WIDTH;
  localparam IW = AXI_ID_WIDTH;

  logic          split_awvalid;
  logic [AW-1:0] split_awaddr;
  logic [IW-1:0] split_awid;
  logic [   7:0] split_awlen;
  logic [   2:0] split_awsize;
  logic [   1:0] split_awburst;
  logic          split_last;
  logic          split_awready;

  logic          b_last;

  logic          s_axi_bvalid_next;
  logic [IW-1:0] s_axi_bid_next;
  logic [   1:0] s_axi_bresp_next;

  logic          fifo_b_w_full;
  logic          fifo_b_r_empty;

  logic          sb_m_bvalid;
  logic [IW-1:0] sb_m_bid;
  logic [   1:0] sb_m_bresp;
  logic          sb_m_bready;

  //-------------------------------------------------------------------------
  //
  // AW channel
  //
  //-------------------------------------------------------------------------

  // split the burst
  //
  // This already registers its signals, so we don't need an incoming sb.
  svc_axi_burst_iter_ax #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_burst_iter_aw_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_valid(s_axi_awvalid),
      .s_addr (s_axi_awaddr),
      .s_id   (s_axi_awid),
      .s_len  (s_axi_awlen),
      .s_size (s_axi_awsize),
      .s_burst(s_axi_awburst),
      .s_ready(s_axi_awready),

      .m_valid(split_awvalid),
      .m_addr (split_awaddr),
      .m_id   (split_awid),
      .m_len  (split_awlen),
      .m_size (split_awsize),
      .m_burst(split_awburst),
      .m_last (split_last),
      .m_ready(split_awready)
  );

  assign split_awready = m_axi_awready && !fifo_b_w_full;

  assign m_axi_awvalid = split_awvalid && !fifo_b_w_full;
  assign m_axi_awaddr  = split_awaddr;
  assign m_axi_awid    = split_awid;
  assign m_axi_awlen   = split_awlen;
  assign m_axi_awsize  = split_awsize;
  assign m_axi_awburst = split_awburst;

  //-------------------------------------------------------------------------
  //
  // W channel
  //
  //-------------------------------------------------------------------------
  assign m_axi_wvalid  = s_axi_wvalid;
  assign m_axi_wdata   = s_axi_wdata;
  assign m_axi_wstrb   = s_axi_wstrb;
  assign m_axi_wlast   = 1'b1;
  assign s_axi_wready  = m_axi_wready;

  //-------------------------------------------------------------------------
  //
  // B channel
  //
  //-------------------------------------------------------------------------
  svc_skidbuf #(
      .DATA_WIDTH(AXI_ID_WIDTH + 2)
  ) svc_skidbuf_b_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(m_axi_bvalid),
      .i_data ({m_axi_bid, m_axi_bresp}),
      .o_ready(m_axi_bready),

      .i_ready(sb_m_bready),
      .o_data ({sb_m_bid, sb_m_bresp}),
      .o_valid(sb_m_bvalid)
  );

  // last io tracking
  svc_sync_fifo #(
      .DATA_WIDTH(1),
      .ADDR_WIDTH(OUTSTANDING_WRITES_WIDTH)
  ) svc_sync_fifo_b_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .clr        (1'b0),
      .w_inc      (split_awvalid && split_awready),
      .w_data     (split_last),
      .w_full     (fifo_b_w_full),
      .w_half_full(),
      .r_inc      (sb_m_bvalid && sb_m_bready),
      .r_data     (b_last),
      .r_empty    (fifo_b_r_empty)
  );

  assign sb_m_bready = !fifo_b_r_empty && (!s_axi_bvalid || s_axi_bready);

  always_comb begin
    s_axi_bvalid_next = s_axi_bvalid && !s_axi_bready;
    s_axi_bid_next    = s_axi_bid;
    s_axi_bresp_next  = s_axi_bresp;

    if (sb_m_bvalid && sb_m_bready && b_last) begin
      s_axi_bvalid_next = 1'b1;
      s_axi_bid_next    = sb_m_bid;
      s_axi_bresp_next  = sb_m_bresp;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_bvalid <= 1'b0;
    end else begin
      s_axi_bvalid <= s_axi_bvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    s_axi_bid   <= s_axi_bid_next;
    s_axi_bresp <= s_axi_bresp_next;
  end

  `SVC_UNUSED(s_axi_wlast);

endmodule
`endif
