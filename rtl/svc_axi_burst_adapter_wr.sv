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
  logic                      sb_s_awvalid;
  logic [AXI_ADDR_WIDTH-1:0] sb_s_awaddr;
  logic [  AXI_ID_WIDTH-1:0] sb_s_awid;
  logic [               7:0] sb_s_awlen;
  logic [               2:0] sb_s_awsize;
  logic [               1:0] sb_s_awburst;
  logic                      sb_s_awready;

  logic                      burst_awready;

  logic                      aw_last;
  logic                      b_last;

  logic                      s_axi_bvalid_next;
  logic [  AXI_ID_WIDTH-1:0] s_axi_bid_next;
  logic [               1:0] s_axi_bresp_next;

  logic                      fifo_b_w_full;
  logic                      fifo_b_r_empty;

  //-------------------------------------------------------------------------
  //
  // AW channel
  //
  //-------------------------------------------------------------------------
  svc_skidbuf #(
      .DATA_WIDTH(AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2)
  ) svc_skidbuf_aw_i (
      .clk(clk),
      .rst_n(rst_n),
      .i_valid(s_axi_awvalid),
      .i_data({
        s_axi_awid, s_axi_awaddr, s_axi_awlen, s_axi_awsize, s_axi_awburst
      }),
      .o_ready(s_axi_awready),
      .i_ready(sb_s_awready),
      .o_data({sb_s_awid, sb_s_awaddr, sb_s_awlen, sb_s_awsize, sb_s_awburst}),
      .o_valid(sb_s_awvalid)
  );

  assign sb_s_awready = (burst_awready && !fifo_b_w_full &&
                         (!m_axi_awvalid || m_axi_awready));

  // split the burst
  svc_axi_burst_iter_ax #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_burst_iter_aw_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_valid(sb_s_awvalid),
      .s_addr (sb_s_awaddr),
      .s_id   (sb_s_awid),
      .s_len  (sb_s_awlen),
      .s_size (sb_s_awsize),
      .s_burst(sb_s_awburst),
      .s_ready(burst_awready),

      .m_valid(m_axi_awvalid),
      .m_addr (m_axi_awaddr),
      .m_id   (m_axi_awid),
      .m_len  (m_axi_awlen),
      .m_size (m_axi_awsize),
      .m_burst(m_axi_awburst),
      .m_last (aw_last),
      .m_ready(m_axi_awready)
  );

  //-------------------------------------------------------------------------
  //
  // W channel
  //
  //-------------------------------------------------------------------------
  assign m_axi_wvalid = s_axi_wvalid;
  assign m_axi_wdata  = s_axi_wdata;
  assign m_axi_wstrb  = s_axi_wstrb;
  assign m_axi_wlast  = 1'b1;
  assign s_axi_wready = m_axi_wready;

  //-------------------------------------------------------------------------
  //
  // B channel
  //
  //-------------------------------------------------------------------------

  // last io tracking
  svc_sync_fifo #(
      .DATA_WIDTH(1),
      .ADDR_WIDTH(OUTSTANDING_WRITES_WIDTH)
  ) svc_sync_fifo_b_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (m_axi_awvalid && m_axi_awready),
      .w_data     (aw_last),
      .w_full     (fifo_b_w_full),
      .w_half_full(),
      .r_inc      (m_axi_bvalid && m_axi_bready),
      .r_data     (b_last),
      .r_empty    (fifo_b_r_empty)
  );

  assign m_axi_bready = !fifo_b_r_empty && (!s_axi_bvalid || s_axi_bready);

  always_comb begin
    s_axi_bvalid_next = s_axi_bvalid && !s_axi_bready;
    s_axi_bid_next    = s_axi_bid;
    s_axi_bresp_next  = s_axi_bresp;

    if (m_axi_bvalid && m_axi_bready && b_last) begin
      s_axi_bvalid_next = 1'b1;
      s_axi_bid_next    = m_axi_bid;
      s_axi_bresp_next  = m_axi_bresp;
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
