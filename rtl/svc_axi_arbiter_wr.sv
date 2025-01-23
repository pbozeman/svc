`ifndef SVC_AXI_ARBITER_WR_SV
`define SVC_AXI_ARBITER_WR_SV

`include "svc.sv"
`include "svc_arbiter.sv"
`include "svc_skidbuf.sv"

//
// AXI write arbiter from N managers to 1 subordinate.
//
module svc_axi_arbiter_wr #(
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
    output logic                      m_axi_bready
);
  // id + addr + len + size + burst
  localparam SKIDBUF_AW_WIDTH = AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2;

  // data + strb + last
  localparam SKIDBUF_W_WIDTH = AXI_DATA_WIDTH + 2 + 1;

  // id + resp
  localparam SKIDBUF_B_WIDTH = AXI_ID_WIDTH + 2;

  localparam GRANT_IDX_WIDTH = $clog2(NUM_M);

  logic [          NUM_M-1:0]                     request_mask;

  logic                                           grant_valid;
  logic                                           grant_done;
  logic [GRANT_IDX_WIDTH-1:0]                     grant_idx;

  logic [          NUM_M-1:0]                     sb_awvalid;
  logic [          NUM_M-1:0][  AXI_ID_WIDTH-1:0] sb_awid;
  logic [          NUM_M-1:0][AXI_ADDR_WIDTH-1:0] sb_awaddr;
  logic [          NUM_M-1:0][               7:0] sb_awlen;
  logic [          NUM_M-1:0][               2:0] sb_awsize;
  logic [          NUM_M-1:0][               1:0] sb_awburst;
  logic [          NUM_M-1:0]                     sb_awready;

  logic [          NUM_M-1:0]                     sb_wvalid;
  logic [          NUM_M-1:0][AXI_DATA_WIDTH-1:0] sb_wdata;
  logic [          NUM_M-1:0][AXI_STRB_WIDTH-1:0] sb_wstrb;
  logic [          NUM_M-1:0]                     sb_wlast;
  logic [          NUM_M-1:0]                     sb_wready;

  logic [          NUM_M-1:0]                     sb_bready;

  logic                                           aw_accepted;
  logic                                           aw_accepted_next;

  logic [   AXI_ID_WIDTH-1:0]                     b_bid;
  logic [GRANT_IDX_WIDTH-1:0]                     b_grant_idx;

  //-------------------------------------------------------------------------
  //
  // Write request/address processing
  //
  //-------------------------------------------------------------------------

  // aw/w channel skid buffs
  for (genvar i = 0; i < NUM_M; i++) begin : gen_aw_sb
    // aw
    svc_skidbuf #(
        .DATA_WIDTH(SKIDBUF_AW_WIDTH)
    ) svc_skidbuf_ar_i (
        .clk(clk),
        .rst_n(rst_n),
        .i_valid(s_axi_awvalid[i] && s_axi_awready[i]),
        .i_data({
          s_axi_awid[i],
          s_axi_awaddr[i],
          s_axi_awlen[i],
          s_axi_awsize[i],
          s_axi_awburst[i]
        }),
        .o_ready(s_axi_awready[i]),
        .i_ready(sb_awready[i]),
        .o_data({
          sb_awid[i], sb_awaddr[i], sb_awlen[i], sb_awsize[i], sb_awburst[i]
        }),
        .o_valid(sb_awvalid[i])
    );

    // w
    svc_skidbuf #(
        .DATA_WIDTH(SKIDBUF_W_WIDTH)
    ) svc_skidbuf_w_i (
        .clk    (clk),
        .rst_n  (rst_n),
        .i_valid(s_axi_wvalid[i] && s_axi_wready[i]),
        .i_data ({s_axi_wdata[i], s_axi_wstrb[i], s_axi_wlast[i]}),
        .o_ready(s_axi_wready[i]),
        .i_ready(sb_wready[i]),
        .o_data ({sb_wdata[i], sb_wstrb[i], sb_wlast[i]}),
        .o_valid(sb_wvalid[i])
    );
  end

  // arbiter
  //
  // Write grants happen on awvalid and are held through wlast. In theory this
  // prevents a downstream from pipelining the setup of the next downstream
  // request if W processing happens a clock after AW, but that's not the case
  // for any svc modules. Revist this if that changes. Keep the arbitration
  // design simple for now.
  //
  // If we have the grant, we don't want to request it again because the sb
  // will still be valid until ready raises.
  assign request_mask = grant_valid ? ~(1 << grant_idx) : '1;
  assign grant_done   = m_axi_wvalid && m_axi_wready && m_axi_wlast;

  svc_arbiter #(
      .NUM_M(NUM_M)
  ) svc_arbiter_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .request    (sb_awvalid & request_mask),
      .done       (m_axi_wvalid && m_axi_wready && m_axi_wlast),
      .grant_valid(grant_valid),
      .grant_idx  (grant_idx)
  );

  always_comb begin
    aw_accepted_next = aw_accepted;

    if (grant_done) begin
      aw_accepted_next = 1'b0;
    end

    if (m_axi_awvalid && m_axi_awready) begin
      aw_accepted_next = 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      aw_accepted <= 1'b0;
    end else begin
      aw_accepted <= aw_accepted_next;
    end
  end

  //
  // Muxing
  //
  // AW out to subordinate mux
  assign m_axi_awvalid = grant_valid && !aw_accepted;
  assign m_axi_awid    = grant_valid ? {grant_idx, sb_awid[grant_idx]} : 0;
  assign m_axi_awaddr  = grant_valid ? sb_awaddr[grant_idx] : 0;
  assign m_axi_awlen   = grant_valid ? sb_awlen[grant_idx] : 0;
  assign m_axi_awsize  = grant_valid ? sb_awsize[grant_idx] : 0;
  assign m_axi_awburst = grant_valid ? sb_awburst[grant_idx] : 0;

  // AW in from subordinate mux
  always_comb begin
    sb_awready = '0;
    if (grant_valid) begin
      sb_awready[grant_idx] = m_axi_awready;
    end
  end

  // W out mux to subordinate mux
  assign m_axi_wvalid = grant_valid ? sb_wvalid[grant_idx] : 0;
  assign m_axi_wdata  = grant_valid ? sb_wdata[grant_idx] : 0;
  assign m_axi_wstrb  = grant_valid ? sb_wstrb[grant_idx] : 0;
  assign m_axi_wlast  = grant_valid ? sb_wlast[grant_idx] : 0;

  // W in from subordinate mux
  always_comb begin
    sb_wready = '0;
    if (grant_valid) begin
      sb_wready[grant_idx] = m_axi_wready;
    end
  end

  //-------------------------------------------------------------------------
  //
  // B/write response processing
  //
  //-------------------------------------------------------------------------
  //
  assign {b_grant_idx, b_bid} = m_axi_bid;
  assign m_axi_bready         = m_axi_bvalid ? sb_bready[b_grant_idx] : 1'b0;

  //
  // b channel skid buffers
  //
  // Note: these also are doing the muxed responses
  //
  for (genvar i = 0; i < NUM_M; i++) begin : gen_b_sb
    svc_skidbuf #(
        .DATA_WIDTH(SKIDBUF_B_WIDTH),
        .OPT_OUTREG(1)
    ) svc_skidbuf_r_i (
        .clk  (clk),
        .rst_n(rst_n),

        .i_valid(b_grant_idx == i && m_axi_bvalid),
        .i_data ({b_bid, m_axi_bresp}),
        .o_ready(sb_bready[i]),

        .i_ready(s_axi_bvalid[i] && s_axi_bready[i]),
        .o_data ({s_axi_bid[i], s_axi_bresp[i]}),
        .o_valid(s_axi_bvalid[i])
    );
  end

endmodule
`endif
