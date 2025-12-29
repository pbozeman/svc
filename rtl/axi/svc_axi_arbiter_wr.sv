`ifndef SVC_AXI_ARBITER_WR_SV
`define SVC_AXI_ARBITER_WR_SV

`include "svc.sv"
`include "svc_arbiter.sv"
`include "svc_skidbuf.sv"
`include "svc_sticky_bit.sv"

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
  localparam SKIDBUF_W_WIDTH = AXI_DATA_WIDTH + AXI_STRB_WIDTH + 1;

  // id + resp
  localparam SKIDBUF_B_WIDTH = AXI_ID_WIDTH + 2;

  localparam GRANT_IDX_WIDTH = $clog2(NUM_M);

  logic [          NUM_M-1:0]                     request_mask;

  logic                                           grant_valid;
  logic                                           grant_done;
  logic [GRANT_IDX_WIDTH-1:0]                     grant_idx;

  logic [          NUM_M-1:0]                     sb_s_awvalid;
  logic [          NUM_M-1:0][  AXI_ID_WIDTH-1:0] sb_s_awid;
  logic [          NUM_M-1:0][AXI_ADDR_WIDTH-1:0] sb_s_awaddr;
  logic [          NUM_M-1:0][               7:0] sb_s_awlen;
  logic [          NUM_M-1:0][               2:0] sb_s_awsize;
  logic [          NUM_M-1:0][               1:0] sb_s_awburst;
  logic [          NUM_M-1:0]                     sb_s_awready;

  logic [          NUM_M-1:0]                     sb_s_wvalid;
  logic [          NUM_M-1:0][AXI_DATA_WIDTH-1:0] sb_s_wdata;
  logic [          NUM_M-1:0][AXI_STRB_WIDTH-1:0] sb_s_wstrb;
  logic [          NUM_M-1:0]                     sb_s_wlast;
  logic [          NUM_M-1:0]                     sb_s_wready;

  logic                                           aw_done;
  logic                                           w_done;

  logic [GRANT_IDX_WIDTH-1:0]                     b_grant_idx;

  logic [   AXI_ID_WIDTH-1:0]                     sb_s_bid;
  logic [          NUM_M-1:0]                     sb_s_bready;

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
    ) svc_skidbuf_aw_i (
        .clk(clk),
        .rst_n(rst_n),
        .i_valid(s_axi_awvalid[i]),
        .i_data({
          s_axi_awburst[i],
          s_axi_awsize[i],
          s_axi_awid[i],
          s_axi_awlen[i],
          s_axi_awaddr[i]
        }),
        .o_ready(s_axi_awready[i]),
        .i_ready(sb_s_awready[i]),
        .o_data({
          sb_s_awburst[i],
          sb_s_awsize[i],
          sb_s_awid[i],
          sb_s_awlen[i],
          sb_s_awaddr[i]
        }),
        .o_valid(sb_s_awvalid[i])
    );

    // w
    svc_skidbuf #(
        .DATA_WIDTH(SKIDBUF_W_WIDTH)
    ) svc_skidbuf_w_i (
        .clk    (clk),
        .rst_n  (rst_n),
        .i_valid(s_axi_wvalid[i]),
        .i_data ({s_axi_wdata[i], s_axi_wstrb[i], s_axi_wlast[i]}),
        .o_ready(s_axi_wready[i]),
        .i_ready(sb_s_wready[i]),
        .o_data ({sb_s_wdata[i], sb_s_wstrb[i], sb_s_wlast[i]}),
        .o_valid(sb_s_wvalid[i])
    );
  end

  svc_sticky_bit svc_sticky_bit_aw_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clear(grant_done),
      .in   (m_axi_awvalid && m_axi_awready),
      .out  (aw_done)
  );

  svc_sticky_bit svc_sticky_bit_w_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clear(grant_done),
      .in   (m_axi_wvalid && m_axi_wready && m_axi_wlast),
      .out  (w_done)
  );

  // arbiter
  //
  // Write grants happen on awvalid and are held through wlast. In theory this
  // prevents a downstream from pipelining the setup of the next downstream
  // request if W processing happens a clock after AW, but that's not the case
  // for any svc modules. Revist this if that changes. Keep the arbitration
  // design simple for now.
  //
  // If we have the grant, we don't want to request it again. grant_done goes
  // high when m_aw has been accepted, and when m_w is final. If m_aw is the
  // one that is triggering this, the sb's version of valid will go low the
  // next cycle.
  always_comb begin
    request_mask = grant_valid ? ~(1 << grant_idx) : '1;
    grant_done   = aw_done && w_done;
  end

  svc_arbiter #(
      .NUM_M(NUM_M)
  ) svc_arbiter_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .request    (sb_s_awvalid & request_mask),
      .done       (grant_done),
      .grant_valid(grant_valid),
      .grant_idx  (grant_idx)
  );

  // break combo loop for m_axi_awvalid
  logic aw_done_reg;
  always_ff @(posedge clk) begin
    aw_done_reg <= aw_done;
  end

  //
  // Muxing
  //
  // AW out to subordinate mux
  assign m_axi_awvalid = grant_valid && !aw_done_reg;
  assign m_axi_awid    = grant_valid ? {grant_idx, sb_s_awid[grant_idx]} : 0;
  assign m_axi_awaddr  = grant_valid ? sb_s_awaddr[grant_idx] : 0;
  assign m_axi_awlen   = grant_valid ? sb_s_awlen[grant_idx] : 0;
  assign m_axi_awsize  = grant_valid ? sb_s_awsize[grant_idx] : 0;
  assign m_axi_awburst = grant_valid ? sb_s_awburst[grant_idx] : 0;

  // AW in from subordinate mux
  always_comb begin
    sb_s_awready = '0;
    if (grant_valid) begin
      sb_s_awready[grant_idx] = grant_done;
    end
  end

  // W out mux to subordinate mux
  assign m_axi_wvalid = grant_valid ? sb_s_wvalid[grant_idx] : 0;
  assign m_axi_wdata  = grant_valid ? sb_s_wdata[grant_idx] : 0;
  assign m_axi_wstrb  = grant_valid ? sb_s_wstrb[grant_idx] : 0;
  assign m_axi_wlast  = grant_valid ? sb_s_wlast[grant_idx] : 0;

  // W in from subordinate mux
  always_comb begin
    sb_s_wready = '0;
    if (grant_valid) begin
      sb_s_wready[grant_idx] = m_axi_wready;
    end
  end

  //-------------------------------------------------------------------------
  //
  // B/write response processing
  //
  //-------------------------------------------------------------------------
  //
  assign {b_grant_idx, sb_s_bid} = m_axi_bid;
  assign m_axi_bready = m_axi_bvalid ? sb_s_bready[b_grant_idx] : 1'b0;

  //
  // b channel skid buffers
  //
  // Note: these also are doing the muxed responses
  //
  for (genvar i = 0; i < NUM_M; i++) begin : gen_b_sb
    svc_skidbuf #(
        .DATA_WIDTH(SKIDBUF_B_WIDTH),
        .OPT_OUTREG(1)
    ) svc_skidbuf_b_i (
        .clk  (clk),
        .rst_n(rst_n),

        .i_valid(b_grant_idx == i && m_axi_bvalid),
        .i_data ({sb_s_bid, m_axi_bresp}),
        .o_ready(sb_s_bready[i]),

        .i_ready(s_axi_bvalid[i] && s_axi_bready[i]),
        .o_data ({s_axi_bid[i], s_axi_bresp[i]}),
        .o_valid(s_axi_bvalid[i])
    );
  end

endmodule
`endif
