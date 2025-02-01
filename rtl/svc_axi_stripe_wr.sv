`ifndef SVC_AXI_STRIPE_WR_SV
`define SVC_AXI_STRIPE_WR_SV

`include "svc.sv"
`include "svc_axi_stripe_addr.sv"
`include "svc_skidbuf.sv"
`include "svc_unused.sv"

//
// Stripe write requests from 1 manager to N subordinates based on the low
// order bits in the address. There are some requirements for usage:
//
//  * NUM_S must be a power of 2.
//  * s_axi_awsize must be for the full data width.
//
// These requirements could be lifted, but would introduce more complexity
// into this module, and would likely come with a performance cost on the
// boundaries. It's better if the caller just does the right thing.
//
// TODO: check assumptions and return a bresp error if they don't hold, for
// now, rely on the asserts during formal verification to catch misuse.
//
// TODO: see the note on the b channel about a final cycle of latency that
// can likely be removed.
//
// TODO: awsize, and maybe others, are fixed value, but we are passing them
// around. Just set them at the destination directly.
//
module svc_axi_stripe_wr #(
    parameter NUM_S            = 2,
    parameter AXI_ADDR_WIDTH   = 8,
    parameter AXI_DATA_WIDTH   = 16,
    parameter AXI_STRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH     = 4,
    parameter S_AXI_ADDR_WIDTH = AXI_ADDR_WIDTH - $clog2(NUM_S)
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
    // Manager interface to our subordinates
    //
    output logic [NUM_S-1:0]                       m_axi_awvalid,
    output logic [NUM_S-1:0][S_AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [NUM_S-1:0][    AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [NUM_S-1:0][                 7:0] m_axi_awlen,
    output logic [NUM_S-1:0][                 2:0] m_axi_awsize,
    output logic [NUM_S-1:0][                 1:0] m_axi_awburst,
    input  logic [NUM_S-1:0]                       m_axi_awready,
    output logic [NUM_S-1:0]                       m_axi_wvalid,
    output logic [NUM_S-1:0][  AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [NUM_S-1:0][  AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    output logic [NUM_S-1:0]                       m_axi_wlast,
    input  logic [NUM_S-1:0]                       m_axi_wready,
    input  logic [NUM_S-1:0]                       m_axi_bvalid,
    input  logic [NUM_S-1:0][    AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [NUM_S-1:0][                 1:0] m_axi_bresp,
    output logic [NUM_S-1:0]                       m_axi_bready
);
  localparam DW = AXI_DATA_WIDTH;
  localparam IW = AXI_ID_WIDTH;
  localparam STRBW = AXI_STRB_WIDTH;
  localparam SAW = S_AXI_ADDR_WIDTH;

  localparam S_WIDTH = $clog2(NUM_S);
  localparam O_WIDTH = $clog2(AXI_STRB_WIDTH);

  logic                          s_axi_awready_next;
  logic                          s_axi_bvalid_next;
  logic [     IW-1:0]            s_axi_bid_next;
  logic [        1:0]            s_axi_bresp_next;

  logic [    SAW-1:0]            aw_stripe_addr;
  logic [S_WIDTH-1:0]            aw_stripe_idx;

  logic                          sb_s_wvalid;
  logic [     DW-1:0]            sb_s_wdata;
  logic [  STRBW-1:0]            sb_s_wstrb;
  logic                          sb_s_wready;

  logic [S_WIDTH-1:0]            w_idx;
  logic [S_WIDTH-1:0]            w_idx_next;

  logic [        7:0]            w_remaining;
  logic [        7:0]            w_remaining_next;

  logic                          w_done;
  logic                          w_done_next;

  logic [  NUM_S-1:0]            m_axi_awvalid_next;
  logic [  NUM_S-1:0][   IW-1:0] m_axi_awid_next;
  logic [  NUM_S-1:0][  SAW-1:0] m_axi_awaddr_next;
  logic [  NUM_S-1:0][      7:0] m_axi_awlen_next;
  logic [  NUM_S-1:0][      2:0] m_axi_awsize_next;
  logic [  NUM_S-1:0][      1:0] m_axi_awburst_next;

  logic [  NUM_S-1:0]            m_axi_wvalid_next;
  logic [  NUM_S-1:0][   DW-1:0] m_axi_wdata_next;
  logic [  NUM_S-1:0][STRBW-1:0] m_axi_wstrb_next;
  logic [  NUM_S-1:0]            m_axi_wlast_next;

  logic [  NUM_S-1:0]            b_done;
  logic [  NUM_S-1:0]            b_done_next;

  //-------------------------------------------------------------------------
  //
  // AW channel
  //
  //-------------------------------------------------------------------------

  svc_axi_stripe_addr #(
      .NUM_S         (NUM_S),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_axi_stripe_addr_i (
      .s_axi_axaddr(s_axi_awaddr),
      .sub_idx     (aw_stripe_idx),
      .word_aligned(),
      .m_axi_axaddr(aw_stripe_addr)
  );

  always_comb begin
    m_axi_awvalid_next = m_axi_awvalid & ~m_axi_awready;
    m_axi_awid_next    = m_axi_awid;
    m_axi_awaddr_next  = m_axi_awaddr;
    m_axi_awlen_next   = m_axi_awlen;
    m_axi_awsize_next  = m_axi_awsize;
    m_axi_awburst_next = m_axi_awburst;

    // FIXME: this still doesn't handle partial stripe writes correctly in
    // that it sends aw valids to all the subs, even if they won't be
    // participating in the io.
    for (int i = 0; i < NUM_S; i++) begin : gen_init
      if (s_axi_awvalid && s_axi_awready) begin

        m_axi_awvalid_next[i] = 1'b1;
        m_axi_awid_next[i]    = s_axi_awid;
        m_axi_awaddr_next[i]  = aw_stripe_addr;
        m_axi_awsize_next[i]  = s_axi_awsize;
        m_axi_awburst_next[i] = s_axi_awburst;
        m_axi_awlen_next[i]   = s_axi_awlen >> S_WIDTH;
      end
    end
  end

  always_comb begin
    s_axi_awready_next = s_axi_awready;

    if (s_axi_awready && s_axi_awvalid) begin
      s_axi_awready_next = 1'b0;
    end

    // TODO: try to remove this
    if (s_axi_bvalid && s_axi_bready) begin
      s_axi_awready_next = 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_awready <= 1'b1;
      m_axi_awvalid <= '0;
    end else begin
      s_axi_awready <= s_axi_awready_next;
      m_axi_awvalid <= m_axi_awvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    m_axi_awid    <= m_axi_awid_next;
    m_axi_awaddr  <= m_axi_awaddr_next;
    m_axi_awlen   <= m_axi_awlen_next;
    m_axi_awsize  <= m_axi_awsize_next;
    m_axi_awburst <= m_axi_awburst_next;
  end

  //-------------------------------------------------------------------------
  //
  // W channel
  //
  //-------------------------------------------------------------------------
  svc_skidbuf #(
      .DATA_WIDTH(DW + 2)
  ) svc_skidbuf_w_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(s_axi_wvalid),
      .i_data ({s_axi_wdata, s_axi_wstrb}),
      .o_ready(s_axi_wready),
      .i_ready(sb_s_wready),
      .o_data ({sb_s_wdata, sb_s_wstrb}),
      .o_valid(sb_s_wvalid)
  );

  always_comb begin
    m_axi_wvalid_next = m_axi_wvalid & ~m_axi_wready;
    m_axi_wdata_next  = m_axi_wdata;
    m_axi_wstrb_next  = m_axi_wstrb;
    m_axi_wlast_next  = m_axi_wlast;

    sb_s_wready       = 1'b0;
    w_idx_next        = w_idx;
    w_remaining_next  = w_remaining;
    w_done_next       = w_done;

    // start of burst
    if (s_axi_awready && s_axi_awvalid) begin
      w_idx_next       = aw_stripe_idx;
      w_remaining_next = s_axi_awlen;
      w_done_next      = 1'b0;
    end

    // incoming write data
    if (sb_s_wvalid && !w_done) begin
      if (!m_axi_wvalid[w_idx] || m_axi_wready[w_idx]) begin
        sb_s_wready              = 1'b1;

        m_axi_wvalid_next[w_idx] = 1'b1;
        m_axi_wdata_next[w_idx]  = sb_s_wdata;
        m_axi_wstrb_next[w_idx]  = sb_s_wstrb;
        m_axi_wlast_next[w_idx]  = w_remaining_next < NUM_S ? '1 : '0;

        // since NUM_S is a power of 2, we don't have to check against
        // a max value, we can just wrap
        w_idx_next               = w_idx + 1;

        // This looks weird, as one would normally want to subtract off of the
        // prev value. However if we are in the first clock cycle of the burst,
        // we won't have a prev value. We will, however, just set
        // w_remaining_next above. On beats other than the first one in the
        // burst, we set w_remaining_next to the prev value at the top of the
        // comb block.
        if (w_remaining_next != 0) begin
          w_remaining_next = w_remaining_next - 1;
        end else begin
          w_done_next = 1'b1;
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      w_idx        <= 0;
      w_done       <= 1'b0;
      m_axi_wvalid <= '0;
    end else begin
      w_idx        <= w_idx_next;
      w_done       <= w_done_next;
      m_axi_wvalid <= m_axi_wvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    w_remaining <= w_remaining_next;

    m_axi_wdata <= m_axi_wdata_next;
    m_axi_wstrb <= m_axi_wstrb_next;
    m_axi_wlast <= m_axi_wlast_next;
  end

  //-------------------------------------------------------------------------
  //
  // B channel
  //
  //-------------------------------------------------------------------------

  // I considered using &m_axi_bvalid ? '1 : '0 to drive all the breadys at
  // the same time, somewhat simplifying this logic. However, doing so will
  // stall the b channel on the earlier subordinates, potentially preventing
  // interleaved usage with some other manager when used with an arbiter. This
  // implementation is slightly more complicated, but provides better
  // aggregate throughput.

  // We're always ready to accept responses since we buffer them for our
  // caller.
  assign m_axi_bready = '1;

  // track bvalid from the subordinates
  for (genvar i = 0; i < NUM_S; i++) begin : gen_b
    always @(*) begin
      b_done_next[i] = b_done[i];

      if (s_axi_bvalid && s_axi_bready) begin
        b_done_next[i] = 1'b0;
      end

      if (m_axi_bvalid[i] && m_axi_bready[i]) begin
        b_done_next[i] = 1'b1;
      end
    end
  end

  // b channel back to the caller
  //
  // TODO: s_axi_bvalid has a cycle of latency that could be optimized out.
  // When doing this remember that the signal needs to be registered with no
  // combinatorial logic on the final output, which is the tricky bit given
  // the logic up to this point. A counter might work, at the expense of
  // a bunch of extra gates. Or there might be some way to tie it directly to
  // the final stripe's bvalid given that we wrote in order. Get formal
  // verification running first and then revisit this.
  always @(*) begin
    s_axi_bvalid_next = s_axi_bvalid && !s_axi_bready;
    s_axi_bid_next    = s_axi_bid;
    s_axi_bresp_next  = s_axi_bresp;

    // We only need an id and resp from one of them, it might as well be the
    // first. Note: we can only do this because we don't accept new writes
    // until the b channel has been accepted too. Otherwise, we would need to
    // store pending b channel info in case the last one wasn't accepted.
    if (m_axi_bvalid[0] && m_axi_bready[0]) begin
      s_axi_bid_next   = m_axi_bid[0];
      s_axi_bresp_next = m_axi_bresp[0];
    end

    // Similar to the above, all requests should start with bvalid low since
    // we wait on it to be awready. Hence, we don't need the usual
    // if (!s_axi_bvalid || s_axi_bready) check here.
    s_axi_bvalid_next = &b_done_next;
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_axi_bvalid <= 1'b0;
      b_done       <= '0;
    end else begin
      s_axi_bvalid <= s_axi_bvalid_next;
      b_done       <= b_done_next;
    end
  end

  always_ff @(posedge clk) begin
    s_axi_bid   <= s_axi_bid_next;
    s_axi_bresp <= s_axi_bresp_next;
  end

  `SVC_UNUSED({s_axi_awaddr[S_WIDTH+O_WIDTH-1:O_WIDTH], s_axi_wlast,
               m_axi_bid[NUM_S-1:1], m_axi_bresp[NUM_S-1:1]});

`ifdef FORMAL
  // Formal testing happens in the combined module, but we do have asserts
  // regarding bad behavior of the callers.
  //
  // Note: if formal verification is added to this module in the future, these
  // should use the ASSUME/ASSERT macros to be assumes for this module, but
  // asserts when used as a submodule.
  always @(posedge clk) begin
    if (rst_n) begin
      assert (NUM_S % 2 == 0);

      // the following are assertions about the requirements for usage
      // documented at the top of the module
      if (s_axi_awvalid) begin
        // Size must match full data width
        assert (int'(s_axi_awsize) == $clog2(AXI_DATA_WIDTH / 8));
      end

      if (s_axi_awvalid && s_axi_awready) begin
        // See the comment in the b-channel section. Given the current
        // implementation, it would be a bug if bvalid is high here.
        assert (!s_axi_bvalid);
      end

      for (int i = 0; i < NUM_S; i++) begin
        if (m_axi_wvalid[i] && m_axi_wready[i]) begin
          assert (m_axi_wlast[i] == (w_remaining < NUM_S - 1));
        end
      end
    end
  end
`endif

endmodule
`endif
