`ifndef SVC_AXI_STRIPE_WR_SV
`define SVC_AXI_STRIPE_WR_SV

`include "svc.sv"
`include "svc_axi_stripe_ax.sv"
`include "svc_skidbuf.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

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

  logic                                 sb_s_awvalid;
  logic [AXI_ADDR_WIDTH-1:0]            sb_s_awaddr;
  logic [  AXI_ID_WIDTH-1:0]            sb_s_awid;
  logic [               7:0]            sb_s_awlen;
  logic [               2:0]            sb_s_awsize;
  logic [               1:0]            sb_s_awburst;
  logic                                 sb_s_awready;

  logic [         NUM_S-1:0]            aw_stripe_valid;
  logic [         NUM_S-1:0][  SAW-1:0] aw_stripe_addr;
  logic [         NUM_S-1:0][      7:0] aw_stripe_len;
  logic [       S_WIDTH-1:0]            aw_stripe_start_idx;
  logic [       S_WIDTH-1:0]            aw_stripe_end_idx;

  logic                                 sb_s_wvalid;
  logic [            DW-1:0]            sb_s_wdata;
  logic [         STRBW-1:0]            sb_s_wstrb;
  logic                                 sb_s_wready;

  logic [       S_WIDTH-1:0]            w_idx_start;
  logic [               7:0]            w_awlen;

  logic [       S_WIDTH-1:0]            w_idx;
  logic [       S_WIDTH-1:0]            w_idx_next;

  logic [               7:0]            w_remaining;
  logic [               7:0]            w_remaining_next;

  logic                                 w_active;
  logic                                 w_active_next;

  logic [         NUM_S-1:0]            m_axi_awvalid_next;
  logic [         NUM_S-1:0][   IW-1:0] m_axi_awid_next;
  logic [         NUM_S-1:0][  SAW-1:0] m_axi_awaddr_next;
  logic [         NUM_S-1:0][      7:0] m_axi_awlen_next;
  logic [         NUM_S-1:0][      2:0] m_axi_awsize_next;
  logic [         NUM_S-1:0][      1:0] m_axi_awburst_next;

  logic [         NUM_S-1:0]            m_axi_wvalid_next;
  logic [         NUM_S-1:0][   DW-1:0] m_axi_wdata_next;
  logic [         NUM_S-1:0][STRBW-1:0] m_axi_wstrb_next;
  logic [         NUM_S-1:0]            m_axi_wlast_next;

  logic [         NUM_S-1:0]            b_stripe_valid;

  logic                                 fifo_w_w_full;
  logic                                 fifo_w_r_empty;

  logic                                 fifo_b_w_full;
  logic                                 fifo_b_r_empty;

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

  assign sb_s_awready = (!fifo_w_w_full && !fifo_b_w_full &&
                         &(~m_axi_awvalid | m_axi_awready));

  svc_axi_stripe_ax #(
      .NUM_S         (NUM_S),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_axi_stripe_addr_i (
      .s_addr         (sb_s_awaddr),
      .s_len          (sb_s_awlen),
      .start_idx      (aw_stripe_start_idx),
      .end_idx        (aw_stripe_end_idx),
      .alignment_error(),
      .m_valid        (aw_stripe_valid),
      .m_addr         (aw_stripe_addr),
      .m_len          (aw_stripe_len)
  );

  always_comb begin
    m_axi_awvalid_next = m_axi_awvalid & ~m_axi_awready;
    m_axi_awid_next    = m_axi_awid;
    m_axi_awaddr_next  = m_axi_awaddr;
    m_axi_awlen_next   = m_axi_awlen;
    m_axi_awsize_next  = m_axi_awsize;
    m_axi_awburst_next = m_axi_awburst;

    if (sb_s_awvalid && sb_s_awready) begin
      m_axi_awvalid_next = aw_stripe_valid;
      m_axi_awaddr_next  = aw_stripe_addr;
      m_axi_awlen_next   = aw_stripe_len;

      m_axi_awsize_next  = {NUM_S{sb_s_awsize}};
      m_axi_awburst_next = {NUM_S{sb_s_awburst}};
      m_axi_awid_next    = {NUM_S{sb_s_awid}};
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_axi_awvalid <= '0;
    end else begin
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

  logic fifo_w_r_inc;

  svc_sync_fifo #(
      .DATA_WIDTH(S_WIDTH + 8)
  ) svc_sync_fifo_w_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .clr        (1'b0),
      .w_inc      (sb_s_awvalid && sb_s_awready),
      .w_data     ({aw_stripe_start_idx, sb_s_awlen}),
      .w_full     (fifo_w_w_full),
      .w_half_full(),
      .r_inc      (fifo_w_r_inc),
      .r_data     ({w_idx_start, w_awlen}),
      .r_empty    (fifo_w_r_empty)
  );

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
    w_active_next     = w_active;

    fifo_w_r_inc      = 1'b0;

    if (!w_active) begin
      if (!fifo_w_r_empty) begin
        fifo_w_r_inc     = 1'b1;
        w_active_next    = 1'b1;
        w_remaining_next = w_awlen;
        w_idx_next       = w_idx_start;

        if (sb_s_wvalid) begin
          if (!m_axi_wvalid[w_idx_start] || m_axi_wready[w_idx_start]) begin
            sb_s_wready                    = 1'b1;

            m_axi_wvalid_next[w_idx_start] = 1'b1;
            m_axi_wdata_next[w_idx_start]  = sb_s_wdata;
            m_axi_wstrb_next[w_idx_start]  = sb_s_wstrb;
            m_axi_wlast_next[w_idx_start]  = w_remaining_next < NUM_S ? '1 : '0;

            w_idx_next                     = w_idx_start + 1;
            if (w_awlen == 0) begin
              w_active_next = 1'b0;
            end else begin
              w_remaining_next = w_awlen - 1;
            end
          end
        end
      end
    end else begin
      if (sb_s_wvalid) begin
        if (!m_axi_wvalid[w_idx] || m_axi_wready[w_idx]) begin
          sb_s_wready              = 1'b1;

          m_axi_wvalid_next[w_idx] = 1'b1;
          m_axi_wdata_next[w_idx]  = sb_s_wdata;
          m_axi_wstrb_next[w_idx]  = sb_s_wstrb;
          m_axi_wlast_next[w_idx]  = w_remaining_next < NUM_S ? '1 : '0;

          w_idx_next               = w_idx + 1;

          if (w_remaining != 0) begin
            w_remaining_next = w_remaining - 1;
          end else begin
            w_active_next = 1'b0;
          end
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      w_idx        <= 0;
      w_active     <= 1'b0;
      m_axi_wvalid <= '0;
    end else begin
      w_idx        <= w_idx_next;
      w_active     <= w_active_next;
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

  logic                       sb_s_bvalid;
  logic [     IW-1:0]         sb_s_bid;
  logic [        1:0]         sb_s_bresp;
  logic                       sb_s_bready;

  logic [  NUM_S-1:0]         sb_m_bvalid;
  logic [  NUM_S-1:0][IW-1:0] sb_m_bid;
  logic [  NUM_S-1:0][   1:0] sb_m_bresp;
  logic [  NUM_S-1:0]         sb_m_bready;

  logic [S_WIDTH-1:0]         b_idx_end;
  logic                       b_idx_valid;

  // keep track of final idx and active subs at the time of aw submission
  svc_sync_fifo #(
      .DATA_WIDTH(S_WIDTH + NUM_S),
      .ADDR_WIDTH(4)
  ) svc_sync_fifo_b_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .clr        (1'b0),
      .w_inc      (sb_s_awvalid && sb_s_awready),
      .w_data     ({aw_stripe_end_idx, aw_stripe_valid}),
      .w_full     (fifo_b_w_full),
      .w_half_full(),
      .r_inc      (sb_s_bvalid && sb_s_bready),
      .r_data     ({b_idx_end, b_stripe_valid}),
      .r_empty    (fifo_b_r_empty)
  );

  // s side skid buf
  svc_skidbuf #(
      .DATA_WIDTH(IW + 2),
      .OPT_OUTREG(1)
  ) svc_skidbuf_s_b_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(sb_s_bvalid),
      .i_data ({sb_s_bid, sb_s_bresp}),
      .o_ready(sb_s_bready),
      .i_ready(s_axi_bready),
      .o_data ({s_axi_bid, s_axi_bresp}),
      .o_valid(s_axi_bvalid)
  );

  // m side skidbufs
  for (genvar i = 0; i < NUM_S; i++) begin : gen_b_sb
    svc_skidbuf #(
        .DATA_WIDTH(IW + 2)
    ) svc_skidbuf_m_b_i (
        .clk  (clk),
        .rst_n(rst_n),

        .i_valid(m_axi_bvalid[i]),
        .i_data ({m_axi_bid[i], m_axi_bresp[i]}),
        .o_ready(m_axi_bready[i]),

        .i_ready(sb_m_bready[i]),
        .o_data ({sb_m_bid[i], sb_m_bresp[i]}),
        .o_valid(sb_m_bvalid[i])
    );
  end

  assign b_idx_valid = !fifo_b_r_empty;

  // mux b channel from subs - we use the end_idx for response
  always_comb begin
    sb_s_bvalid = 1'b0;
    sb_s_bid    = 0;
    sb_s_bresp  = 2'b0;

    if (b_idx_valid) begin
      sb_s_bvalid = sb_m_bvalid[b_idx_end];
      sb_s_bid    = sb_m_bid[b_idx_end];
      sb_s_bresp  = sb_m_bresp[b_idx_end];
    end
  end

  // mux to subs - ready signals to all active subordinates
  always_comb begin
    sb_m_bready = '0;

    if (b_idx_valid) begin
      // Only set ready for the subordinates that are part of this transaction
      sb_m_bready = b_stripe_valid & {NUM_S{sb_s_bready}};
    end
  end

  `SVC_UNUSED({sb_s_awaddr[S_WIDTH+O_WIDTH-1:O_WIDTH], s_axi_wlast});

`ifdef FORMAL
`ifndef FORMAL_NO_SUBMODULES
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

      if (|m_axi_bvalid) begin
        assert (!fifo_b_r_empty);
      end
    end
  end
`endif
`endif

endmodule
`endif
