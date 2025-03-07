`ifndef SVC_AXI_STRIPE_RD_SV
`define SVC_AXI_STRIPE_RD_SV

`include "svc.sv"
`include "svc_axi_stripe_ax.sv"
`include "svc_skidbuf.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

// Stripe read requests from 1 manager to N subordinates based on the low
// order bits in the address. There are some requirements for usage:
//
//  * NUM_S must be a power of 2.
//  * s_axi_arsize must be for the full data width.
//
// See design comments and TODOs in stripe_wr.

module svc_axi_stripe_rd #(
    parameter NUM_S            = 2,
    parameter AXI_ADDR_WIDTH   = 8,
    parameter AXI_DATA_WIDTH   = 16,
    parameter AXI_ID_WIDTH     = 4,
    parameter S_AXI_ADDR_WIDTH = AXI_ADDR_WIDTH - $clog2(NUM_S)
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
    // Manager interface to our subordinates
    //
    output logic [NUM_S-1:0]                       m_axi_arvalid,
    output logic [NUM_S-1:0][    AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [NUM_S-1:0][S_AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [NUM_S-1:0][                 7:0] m_axi_arlen,
    output logic [NUM_S-1:0][                 2:0] m_axi_arsize,
    output logic [NUM_S-1:0][                 1:0] m_axi_arburst,
    input  logic [NUM_S-1:0]                       m_axi_arready,
    input  logic [NUM_S-1:0]                       m_axi_rvalid,
    input  logic [NUM_S-1:0][    AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [NUM_S-1:0][  AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [NUM_S-1:0][                 1:0] m_axi_rresp,
    input  logic [NUM_S-1:0]                       m_axi_rlast,
    output logic [NUM_S-1:0]                       m_axi_rready
);
  localparam AW = AXI_ADDR_WIDTH;
  localparam DW = AXI_DATA_WIDTH;
  localparam IW = AXI_ID_WIDTH;
  localparam STRBW = DW / 8;
  localparam SAW = S_AXI_ADDR_WIDTH;

  localparam S_WIDTH = $clog2(NUM_S);
  localparam O_WIDTH = $clog2(STRBW);

  logic                        sb_s_arvalid;
  logic [     AW-1:0]          sb_s_araddr;
  logic [     IW-1:0]          sb_s_arid;
  logic [        7:0]          sb_s_arlen;
  logic [        2:0]          sb_s_arsize;
  logic [        1:0]          sb_s_arburst;
  logic                        sb_s_arready;

  logic [  NUM_S-1:0]          ar_stripe_valid;
  logic [  NUM_S-1:0][SAW-1:0] ar_stripe_addr;
  logic [  NUM_S-1:0][    7:0] ar_stripe_len;
  logic [S_WIDTH-1:0]          ar_stripe_start_idx;
  logic [S_WIDTH-1:0]          ar_stripe_end_idx;

  logic [  NUM_S-1:0]          m_axi_arvalid_next;
  logic [  NUM_S-1:0][ IW-1:0] m_axi_arid_next;
  logic [  NUM_S-1:0][SAW-1:0] m_axi_araddr_next;
  logic [  NUM_S-1:0][    7:0] m_axi_arlen_next;
  logic [  NUM_S-1:0][    2:0] m_axi_arsize_next;
  logic [  NUM_S-1:0][    1:0] m_axi_arburst_next;

  logic                        sb_s_rvalid;
  logic [     IW-1:0]          sb_s_rid;
  logic [     DW-1:0]          sb_s_rdata;
  logic [        1:0]          sb_s_rresp;
  logic                        sb_s_rlast;
  logic                        sb_s_rready;

  logic [  NUM_S-1:0]          sb_m_rvalid;
  logic [  NUM_S-1:0][ IW-1:0] sb_m_rid;
  logic [  NUM_S-1:0][ DW-1:0] sb_m_rdata;
  logic [  NUM_S-1:0][    1:0] sb_m_rresp;
  logic [  NUM_S-1:0]          sb_m_rlast;
  logic [  NUM_S-1:0]          sb_m_rready;

  // TODO: clean up these, and the ar version, signal names
  logic [S_WIDTH-1:0]          r_idx_start;
  logic [S_WIDTH-1:0]          r_idx_end;

  logic [S_WIDTH-1:0]          r_idx_offset;
  logic [S_WIDTH-1:0]          r_idx_offset_next;

  logic [S_WIDTH-1:0]          r_idx;

  logic                        fifo_r_w_full;
  logic                        fifo_r_r_empty;

  logic                        r_idx_valid;

  //-------------------------------------------------------------------------
  //
  // AR channel
  //
  //-------------------------------------------------------------------------
  svc_skidbuf #(
      .DATA_WIDTH(AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2)
  ) svc_skidbuf_ar_i (
      .clk(clk),
      .rst_n(rst_n),
      .i_valid(s_axi_arvalid),
      .i_data({
        s_axi_arid, s_axi_araddr, s_axi_arlen, s_axi_arsize, s_axi_arburst
      }),
      .o_ready(s_axi_arready),
      .i_ready(sb_s_arready),
      .o_data({sb_s_arid, sb_s_araddr, sb_s_arlen, sb_s_arsize, sb_s_arburst}),
      .o_valid(sb_s_arvalid)
  );

  assign sb_s_arready = (!fifo_r_w_full && &(~m_axi_arvalid | m_axi_arready));

  svc_axi_stripe_ax #(
      .NUM_S         (NUM_S),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_axi_stripe_addr_i (
      .s_addr         (sb_s_araddr),
      .s_len          (sb_s_arlen),
      .start_idx      (ar_stripe_start_idx),
      .end_idx        (ar_stripe_end_idx),
      .alignment_error(),
      .m_valid        (ar_stripe_valid),
      .m_addr         (ar_stripe_addr),
      .m_len          (ar_stripe_len)
  );

  always_comb begin
    m_axi_arvalid_next = m_axi_arvalid & ~m_axi_arready;
    m_axi_arid_next    = m_axi_arid;
    m_axi_araddr_next  = m_axi_araddr;
    m_axi_arlen_next   = m_axi_arlen;
    m_axi_arsize_next  = m_axi_arsize;
    m_axi_arburst_next = m_axi_arburst;

    if (sb_s_arvalid && sb_s_arready) begin
      m_axi_arvalid_next = ar_stripe_valid;
      m_axi_araddr_next  = ar_stripe_addr;
      m_axi_arlen_next   = ar_stripe_len;

      m_axi_arsize_next  = {NUM_S{sb_s_arsize}};
      m_axi_arburst_next = {NUM_S{sb_s_arburst}};
      m_axi_arid_next    = {NUM_S{sb_s_arid}};
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_axi_arvalid <= '0;
    end else begin
      m_axi_arvalid <= m_axi_arvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    m_axi_arid    <= m_axi_arid_next;
    m_axi_araddr  <= m_axi_araddr_next;
    m_axi_arlen   <= m_axi_arlen_next;
    m_axi_arsize  <= m_axi_arsize_next;
    m_axi_arburst <= m_axi_arburst_next;
  end

  //-------------------------------------------------------------------------
  //
  // R channel
  //
  //-------------------------------------------------------------------------

  // start/end idx at the time of ar submission
  //
  // If this is being used with large bursts, the addr width can be small, but
  // if used with small bursts, then this needs to be large enough to cover
  // the outstanding/pipelined ios.
  //
  // TODO: make addr_width configurable. See note above.
  svc_sync_fifo #(
      .DATA_WIDTH(S_WIDTH * 2),
      .ADDR_WIDTH(3)
  ) svc_sync_fifo_r_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (sb_s_arvalid && sb_s_arready),
      .w_data     ({ar_stripe_start_idx, ar_stripe_end_idx}),
      .w_full     (fifo_r_w_full),
      .w_half_full(),
      .r_inc      (sb_s_rvalid && sb_s_rready && sb_s_rlast),
      .r_data     ({r_idx_start, r_idx_end}),
      .r_empty    (fifo_r_r_empty)
  );

  // s side skid buf
  svc_skidbuf #(
      .DATA_WIDTH(IW + DW + 2 + 1),
      .OPT_OUTREG(1)
  ) svc_skidbuf_s_r_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(sb_s_rvalid),
      .i_data ({sb_s_rid, sb_s_rdata, sb_s_rresp, sb_s_rlast}),
      .o_ready(sb_s_rready),
      .i_ready(s_axi_rready),
      .o_data ({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast}),
      .o_valid(s_axi_rvalid)
  );

  // m side skidbufs
  for (genvar i = 0; i < NUM_S; i++) begin : gen_r_sb
    svc_skidbuf #(
        .DATA_WIDTH(IW + DW + 2 + 1)
    ) svc_skidbuf_m_r_i (
        .clk  (clk),
        .rst_n(rst_n),

        .i_valid(m_axi_rvalid[i]),
        .i_data({m_axi_rid[i], m_axi_rdata[i], m_axi_rresp[i], m_axi_rlast[i]}),
        .o_ready(m_axi_rready[i]),

        .i_ready(sb_m_rready[i]),
        .o_data ({sb_m_rid[i], sb_m_rdata[i], sb_m_rresp[i], sb_m_rlast[i]}),
        .o_valid(sb_m_rvalid[i])
    );
  end

  assign r_idx_valid = !fifo_r_r_empty;
  assign r_idx       = r_idx_valid ? r_idx_start + r_idx_offset : 0;

  // mux r channel from subs
  always_comb begin
    sb_s_rvalid = 1'b0;
    sb_s_rid    = 0;
    sb_s_rdata  = 0;
    sb_s_rresp  = 2'b0;
    sb_s_rlast  = 1'b0;

    if (r_idx_valid) begin
      sb_s_rvalid = sb_m_rvalid[r_idx];
      sb_s_rid    = sb_m_rid[r_idx];
      sb_s_rdata  = sb_m_rdata[r_idx];
      sb_s_rresp  = sb_m_rresp[r_idx];
      sb_s_rlast  = sb_m_rlast[r_idx] && r_idx == r_idx_end;
    end
  end

  // mux to subs
  always_comb begin
    sb_m_rready = '0;

    if (r_idx_valid) begin
      sb_m_rready[r_idx] = sb_s_rready;
    end
  end

  // index management
  always_comb begin
    r_idx_offset_next = r_idx_offset;

    if (sb_s_rvalid && sb_s_rready) begin
      if (sb_s_rlast) begin
        r_idx_offset_next = 0;
      end else begin
        r_idx_offset_next = r_idx_offset + 1;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      r_idx_offset <= 0;
    end else begin
      r_idx_offset <= r_idx_offset_next;
    end
  end

  `SVC_UNUSED({s_axi_araddr[S_WIDTH+O_WIDTH-1:O_WIDTH], fifo_r_r_empty});

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
      if (s_axi_arvalid) begin
        // Size must match full data width
        assert (int'(s_axi_arsize) == $clog2(AXI_DATA_WIDTH / 8));
      end

      if (|m_axi_rvalid) begin
        assert (!fifo_r_r_empty);
      end
    end
  end
`endif

endmodule
`endif
