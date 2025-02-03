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

  logic                        sb_s_rready;

  logic                        r_active;
  logic                        r_active_next;

  logic [S_WIDTH-1:0]          r_idx;
  logic [S_WIDTH-1:0]          r_idx_next;

  logic [S_WIDTH-1:0]          r_stripe_end_idx;

  logic                        fifo_r_w_full;
  logic                        fifo_r_r_empty;

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

  assign sb_s_arready = (!r_active && !fifo_r_w_full &&
                         &(~m_axi_arvalid | m_axi_arready));

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

  // keep track of final idx at the time of ar submission
  svc_sync_fifo #(
      .DATA_WIDTH(S_WIDTH)
  ) svc_sync_fifo_r_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (sb_s_arvalid && sb_s_arready),
      .w_data     (ar_stripe_end_idx),
      .w_full     (fifo_r_w_full),
      .w_half_full(),
      .r_inc      (s_axi_rvalid && s_axi_rready && s_axi_rlast),
      .r_data     (r_stripe_end_idx),
      .r_empty    (fifo_r_r_empty)
  );

  // skid buf, with muxing to the subs
  svc_skidbuf #(
      .DATA_WIDTH(IW + DW + 2 + 1),
      .OPT_OUTREG(1)
  ) svc_skidbuf_r_i (
      .clk(clk),
      .rst_n(rst_n),
      .i_valid(m_axi_rvalid[r_idx]),
      .i_data({
        m_axi_rid[r_idx],
        m_axi_rdata[r_idx],
        m_axi_rresp[r_idx],
        m_axi_rlast[r_idx] && r_idx == r_stripe_end_idx
      }),
      .o_ready(sb_s_rready),
      .i_ready(s_axi_rready),
      .o_data({s_axi_rid, s_axi_rdata, s_axi_rresp, s_axi_rlast}),
      .o_valid(s_axi_rvalid)
  );

  // mux s_axi_rready to the subs
  always_comb begin
    m_axi_rready        = '0;
    m_axi_rready[r_idx] = sb_s_rready;
  end

  // index management
  always_comb begin
    r_active_next = r_active;
    r_idx_next    = r_idx;

    if (s_axi_rvalid && s_axi_rready && s_axi_rlast) begin
      r_active_next = 1'b0;
    end

    if (sb_s_arvalid && sb_s_arready) begin
      r_active_next = 1'b1;
      r_idx_next    = ar_stripe_start_idx;
    end

    if (m_axi_rvalid[r_idx] && m_axi_rready[r_idx]) begin
      r_idx_next = r_idx + 1;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      r_active <= 1'b0;
      r_idx    <= 0;
    end else begin
      r_idx    <= r_idx_next;
      r_active <= r_active_next;
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
