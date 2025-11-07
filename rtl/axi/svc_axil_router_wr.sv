`ifndef SVC_AXIL_ROUTER_WR_SV
`define SVC_AXIL_ROUTER_WR_SV

`include "svc.sv"
`include "svc_skidbuf.sv"
`include "svc_unused.sv"

//
// Route AXIL manager write requests to 1 of N subordinates
//
// The $clog2(NUM_S) bits are used from the top of the addr space
// to route. They are zero'd when passed to the subordinate.
//
// This is not a high performance interface. It was designed to route
// requests to debugging registers. It does not allow requests
// to be issued in parallel to keep the logic footprint down, i.e.
// aw and w requests are not pipelined to different subordinates while waiting
// for a write response. It would involve a lot of extra logic to handle
// the potential out of order responses. And, if that is ever needed,
// I'd rather make the investment in a high-perf full xbar rather
// than this 1:N.
//
module svc_axil_router_wr #(
    parameter S_AXIL_ADDR_WIDTH = 32,
    parameter S_AXIL_DATA_WIDTH = 16,
    parameter M_AXIL_ADDR_WIDTH = 32,
    parameter M_AXIL_DATA_WIDTH = 16,
    parameter NUM_S             = 2
) (
    input logic clk,
    input logic rst_n,

    // subordinate interface for our manager
    input  logic                         s_axil_awvalid,
    input  logic [S_AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    output logic                         s_axil_awready,

    input  logic                           s_axil_wvalid,
    input  logic [  S_AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [S_AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb,
    output logic                           s_axil_wready,

    output logic       s_axil_bvalid,
    output logic [1:0] s_axil_bresp,
    input  logic       s_axil_bready,

    // manager interfaces to our subordinates
    output logic [NUM_S-1:0]                        m_axil_awvalid,
    output logic [NUM_S-1:0][M_AXIL_ADDR_WIDTH-1:0] m_axil_awaddr,
    input  logic [NUM_S-1:0]                        m_axil_awready,

    output logic [NUM_S-1:0]                          m_axil_wvalid,
    output logic [NUM_S-1:0][  M_AXIL_DATA_WIDTH-1:0] m_axil_wdata,
    output logic [NUM_S-1:0][M_AXIL_DATA_WIDTH/8-1:0] m_axil_wstrb,
    input  logic [NUM_S-1:0]                          m_axil_wready,

    input  logic [NUM_S-1:0]      m_axil_bvalid,
    input  logic [NUM_S-1:0][1:0] m_axil_bresp,
    output logic [NUM_S-1:0]      m_axil_bready
);
  localparam S_AW = S_AXIL_ADDR_WIDTH;
  localparam S_DW = S_AXIL_DATA_WIDTH;
  localparam M_AW = M_AXIL_ADDR_WIDTH;
  localparam M_DW = M_AXIL_DATA_WIDTH;
  localparam SEL_W = $clog2(NUM_S);
  localparam S_SW = S_DW / 8;
  localparam M_SW = M_DW / 8;

  // We only need to check for addr/bus erros when there are unused
  // portions of the addr space. Otherwise, verilator complains with:
  //   Warning-CMPCONST: ...Comparison is constant due to limited range:
  //         .... if (sb_s_awaddr_sel > SEL_W'(NUM_S - 1)) begin
  //
  localparam bit NEED_ADDR_RANGE_CHECK = (1 << SEL_W) > NUM_S;

  logic                               active;
  logic                               active_next;

  logic                               bus_err;
  logic                               bus_err_next;

  logic [        NUM_S-1:0]           m_axil_awvalid_next;
  logic [        NUM_S-1:0][M_AW-1:0] m_axil_awaddr_next;
  logic [        NUM_S-1:0]           m_axil_wvalid_next;
  logic [        NUM_S-1:0][M_DW-1:0] m_axil_wdata_next;
  logic [        NUM_S-1:0][M_SW-1:0] m_axil_wstrb_next;

  logic                               sb_s_awvalid;
  logic [S_AW-1:S_AW-SEL_W]           sb_s_awaddr_sel;
  logic [   S_AW-SEL_W-1:0]           sb_s_awaddr_sub;
  logic                               sb_s_awready;

  logic                               sb_s_wvalid;
  logic [         S_DW-1:0]           sb_s_wdata;
  logic [         S_SW-1:0]           sb_s_wstrb;
  logic                               sb_s_wready;

  logic                               sb_s_bvalid;
  logic [              1:0]           sb_s_bresp;
  logic                               sb_s_bready;

  logic [        NUM_S-1:0]           sb_m_bvalid;
  logic [        NUM_S-1:0][     1:0] sb_m_bresp;
  logic [        NUM_S-1:0]           sb_m_bready;

  logic [        SEL_W-1:0]           sel;
  logic [        SEL_W-1:0]           sel_next;

  svc_skidbuf #(
      .DATA_WIDTH(S_AW)
  ) svc_skidbuf_s_aw_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_awvalid),
      .i_data (s_axil_awaddr),
      .o_ready(s_axil_awready),

      .i_ready(sb_s_awready),
      .o_data ({sb_s_awaddr_sel, sb_s_awaddr_sub}),
      .o_valid(sb_s_awvalid)
  );

  svc_skidbuf #(
      .DATA_WIDTH(S_DW + S_SW)
  ) svc_skidbuf_s_w_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_wvalid),
      .i_data ({s_axil_wstrb, s_axil_wdata}),
      .o_ready(s_axil_wready),

      .i_ready(sb_s_wready),
      .o_data ({sb_s_wstrb, sb_s_wdata}),
      .o_valid(sb_s_wvalid)
  );

  svc_skidbuf #(
      .DATA_WIDTH(2),
      .OPT_OUTREG(1)
  ) svc_skidbuf_s_b_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(sb_s_bvalid),
      .i_data (sb_s_bresp),
      .o_ready(sb_s_bready),
      .i_ready(s_axil_bready),
      .o_data (s_axil_bresp),
      .o_valid(s_axil_bvalid)
  );

  for (genvar i = 0; i < NUM_S; i++) begin : gen_b_sb
    svc_skidbuf #(
        .DATA_WIDTH(2)
    ) svc_skidbuf_m_b_i (
        .clk  (clk),
        .rst_n(rst_n),

        .i_valid(m_axil_bvalid[i]),
        .i_data (m_axil_bresp[i]),
        .o_ready(m_axil_bready[i]),

        .i_ready(sb_m_bready[i]),
        .o_data (sb_m_bresp[i]),
        .o_valid(sb_m_bvalid[i])
    );
  end

  always_comb begin
    active_next         = active;
    bus_err_next        = bus_err;
    sel_next            = sel;

    m_axil_awvalid_next = m_axil_awvalid & ~m_axil_awready;
    m_axil_awaddr_next  = m_axil_awaddr;
    m_axil_wvalid_next  = m_axil_wvalid & ~m_axil_wready;
    m_axil_wdata_next   = m_axil_wdata;
    m_axil_wstrb_next   = m_axil_wstrb;

    sb_s_awready        = 1'b0;
    sb_s_wready         = 1'b0;

    // we stay active through the write response
    if (!active) begin
      // Wait for both address and data to be valid before proceeding
      if (sb_s_awvalid && sb_s_wvalid) begin
        active_next  = 1'b1;
        sel_next     = sb_s_awaddr_sel;
        sb_s_awready = 1'b1;
        sb_s_wready  = 1'b1;

        if (NEED_ADDR_RANGE_CHECK && sb_s_awaddr_sel > SEL_W'(NUM_S - 1)) begin
          bus_err_next = 1'b1;
        end else begin
          m_axil_awvalid_next[sel_next] = 1'b1;
          m_axil_awaddr_next[sel_next]  = M_AW'({SEL_W'(0), sb_s_awaddr_sub});
          m_axil_wvalid_next[sel_next]  = 1'b1;
          m_axil_wdata_next[sel_next]   = M_DW'(sb_s_wdata);
          m_axil_wstrb_next[sel_next]   = M_SW'(sb_s_wstrb);
        end
      end
    end else begin
      if (bus_err) begin
        if (sb_s_bvalid && sb_s_bready) begin
          active_next  = 1'b0;
          bus_err_next = 1'b0;
        end
      end else if (sb_m_bvalid[sel] && sb_m_bready[sel]) begin
        active_next = 1'b0;
      end
    end
  end

  // mux to subs
  always_comb begin
    sb_m_bready = '0;

    if (active && !bus_err) begin
      sb_m_bready[sel] = sb_s_bready;
    end
  end

  // demux b channel from subs
  always_comb begin
    case (1'b1)
      !active: begin
        sb_s_bvalid = 1'b0;
        sb_s_bresp  = 2'b0;
      end
      active && bus_err: begin
        sb_s_bvalid = 1'b1;
        sb_s_bresp  = 2'b11;
      end
      default: begin
        sb_s_bvalid = sb_m_bvalid[sel];
        sb_s_bresp  = sb_m_bresp[sel];
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      active         <= 1'b0;
      bus_err        <= 1'b0;
      m_axil_awvalid <= '0;
      m_axil_wvalid  <= '0;
    end else begin
      active         <= active_next;
      bus_err        <= bus_err_next;
      m_axil_awvalid <= m_axil_awvalid_next;
      m_axil_wvalid  <= m_axil_wvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    m_axil_awaddr <= m_axil_awaddr_next;
    m_axil_wdata  <= m_axil_wdata_next;
    m_axil_wstrb  <= m_axil_wstrb_next;
    sel           <= sel_next;
  end

  if (S_DW != M_DW) begin : gen_unused
    `SVC_UNUSED({sb_s_wdata[S_DW-1:M_DW], sb_s_wstrb[S_SW-1:M_SW]});
  end

`ifdef FORMAL
  // This doesn't have a formal of it's own, but gets tested up with the full
  // router.
  always @(posedge clk) begin
    if (rst_n) begin
      if (|m_axil_awvalid) begin
        assert (active);
      end

      if (|m_axil_wvalid) begin
        assert (active);
      end

      if (|sb_m_bvalid) begin
        assert (active);
      end
    end
  end
`endif

endmodule
`endif
