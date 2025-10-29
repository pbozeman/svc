`ifndef SVC_AXIL_ROUTER_RD_SV
`define SVC_AXIL_ROUTER_RD_SV

`include "svc.sv"
`include "svc_skidbuf.sv"

//
// Route AXIL manager requests to 1 of N subordinates
//
// The $clog2(NUM_S) bits are used from the top of the addr space
// to route. They are zero'd when passed to the subordinate.
//
// This is not a high performance interface. It was designed to route
// requests to debugging registers. It does not allow requests
// to be issued in parallel to keep the logic footprint down, i.e.
// ar requests are not pipelined to different subordinates while waiting
// for a read response. It would involved a lot of extra logic to handle
// the potential out of order responses. And, if that is ever needed,
// I'd rather make the investment in a high-perf full xbar rather
// than this 1:N.
//
module svc_axil_router_rd #(
    parameter S_AXIL_ADDR_WIDTH = 32,
    parameter S_AXIL_DATA_WIDTH = 16,
    parameter M_AXIL_ADDR_WIDTH = 32,
    parameter M_AXIL_DATA_WIDTH = 16,
    parameter NUM_S             = 2
) (
    input logic clk,
    input logic rst_n,

    // subordinate interface for our manager
    input  logic                         s_axil_arvalid,
    input  logic [S_AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                         s_axil_arready,

    output logic                         s_axil_rvalid,
    output logic [S_AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                  1:0] s_axil_rresp,
    input  logic                         s_axil_rready,

    // manager interfaces to our subordinates
    output logic [NUM_S-1:0]                        m_axil_arvalid,
    output logic [NUM_S-1:0][M_AXIL_ADDR_WIDTH-1:0] m_axil_araddr,
    input  logic [NUM_S-1:0]                        m_axil_arready,

    input  logic [NUM_S-1:0]                        m_axil_rvalid,
    input  logic [NUM_S-1:0][M_AXIL_DATA_WIDTH-1:0] m_axil_rdata,
    input  logic [NUM_S-1:0][                  1:0] m_axil_rresp,
    output logic [NUM_S-1:0]                        m_axil_rready
);
  localparam S_AW = S_AXIL_ADDR_WIDTH;
  localparam S_DW = S_AXIL_DATA_WIDTH;
  localparam M_AW = M_AXIL_ADDR_WIDTH;
  localparam M_DW = M_AXIL_DATA_WIDTH;
  localparam SEL_W = $clog2(NUM_S);

  // We only need to check for addr/bus erros when there are unused
  // portions of the addr space. Otherwise, verilator complains with:
  //   Warning-CMPCONST: ...Comparison is constant due to limited range:
  //         .... if (sb_s_araddr_sel > SEL_W'(NUM_S - 1)) begin
  //
  localparam bit NEED_ADDR_RANGE_CHECK = (1 << SEL_W) > NUM_S;

  logic                               active;
  logic                               active_next;

  logic                               bus_err;
  logic                               bus_err_next;

  logic [        NUM_S-1:0]           m_axil_arvalid_next;
  logic [        NUM_S-1:0][M_AW-1:0] m_axil_araddr_next;

  logic                               sb_s_arvalid;
  logic [S_AW-1:S_AW-SEL_W]           sb_s_araddr_sel;
  logic [   S_AW-SEL_W-1:0]           sb_s_araddr_sub;
  logic                               sb_s_arready;

  logic                               sb_s_rvalid;
  logic [         S_DW-1:0]           sb_s_rdata;
  logic [              1:0]           sb_s_rresp;
  logic                               sb_s_rready;

  logic [        NUM_S-1:0]           sb_m_rvalid;
  logic [        NUM_S-1:0][M_DW-1:0] sb_m_rdata;
  logic [        NUM_S-1:0][     1:0] sb_m_rresp;
  logic [        NUM_S-1:0]           sb_m_rready;

  logic [        SEL_W-1:0]           sel;
  logic [        SEL_W-1:0]           sel_next;

  svc_skidbuf #(
      .DATA_WIDTH(S_AW)
  ) svc_skidbuf_s_ar_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_arvalid),
      .i_data (s_axil_araddr),
      .o_ready(s_axil_arready),

      .i_ready(sb_s_arready),
      .o_data ({sb_s_araddr_sel, sb_s_araddr_sub}),
      .o_valid(sb_s_arvalid)
  );

  svc_skidbuf #(
      .DATA_WIDTH(S_DW + 2),
      .OPT_OUTREG(1)
  ) svc_skidbuf_s_r_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .i_valid(sb_s_rvalid),
      .i_data ({sb_s_rresp, sb_s_rdata}),
      .o_ready(sb_s_rready),
      .i_ready(s_axil_rready),
      .o_data ({s_axil_rresp, s_axil_rdata}),
      .o_valid(s_axil_rvalid)
  );

  for (genvar i = 0; i < NUM_S; i++) begin : gen_r_sb
    svc_skidbuf #(
        .DATA_WIDTH(M_DW + 2)
    ) svc_skidbuf_m_r_i (
        .clk  (clk),
        .rst_n(rst_n),

        .i_valid(m_axil_rvalid[i]),
        .i_data ({m_axil_rresp[i], m_axil_rdata[i]}),
        .o_ready(m_axil_rready[i]),

        .i_ready(sb_m_rready[i]),
        .o_data ({sb_m_rresp[i], sb_m_rdata[i]}),
        .o_valid(sb_m_rvalid[i])
    );
  end

  always_comb begin
    active_next         = active;
    bus_err_next        = bus_err;
    sel_next            = sel;

    m_axil_arvalid_next = m_axil_arvalid & ~m_axil_arready;
    m_axil_araddr_next  = m_axil_araddr;

    sb_s_arready        = 1'b0;

    // we stay active through the read response
    if (!active) begin
      sb_s_arready = 1'b1;

      if (sb_s_arvalid) begin
        active_next = 1'b1;
        sel_next    = sb_s_araddr_sel;

        if (NEED_ADDR_RANGE_CHECK && sb_s_araddr_sel > SEL_W'(NUM_S - 1)) begin
          bus_err_next = 1'b1;
        end else begin
          m_axil_arvalid_next[sel_next] = 1'b1;
          m_axil_araddr_next[sel_next]  = M_AW'({SEL_W'(0), sb_s_araddr_sub});
        end
      end
    end else begin
      if (bus_err) begin
        if (sb_s_rvalid && sb_s_rready) begin
          active_next  = 1'b0;
          bus_err_next = 1'b0;
        end
      end else if (sb_m_rvalid[sel] && sb_m_rready[sel]) begin
        active_next = 1'b0;
      end
    end
  end

  // mux to subs
  always_comb begin
    sb_m_rready = '0;

    if (active && !bus_err) begin
      sb_m_rready[sel] = sb_s_rready;
    end
  end

  // demux r channel from subs
  always_comb begin
    sb_s_rvalid = 1'b0;
    sb_s_rdata  = 0;
    sb_s_rresp  = 2'b0;

    if (active) begin
      if (bus_err) begin
        sb_s_rvalid = 1'b1;
        sb_s_rdata  = S_DW'(32'hADD1EBAD);
        sb_s_rresp  = 2'b11;
      end else begin
        sb_s_rvalid = sb_m_rvalid[sel];
        sb_s_rdata  = S_DW'(sb_m_rdata[sel]);
        sb_s_rresp  = sb_m_rresp[sel];
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      active         <= 1'b0;
      bus_err        <= 1'b0;
      m_axil_arvalid <= '0;
    end else begin
      active         <= active_next;
      bus_err        <= bus_err_next;
      m_axil_arvalid <= m_axil_arvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    m_axil_araddr <= m_axil_araddr_next;
    sel           <= sel_next;
  end

`ifdef FORMAL
  // This doesn't have a formal of it's own, but gets tested up with the full
  // router.
  always @(posedge clk) begin
    if (rst_n) begin
      if (|m_axil_arvalid) begin
        assert (active);
      end

      if (|sb_m_rvalid) begin
        assert (active);
      end
    end
  end
`endif

endmodule
`endif
