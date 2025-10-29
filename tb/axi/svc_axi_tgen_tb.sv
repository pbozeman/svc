`include "svc_unit.sv"
`include "svc_axi_tgen.sv"

// This is a super simple smoke test to make sure there are no lint/synth
// issues. Each of the submodules has more testing.

// verilator lint_off: UNUSEDSIGNAL
module svc_axi_tgen_tb;
  localparam AXI_ADDR_WIDTH = 20;
  localparam AXI_DATA_WIDTH = 16;
  localparam AXI_ID_WIDTH = 4;
  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                      w_start;
  logic                      r_start;
  logic                      busy;

  logic [AXI_ADDR_WIDTH-1:0] w_base_addr;
  logic [  AXI_ID_WIDTH-1:0] w_burst_id;
  logic [               7:0] w_burst_beats;
  logic [AXI_ADDR_WIDTH-1:0] w_burst_stride;
  logic [               2:0] w_burst_awsize;
  logic [              15:0] w_burst_num;

  logic [AXI_ADDR_WIDTH-1:0] r_base_addr;
  logic [  AXI_ID_WIDTH-1:0] r_burst_id;
  logic [               7:0] r_burst_beats;
  logic [AXI_ADDR_WIDTH-1:0] r_burst_stride;
  logic [               2:0] r_burst_arsize;
  logic [              15:0] r_burst_num;

  logic                      m_axi_awvalid;
  logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr;
  logic [  AXI_ID_WIDTH-1:0] m_axi_awid;
  logic [               7:0] m_axi_awlen;
  logic [               2:0] m_axi_awsize;
  logic [               1:0] m_axi_awburst;
  logic                      m_axi_awready;

  logic                      m_axi_wvalid;
  logic [AXI_DATA_WIDTH-1:0] m_axi_wdata;
  logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb;
  logic                      m_axi_wlast;
  logic                      m_axi_wready;

  logic                      m_axi_bvalid;
  logic [  AXI_ID_WIDTH-1:0] m_axi_bid;
  logic [               1:0] m_axi_bresp;
  logic                      m_axi_bready;

  logic                      m_axi_arvalid;
  logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr;
  logic [  AXI_ID_WIDTH-1:0] m_axi_arid;
  logic [               7:0] m_axi_arlen;
  logic [               2:0] m_axi_arsize;
  logic [               1:0] m_axi_arburst;
  logic                      m_axi_arready;

  logic                      m_axi_rvalid;
  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata;
  logic                      m_axi_rlast;
  logic [  AXI_ID_WIDTH-1:0] m_axi_rid;
  logic [               1:0] m_axi_rresp;
  logic                      m_axi_rready;

  svc_axi_tgen #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .AXI_STRB_WIDTH(AXI_STRB_WIDTH)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .w_start(w_start),
      .r_start(r_start),
      .busy   (busy),

      .w_base_addr   (w_base_addr),
      .w_burst_id    (w_burst_id),
      .w_burst_beats (w_burst_beats),
      .w_burst_stride(w_burst_stride),
      .w_burst_awsize(w_burst_awsize),
      .w_burst_num   (w_burst_num),

      .r_base_addr   (r_base_addr),
      .r_burst_id    (r_burst_id),
      .r_burst_beats (r_burst_beats),
      .r_burst_stride(r_burst_stride),
      .r_burst_arsize(r_burst_arsize),
      .r_burst_num   (r_burst_num),

      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awlen  (m_axi_awlen),
      .m_axi_awsize (m_axi_awsize),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awready(m_axi_awready),

      .m_axi_wvalid(m_axi_wvalid),
      .m_axi_wdata (m_axi_wdata),
      .m_axi_wstrb (m_axi_wstrb),
      .m_axi_wlast (m_axi_wlast),
      .m_axi_wready(m_axi_wready),

      .m_axi_bvalid(m_axi_bvalid),
      .m_axi_bid   (m_axi_bid),
      .m_axi_bresp (m_axi_bresp),
      .m_axi_bready(m_axi_bready),

      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arid   (m_axi_arid),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arready(m_axi_arready),

      .m_axi_rvalid(m_axi_rvalid),
      .m_axi_rdata (m_axi_rdata),
      .m_axi_rlast (m_axi_rlast),
      .m_axi_rid   (m_axi_rid),
      .m_axi_rresp (m_axi_rresp),
      .m_axi_rready(m_axi_rready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      w_start        <= 1'b0;
      r_start        <= 1'b0;

      w_base_addr    <= '0;
      w_burst_id     <= '0;
      w_burst_beats  <= '0;
      w_burst_stride <= '0;
      w_burst_awsize <= '0;
      w_burst_num    <= '0;

      r_base_addr    <= '0;
      r_burst_id     <= '0;
      r_burst_beats  <= '0;
      r_burst_stride <= '0;
      r_burst_arsize <= '0;
      r_burst_num    <= '0;

      m_axi_awready  <= 1'b0;
      m_axi_wready   <= 1'b0;
      m_axi_bvalid   <= 1'b0;
      m_axi_bid      <= '0;
      m_axi_bresp    <= '0;

      m_axi_arready  <= 1'b0;
      m_axi_rvalid   <= 1'b0;
      m_axi_rdata    <= '0;
      m_axi_rlast    <= 1'b0;
      m_axi_rid      <= '0;
      m_axi_rresp    <= '0;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(m_axi_awvalid);
    `CHECK_FALSE(m_axi_wvalid);
    `CHECK_TRUE(m_axi_bready);
    `CHECK_FALSE(m_axi_arvalid);
    `CHECK_TRUE(m_axi_rready);
    `CHECK_FALSE(busy);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_tgen_tb);
  `TEST_CASE(test_reset);
  `TEST_SUITE_END();
endmodule
