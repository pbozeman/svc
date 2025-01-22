`include "svc_unit.sv"

`include "svc_axi_arbiter_wr.sv"
`include "svc_unused.sv"

// This is just a quick smoke test. The real testing is via formal of the
// combined rw module.

module svc_axi_arbiter_wr_tb;
  parameter NUM_M = 3;
  parameter AW = 20;
  parameter DW = 16;
  parameter IDW = 4;
  parameter S_IDW = IDW + $clog2(NUM_M);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [NUM_M-1:0]           m_axi_awvalid;
  logic [NUM_M-1:0][ IDW-1:0] m_axi_awid;
  logic [NUM_M-1:0][  AW-1:0] m_axi_awaddr;
  logic [NUM_M-1:0][     7:0] m_axi_awlen;
  logic [NUM_M-1:0][     2:0] m_axi_awsize;
  logic [NUM_M-1:0][     1:0] m_axi_awburst;
  logic [NUM_M-1:0]           m_axi_awready;

  logic [NUM_M-1:0]           m_axi_wvalid;
  logic [NUM_M-1:0][  DW-1:0] m_axi_wdata;
  logic [NUM_M-1:0][DW/8-1:0] m_axi_wstrb;
  logic [NUM_M-1:0]           m_axi_wlast;
  logic [NUM_M-1:0]           m_axi_wready;

  logic [NUM_M-1:0]           m_axi_bvalid;
  logic [NUM_M-1:0][ IDW-1:0] m_axi_bid;
  logic [NUM_M-1:0][     1:0] m_axi_bresp;
  logic [NUM_M-1:0]           m_axi_bready;

  logic                       s_axi_awvalid;
  logic [S_IDW-1:0]           s_axi_awid;
  logic [   AW-1:0]           s_axi_awaddr;
  logic [      7:0]           s_axi_awlen;
  logic [      2:0]           s_axi_awsize;
  logic [      1:0]           s_axi_awburst;
  logic                       s_axi_awready;

  logic                       s_axi_wvalid;
  logic [   DW-1:0]           s_axi_wdata;
  logic [ DW/8-1:0]           s_axi_wstrb;
  logic                       s_axi_wlast;
  logic                       s_axi_wready;

  logic                       s_axi_bvalid;
  logic [S_IDW-1:0]           s_axi_bid;
  logic [      1:0]           s_axi_bresp;
  logic                       s_axi_bready;

  svc_axi_arbiter_wr #(
      .NUM_M         (NUM_M),
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_awready(m_axi_awready),

      .s_axi_wvalid(m_axi_wvalid),
      .s_axi_wdata (m_axi_wdata),
      .s_axi_wstrb (m_axi_wstrb),
      .s_axi_wlast (m_axi_wlast),
      .s_axi_wready(m_axi_wready),

      .s_axi_bvalid(m_axi_bvalid),
      .s_axi_bid   (m_axi_bid),
      .s_axi_bresp (m_axi_bresp),
      .s_axi_bready(m_axi_bready),

      .m_axi_awvalid(s_axi_awvalid),
      .m_axi_awid   (s_axi_awid),
      .m_axi_awaddr (s_axi_awaddr),
      .m_axi_awlen  (s_axi_awlen),
      .m_axi_awsize (s_axi_awsize),
      .m_axi_awburst(s_axi_awburst),
      .m_axi_awready(s_axi_awready),

      .m_axi_wvalid(s_axi_wvalid),
      .m_axi_wdata (s_axi_wdata),
      .m_axi_wstrb (s_axi_wstrb),
      .m_axi_wlast (s_axi_wlast),
      .m_axi_wready(s_axi_wready),

      .m_axi_bvalid(s_axi_bvalid),
      .m_axi_bid   (s_axi_bid),
      .m_axi_bresp (s_axi_bresp),
      .m_axi_bready(s_axi_bready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_awvalid <= '0;
      m_axi_awid    <= '0;
      m_axi_awaddr  <= '0;
      m_axi_awlen   <= '0;
      m_axi_awsize  <= '0;
      m_axi_awburst <= '0;

      m_axi_wvalid  <= '0;
      m_axi_wdata   <= '0;
      m_axi_wstrb   <= '0;
      m_axi_wlast   <= '0;

      m_axi_bready  <= '0;

      s_axi_awready <= 1'b0;
      s_axi_wready  <= 1'b0;
      s_axi_bvalid  <= 1'b0;
      s_axi_bid     <= '0;
      s_axi_bresp   <= 2'b00;
    end
  end

  always_ff @(posedge clk) begin
    for (int i = 0; i < NUM_M; i++) begin
      if (m_axi_awvalid[i] && m_axi_awready[i]) begin
        m_axi_awvalid[i] <= 1'b0;
      end
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axi_awvalid);
    `CHECK_FALSE(s_axi_wvalid);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  // Basic smoke test
  task automatic test_basic;
    logic [   AW-1:0] addr = AW'(16'hA000);
    logic [   DW-1:0] data = DW'(16'hD000);
    logic [S_IDW-1:0] awid;


    m_axi_awvalid    = '0;
    m_axi_wvalid     = '0;
    m_axi_bready     = '1;

    // Set up a burst from master 0
    // length 2, INCR, 2 byte stride
    m_axi_awvalid[0] = 1'b1;
    m_axi_awaddr[0]  = addr;
    m_axi_awid[0]    = 4'h1;
    m_axi_awlen[0]   = 8'h01;
    m_axi_awburst[0] = 2'b01;
    m_axi_awsize[0]  = 3'b001;

    s_axi_awready    = 1'b1;
    s_axi_wready     = 1'b1;

    // First clock - check arbitration and address phase
    `CHECK_TRUE(m_axi_awvalid[0] && m_axi_awready[0]);
    `CHECK_FALSE(s_axi_awvalid);
    `TICK(clk);
    `CHECK_FALSE(m_axi_awvalid[0]);

    `CHECK_TRUE(s_axi_awvalid);
    `CHECK_EQ(s_axi_awaddr, addr);
    `CHECK_EQ(s_axi_awlen, 8'h01);
    `CHECK_EQ(s_axi_awsize, 3'b001);
    `CHECK_EQ(s_axi_awburst, 2'b01);
    awid            = s_axi_awid;

    // Send first data beat
    m_axi_wvalid[0] = 1'b1;
    m_axi_wdata[0]  = data;
    m_axi_wstrb[0]  = '1;
    m_axi_wlast[0]  = 1'b0;

    `CHECK_TRUE(m_axi_wvalid[0] && m_axi_wready[0]);
    `CHECK_TRUE(s_axi_wvalid && s_axi_wready);
    `CHECK_EQ(s_axi_wdata, data);
    `CHECK_EQ(s_axi_wstrb, '1);
    `CHECK_FALSE(s_axi_wlast);

    `TICK(clk);
    // Second/last data beat
    m_axi_wdata[0] = data + DW'(1);
    m_axi_wlast[0] = 1'b1;

    `CHECK_TRUE(s_axi_wvalid && s_axi_wready);
    `CHECK_EQ(s_axi_wdata, data + DW'(1));
    `CHECK_EQ(s_axi_wstrb, '1);
    `CHECK_TRUE(s_axi_wlast);

    // Response phase
    `TICK(clk);
    s_axi_bvalid = 1'b1;
    s_axi_bid    = awid;
    s_axi_bresp  = 2'b00;

    `TICK(clk);
    `CHECK_TRUE(s_axi_bvalid && s_axi_bready);
    `CHECK_EQ(m_axi_bvalid, 3'b001);
    `CHECK_EQ(m_axi_bid[0], 4'h1);
    `CHECK_EQ(m_axi_bresp[0], 2'b00);

    // Clear signals
    m_axi_awvalid = '0;
    m_axi_wvalid  = '0;
    s_axi_bvalid  = 1'b0;

    `TICK(clk);
    `CHECK_FALSE(s_axi_awvalid);
    `CHECK_FALSE(s_axi_wvalid);
    `CHECK_EQ(m_axi_bvalid, 3'b000);
  endtask

  `SVC_UNUSED({m_axi_wready[NUM_M-1:1], m_axi_bid[NUM_M-1:1],
               m_axi_bresp[NUM_M-1:1]});

  `TEST_SUITE_BEGIN(svc_axi_arbiter_wr_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
