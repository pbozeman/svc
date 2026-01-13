`include "svc_unit.sv"
`include "svc_axil_router_wr.sv"

module svc_axil_router_wr_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // Keep M/S different to catch bad types and/or casts.
  localparam M_AXIL_ADDR_WIDTH = 30;
  localparam M_AXIL_DATA_WIDTH = 32;

  localparam S_AXIL_ADDR_WIDTH = M_AXIL_ADDR_WIDTH - 4;
  localparam S_AXIL_DATA_WIDTH = M_AXIL_DATA_WIDTH - 8;

  // NUM_S must not be a power of 2 in order for the bad_addr test
  // to work.. (i.e. there must be a bad addr)
  localparam NUM_S = 3;
  localparam SEL_W = $clog2(NUM_S);

  // Module interface signals
  logic                                                    m_axil_awvalid;
  logic [  M_AXIL_ADDR_WIDTH-1:0]                          m_axil_awaddr;
  logic                                                    m_axil_awready;

  logic                                                    m_axil_wvalid;
  logic [  M_AXIL_DATA_WIDTH-1:0]                          m_axil_wdata;
  logic [M_AXIL_DATA_WIDTH/8-1:0]                          m_axil_wstrb;
  logic                                                    m_axil_wready;

  logic                                                    m_axil_bvalid;
  logic [                    1:0]                          m_axil_bresp;
  logic                                                    m_axil_bready;

  logic [              NUM_S-1:0]                          s_axil_awvalid;
  logic [              NUM_S-1:0][  S_AXIL_ADDR_WIDTH-1:0] s_axil_awaddr;
  logic [              NUM_S-1:0]                          s_axil_awready;

  logic [              NUM_S-1:0]                          s_axil_wvalid;
  logic [              NUM_S-1:0][  S_AXIL_DATA_WIDTH-1:0] s_axil_wdata;
  logic [              NUM_S-1:0][S_AXIL_DATA_WIDTH/8-1:0] s_axil_wstrb;
  logic [              NUM_S-1:0]                          s_axil_wready;

  logic [              NUM_S-1:0]                          s_axil_bvalid;
  logic [              NUM_S-1:0][                    1:0] s_axil_bresp;
  logic [              NUM_S-1:0]                          s_axil_bready;

  svc_axil_router_wr #(
      .S_AXIL_ADDR_WIDTH(M_AXIL_ADDR_WIDTH),
      .S_AXIL_DATA_WIDTH(M_AXIL_DATA_WIDTH),
      .M_AXIL_ADDR_WIDTH(S_AXIL_ADDR_WIDTH),
      .M_AXIL_DATA_WIDTH(S_AXIL_DATA_WIDTH),
      .NUM_S            (NUM_S)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_awvalid(m_axil_awvalid),
      .s_axil_awaddr (m_axil_awaddr),
      .s_axil_awready(m_axil_awready),

      .s_axil_wvalid(m_axil_wvalid),
      .s_axil_wdata (m_axil_wdata),
      .s_axil_wstrb (m_axil_wstrb),
      .s_axil_wready(m_axil_wready),

      .s_axil_bvalid(m_axil_bvalid),
      .s_axil_bresp (m_axil_bresp),
      .s_axil_bready(m_axil_bready),

      .m_axil_awvalid(s_axil_awvalid),
      .m_axil_awaddr (s_axil_awaddr),
      .m_axil_awready(s_axil_awready),

      .m_axil_wvalid(s_axil_wvalid),
      .m_axil_wdata (s_axil_wdata),
      .m_axil_wstrb (s_axil_wstrb),
      .m_axil_wready(s_axil_wready),

      .m_axil_bvalid(s_axil_bvalid),
      .m_axil_bresp (s_axil_bresp),
      .m_axil_bready(s_axil_bready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axil_awvalid <= 1'b0;
      m_axil_awaddr  <= '0;
      m_axil_wvalid  <= 1'b0;
      m_axil_wdata   <= '0;
      m_axil_wstrb   <= '0;
      m_axil_bready  <= 1'b0;

      for (int i = 0; i < NUM_S; i++) begin
        s_axil_awready[i] <= 1'b0;
        s_axil_wready[i]  <= 1'b0;
        s_axil_bvalid[i]  <= 1'b0;
        s_axil_bresp[i]   <= 2'b00;
      end
    end else begin
      m_axil_awvalid <= m_axil_awvalid & ~m_axil_awready;
      m_axil_wvalid  <= m_axil_wvalid & ~m_axil_wready;
      s_axil_bvalid  <= s_axil_bvalid & ~s_axil_bready;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(m_axil_bvalid);

    for (int i = 0; i < NUM_S; i++) begin
      `CHECK_FALSE(s_axil_awvalid[i]);
      `CHECK_FALSE(s_axil_wvalid[i]);
    end
  endtask

  task automatic test_basic_routing();
    logic [M_AXIL_ADDR_WIDTH-1:0] addr;
    for (int sub = 0; sub < NUM_S; sub++) begin
      // Create address with the subordinate ID in the upper bits
      addr = {sub[SEL_W-1:0], {(M_AXIL_ADDR_WIDTH - SEL_W) {1'b0}}} | 'h1000;

      `CHECK_FALSE(uut.active);

      // Set both AW and W channels valid to proceed
      m_axil_awvalid = 1'b1;
      m_axil_awaddr  = addr;
      m_axil_wvalid  = 1'b1;
      m_axil_wdata   = M_AXIL_DATA_WIDTH'(32'hABCD0000 | sub);
      m_axil_wstrb   = '1;
      s_axil_awready = '0;
      s_axil_wready  = '0;

      // Wait for both channels to be valid to subordinate
      `CHECK_WAIT_FOR(clk, s_axil_awvalid[sub] && s_axil_wvalid[sub], 3);
      `CHECK_EQ(s_axil_awaddr[sub], S_AXIL_ADDR_WIDTH'({
                {SEL_W{1'b0}}, addr[M_AXIL_ADDR_WIDTH-SEL_W-1:0]}));
      `CHECK_EQ(s_axil_wdata[sub], S_AXIL_DATA_WIDTH'(32'hABCD0000 | sub));
      `CHECK_EQ(s_axil_wstrb[sub], '1);
      `CHECK_TRUE(uut.active);

      // Accept at subordinate (both channels)
      s_axil_awready[sub] = 1'b1;
      s_axil_wready[sub]  = 1'b1;
      `TICK(clk);
      s_axil_awready = '0;
      s_axil_wready  = '0;

      `CHECK_EQ(s_axil_awvalid, 0);
      `CHECK_EQ(s_axil_wvalid, 0);
      `CHECK_TRUE(uut.active);

      // Send write response
      s_axil_bvalid[sub] = 1'b1;
      s_axil_bresp[sub]  = 2'b00;
      m_axil_bready      = 1'b1;

      `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
      `CHECK_FALSE(uut.active);
      `CHECK_EQ(m_axil_bresp, 2'b00);
    end
  endtask

  task automatic test_error_response();
    m_axil_awvalid    = 1'b1;
    m_axil_awaddr     = 0;
    m_axil_wvalid     = 1'b1;
    m_axil_wdata      = 32'h12345678;
    m_axil_wstrb      = '1;
    s_axil_awready[0] = 1'b1;
    s_axil_wready[0]  = 1'b1;

    `CHECK_WAIT_FOR(clk,
                    (s_axil_awvalid[0] && s_axil_awready[0] &&
                     s_axil_wvalid[0] && s_axil_wready[0]));
    s_axil_bvalid[0] = 1'b1;
    s_axil_bresp[0]  = 2'b10;
    m_axil_bready    = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
    `CHECK_EQ(m_axil_bresp, 2'b10);

    s_axil_bvalid[0] = 1'b0;
    m_axil_bready    = 1'b0;

    `TICK(clk);
  endtask

  task automatic test_bad_addr();
    m_axil_awvalid = 1'b1;
    m_axil_awaddr  = '1;  // Invalid address
    m_axil_wvalid  = 1'b1;
    m_axil_wdata   = 32'hDEADBEEF;
    m_axil_wstrb   = '1;
    m_axil_bready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_bvalid && m_axil_bready);
    `CHECK_EQ(m_axil_bresp, 2'b11);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_router_wr_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_routing);
  `TEST_CASE(test_error_response);
  `TEST_CASE(test_bad_addr);
  `TEST_SUITE_END();

endmodule
