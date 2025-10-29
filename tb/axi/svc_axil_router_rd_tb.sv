`include "svc_unit.sv"
`include "svc_axil_router_rd.sv"

module svc_axil_router_rd_tb;
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
  logic                                                m_axil_arvalid;
  logic [M_AXIL_ADDR_WIDTH-1:0]                        m_axil_araddr;
  logic                                                m_axil_arready;

  logic                                                m_axil_rvalid;
  logic [M_AXIL_DATA_WIDTH-1:0]                        m_axil_rdata;
  logic [                  1:0]                        m_axil_rresp;
  logic                                                m_axil_rready;

  logic [            NUM_S-1:0]                        s_axil_arvalid;
  logic [            NUM_S-1:0][S_AXIL_ADDR_WIDTH-1:0] s_axil_araddr;
  logic [            NUM_S-1:0]                        s_axil_arready;

  logic [            NUM_S-1:0]                        s_axil_rvalid;
  logic [            NUM_S-1:0][S_AXIL_DATA_WIDTH-1:0] s_axil_rdata;
  logic [            NUM_S-1:0][                  1:0] s_axil_rresp;
  logic [            NUM_S-1:0]                        s_axil_rready;

  svc_axil_router_rd #(
      .S_AXIL_ADDR_WIDTH(M_AXIL_ADDR_WIDTH),
      .S_AXIL_DATA_WIDTH(M_AXIL_DATA_WIDTH),
      .M_AXIL_ADDR_WIDTH(S_AXIL_ADDR_WIDTH),
      .M_AXIL_DATA_WIDTH(S_AXIL_DATA_WIDTH),
      .NUM_S            (NUM_S)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axil_arvalid(m_axil_arvalid),
      .s_axil_araddr (m_axil_araddr),
      .s_axil_arready(m_axil_arready),

      .s_axil_rvalid(m_axil_rvalid),
      .s_axil_rdata (m_axil_rdata),
      .s_axil_rresp (m_axil_rresp),
      .s_axil_rready(m_axil_rready),

      .m_axil_arvalid(s_axil_arvalid),
      .m_axil_araddr (s_axil_araddr),
      .m_axil_arready(s_axil_arready),

      .m_axil_rvalid(s_axil_rvalid),
      .m_axil_rdata (s_axil_rdata),
      .m_axil_rresp (s_axil_rresp),
      .m_axil_rready(s_axil_rready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axil_arvalid <= 1'b0;
      m_axil_araddr  <= '0;
      m_axil_rready  <= 1'b0;

      for (int i = 0; i < NUM_S; i++) begin
        s_axil_arready[i] <= 1'b0;
        s_axil_rvalid[i]  <= 1'b0;
        s_axil_rdata[i]   <= '0;
        s_axil_rresp[i]   <= 2'b00;
      end

    end else begin
      m_axil_arvalid <= m_axil_arvalid & ~m_axil_arready;
      s_axil_rvalid  <= s_axil_rvalid & ~s_axil_rready;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(m_axil_rvalid);

    for (int i = 0; i < NUM_S; i++) begin
      `CHECK_FALSE(s_axil_arvalid[i]);
    end
  endtask

  task automatic test_basic_routing();
    logic [M_AXIL_ADDR_WIDTH-1:0] addr;
    for (int sub = 0; sub < NUM_S; sub++) begin
      // Create address with the subordinate ID in the upper bits
      addr = {sub[SEL_W-1:0], {(M_AXIL_ADDR_WIDTH - SEL_W) {1'b0}}} | 'h1000;

      `CHECK_FALSE(uut.active);

      m_axil_arvalid = 1'b1;
      m_axil_araddr  = addr;
      s_axil_arready = '0;

      `CHECK_WAIT_FOR(clk, s_axil_arvalid[sub], 3);
      `CHECK_EQ(s_axil_araddr[sub], S_AXIL_ADDR_WIDTH'({
                {SEL_W{1'b0}}, addr[M_AXIL_ADDR_WIDTH-SEL_W-1:0]}));
      `CHECK_TRUE(uut.active);

      // accept at sub
      s_axil_arready[sub] = 1'b1;
      `TICK(clk);
      s_axil_arready = '0;

      `CHECK_EQ(s_axil_arvalid, 0);
      `CHECK_TRUE(uut.active);

      // Send read response
      s_axil_rvalid[sub] = 1'b1;
      s_axil_rdata[sub]  = S_AXIL_DATA_WIDTH'(sub);
      s_axil_rresp[sub]  = 2'b00;
      m_axil_rready      = 1'b1;

      `CHECK_WAIT_FOR(clk, m_axil_rvalid && m_axil_rready);
      `CHECK_FALSE(uut.active);
      `CHECK_EQ(m_axil_rdata, M_AXIL_DATA_WIDTH'(sub));
      `CHECK_EQ(m_axil_rresp, 2'b00);
    end
  endtask

  task automatic test_error_response();
    m_axil_arvalid    = 1'b1;
    m_axil_araddr     = 0;
    s_axil_arready[0] = 1'b1;

    `CHECK_WAIT_FOR(clk, s_axil_arvalid[0] && s_axil_arready[0]);
    s_axil_rvalid[0] = 1'b1;
    s_axil_rdata[0]  = '1;
    s_axil_rresp[0]  = 2'b10;
    m_axil_rready    = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_rvalid && m_axil_rready);
    `CHECK_EQ(m_axil_rresp, 2'b10);

    s_axil_rvalid[0] = 1'b0;
    m_axil_rready    = 1'b0;

    `TICK(clk);
  endtask

  task automatic test_bad_addr();
    m_axil_arvalid = 1'b1;
    m_axil_araddr  = '1;
    m_axil_rready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_rvalid && m_axil_rready);
    `CHECK_EQ(m_axil_rdata, 32'hADD1EBAD);
    `CHECK_EQ(m_axil_rresp, 2'b11);
  endtask


  `TEST_SUITE_BEGIN(svc_axil_router_rd_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_routing);
  `TEST_CASE(test_error_response);
  `TEST_CASE(test_bad_addr);
  `TEST_SUITE_END();

endmodule
