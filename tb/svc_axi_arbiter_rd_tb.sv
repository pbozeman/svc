`include "svc_unit.sv"

`include "svc_axi_arbiter_rd.sv"
`include "svc_unused.sv"

// This is just a quick smoke test. The real testing is via formal of the
// combined rw module.

module svc_axi_arbiter_rd_tb;
  parameter NUM_M = 3;
  parameter AW = 20;
  parameter DW = 16;
  parameter IDW = 4;
  parameter S_IDW = IDW + $clog2(NUM_M);

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [NUM_M-1:0]          m_axi_arvalid;
  logic [NUM_M-1:0][IDW-1:0] m_axi_arid;
  logic [NUM_M-1:0][ AW-1:0] m_axi_araddr;
  logic [NUM_M-1:0][    7:0] m_axi_arlen;
  logic [NUM_M-1:0][    2:0] m_axi_arsize;
  logic [NUM_M-1:0][    1:0] m_axi_arburst;
  logic [NUM_M-1:0]          m_axi_arready;
  logic [NUM_M-1:0]          m_axi_rvalid;
  logic [NUM_M-1:0][IDW-1:0] m_axi_rid;
  logic [NUM_M-1:0][ DW-1:0] m_axi_rdata;
  logic [NUM_M-1:0][    1:0] m_axi_rresp;
  logic [NUM_M-1:0]          m_axi_rlast;
  logic [NUM_M-1:0]          m_axi_rready;

  logic                      s_axi_arvalid;
  logic [S_IDW-1:0]          s_axi_arid;
  logic [   AW-1:0]          s_axi_araddr;
  logic [      7:0]          s_axi_arlen;
  logic [      2:0]          s_axi_arsize;
  logic [      1:0]          s_axi_arburst;
  logic                      s_axi_arready;
  logic                      s_axi_rvalid;
  logic [S_IDW-1:0]          s_axi_rid;
  logic [   DW-1:0]          s_axi_rdata;
  logic [      1:0]          s_axi_rresp;
  logic                      s_axi_rlast;
  logic                      s_axi_rready;

  svc_axi_arbiter_rd #(
      .NUM_M         (NUM_M),
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arid   (m_axi_arid),
      .s_axi_araddr (m_axi_araddr),
      .s_axi_arlen  (m_axi_arlen),
      .s_axi_arsize (m_axi_arsize),
      .s_axi_arburst(m_axi_arburst),
      .s_axi_arready(m_axi_arready),
      .s_axi_rvalid (m_axi_rvalid),
      .s_axi_rid    (m_axi_rid),
      .s_axi_rdata  (m_axi_rdata),
      .s_axi_rresp  (m_axi_rresp),
      .s_axi_rlast  (m_axi_rlast),
      .s_axi_rready (m_axi_rready),

      .m_axi_arvalid(s_axi_arvalid),
      .m_axi_arid   (s_axi_arid),
      .m_axi_araddr (s_axi_araddr),
      .m_axi_arlen  (s_axi_arlen),
      .m_axi_arsize (s_axi_arsize),
      .m_axi_arburst(s_axi_arburst),
      .m_axi_arready(s_axi_arready),
      .m_axi_rvalid (s_axi_rvalid),
      .m_axi_rid    (s_axi_rid),
      .m_axi_rdata  (s_axi_rdata),
      .m_axi_rresp  (s_axi_rresp),
      .m_axi_rlast  (s_axi_rlast),
      .m_axi_rready (s_axi_rready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_arvalid <= '0;
      m_axi_arid    <= '0;
      m_axi_araddr  <= '0;
      m_axi_arlen   <= '0;
      m_axi_arsize  <= '0;
      m_axi_arburst <= '0;

      m_axi_rready  <= '0;

      s_axi_arready <= 1'b0;
      s_axi_rvalid  <= 1'b0;
      s_axi_rid     <= 0;
      s_axi_rdata   <= 0;
      s_axi_rresp   <= 2'b00;
      s_axi_rlast   <= 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    for (int i = 0; i < NUM_M; i++) begin
      if (m_axi_arvalid[i] && m_axi_arready[i]) begin
        m_axi_arvalid[i] <= 1'b0;
      end
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axi_arvalid);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  // Basic smoke test
  task automatic test_basic;
    logic [AW-1:0] addr = AW'(16'hA000);
    logic [DW-1:0] data = DW'(16'hD000);

    m_axi_arvalid    = '0;
    m_axi_rready     = '1;

    // Set up a burst from master 0
    // length 2, INCR, 2 byte stride
    m_axi_arvalid[0] = 1'b1;
    m_axi_araddr[0]  = addr;
    m_axi_arid[0]    = 4'h1;
    m_axi_arlen[0]   = 8'h01;
    m_axi_arburst[0] = 2'b01;
    m_axi_arsize[0]  = 3'b001;

    s_axi_arready    = 1'b1;

    // First clock - check arbitration and address phase
    `CHECK_TRUE(m_axi_arvalid[0] && m_axi_arready[0]);
    `TICK(clk);
    `CHECK_FALSE(m_axi_arvalid[0]);

    `CHECK_TRUE(s_axi_arvalid);
    `CHECK_EQ(s_axi_araddr, addr);
    `CHECK_EQ(s_axi_arlen, 8'h01);
    `CHECK_EQ(s_axi_arsize, 3'b001);
    `CHECK_EQ(s_axi_arburst, 2'b01);

    // Provide first data beat
    s_axi_rvalid = 1'b1;
    s_axi_rid    = s_axi_arid;
    s_axi_rdata  = data;
    s_axi_rlast  = 1'b0;
    s_axi_rresp  = 2'b00;

    `TICK(clk);
    `CHECK_FALSE(s_axi_arvalid);
    `CHECK_TRUE(s_axi_rvalid && s_axi_rready);
    `CHECK_EQ(m_axi_rvalid, 3'b001);
    `CHECK_EQ(m_axi_rdata[0], data);

    // Second/last data beat
    s_axi_rdata = data + DW'(1);
    s_axi_rlast = 1'b1;

    `TICK(clk);
    `CHECK_EQ(m_axi_rvalid, 3'b001);
    `CHECK_EQ(m_axi_rid[0], 4'h1);
    `CHECK_EQ(m_axi_rresp[0], 2'b00);
    `CHECK_EQ(m_axi_rdata[0], data + DW'(1));
    `CHECK_TRUE(m_axi_rlast[0]);

    // Clear signals
    m_axi_arvalid = '0;
    s_axi_rvalid  = 1'b0;
    s_axi_rlast   = 1'b0;

    `TICK(clk);
    `CHECK_FALSE(s_axi_arvalid);
    `CHECK_EQ(m_axi_rvalid, 3'b000);
  endtask

  `SVC_UNUSED({m_axi_rid[NUM_M-1:1], m_axi_rdata[NUM_M-1:1],
               m_axi_rresp[NUM_M-1:1], m_axi_rlast[NUM_M-1:1]});

  `TEST_SUITE_BEGIN(svc_axi_arbiter_rd_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
