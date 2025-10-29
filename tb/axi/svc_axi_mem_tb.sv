`include "svc_unit.sv"

`include "svc_axi_mem.sv"

// This is just a quick smoke test. The real testing is via formal.

module svc_axi_mem_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter IDW = 4;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic            m_axi_awvalid;
  logic [ IDW-1:0] m_axi_awid;
  logic [  AW-1:0] m_axi_awaddr;
  logic [     7:0] m_axi_awlen;
  logic [     2:0] m_axi_awsize;
  logic [     1:0] m_axi_awburst;
  logic            m_axi_awready;

  logic            m_axi_wvalid;
  logic [  DW-1:0] m_axi_wdata;
  logic [DW/8-1:0] m_axi_wstrb;
  logic            m_axi_wlast;
  logic            m_axi_wready;

  logic            m_axi_bvalid;
  logic [ IDW-1:0] m_axi_bid;
  logic [     1:0] m_axi_bresp;
  logic            m_axi_bready;

  logic            m_axi_arvalid;
  logic [ IDW-1:0] m_axi_arid;
  logic [  AW-1:0] m_axi_araddr;
  logic [     7:0] m_axi_arlen;
  logic [     2:0] m_axi_arsize;
  logic [     1:0] m_axi_arburst;
  logic            m_axi_arready;

  logic            m_axi_rvalid;
  logic [ IDW-1:0] m_axi_rid;
  logic [  DW-1:0] m_axi_rdata;
  logic [     1:0] m_axi_rresp;
  logic            m_axi_rlast;
  logic            m_axi_rready;

  svc_axi_mem #(
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
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wlast  (m_axi_wlast),
      .s_axi_wready (m_axi_wready),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bid    (m_axi_bid),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_bready (m_axi_bready),

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
      .s_axi_rready (m_axi_rready)
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

      m_axi_arvalid <= '0;
      m_axi_arid    <= '0;
      m_axi_araddr  <= '0;
      m_axi_arlen   <= '0;
      m_axi_arsize  <= '0;
      m_axi_arburst <= '0;

      m_axi_rready  <= '0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axi_awvalid && m_axi_awready) begin
      m_axi_awvalid <= 1'b0;
    end

    if (m_axi_arvalid && m_axi_arready) begin
      m_axi_arvalid <= 1'b0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(m_axi_rvalid);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  // Basic smoke test
  task automatic test_basic;
    logic [ AW-1:0] addr = AW'(16'hA000);
    logic [ DW-1:0] data = DW'(16'hD000);
    logic [IDW-1:0] id = IDW'(4'hD);

    // Set up a burst from master 0
    // length 2, INCR, 2 byte stride
    m_axi_awvalid = 1'b1;
    m_axi_awaddr  = addr;
    m_axi_awid    = id;
    m_axi_awlen   = 8'h01;
    m_axi_awburst = 2'b01;
    m_axi_awsize  = 3'b001;

    m_axi_bready  = 1'b1;

    // Send first data beat
    m_axi_wvalid  = 1'b1;
    m_axi_wdata   = data;
    m_axi_wstrb   = '1;
    m_axi_wlast   = 1'b0;
    `CHECK_WAIT_FOR(clk, m_axi_wvalid && m_axi_wready);
    `TICK(clk);

    // Second/last data beat
    m_axi_wvalid = 1'b1;
    m_axi_wdata  = data + DW'(1);
    m_axi_wlast  = 1'b1;
    `TICK(clk);
    m_axi_wvalid = 1'b0;

    `CHECK_WAIT_FOR(clk, m_axi_bvalid && m_axi_bready);
    `CHECK_EQ(m_axi_bid, id);
    `CHECK_EQ(m_axi_bresp, 2'b00);

    //
    // Read it back
    //
    m_axi_arvalid = 1'b1;
    m_axi_araddr  = addr;
    m_axi_arid    = id;
    m_axi_arlen   = 8'h01;
    m_axi_arburst = 2'b01;
    m_axi_arsize  = 3'b001;

    m_axi_rready  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_FALSE(m_axi_rlast);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_EQ(m_axi_rdata, data);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
    `CHECK_EQ(m_axi_rid, id);
    `CHECK_EQ(m_axi_rresp, 2'b00);
    `CHECK_TRUE(m_axi_rlast);
    `CHECK_EQ(m_axi_rdata, data + DW'(1));

    `TICK(clk);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_mem_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
