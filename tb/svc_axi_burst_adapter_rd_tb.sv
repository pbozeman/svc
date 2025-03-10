`include "svc_unit.sv"

`include "svc_axi_burst_adapter_rd.sv"

// This is just a quick smoke test

// verilator lint_off: UNUSEDSIGNAL
module svc_axi_burst_adapter_rd_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter IDW = 4;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic           m_axi_arvalid;
  logic [IDW-1:0] m_axi_arid;
  logic [ AW-1:0] m_axi_araddr;
  logic [    7:0] m_axi_arlen;
  logic [    2:0] m_axi_arsize;
  logic [    1:0] m_axi_arburst;
  logic           m_axi_arready;
  logic           m_axi_rvalid;
  logic [IDW-1:0] m_axi_rid;
  logic [ DW-1:0] m_axi_rdata;
  logic [    1:0] m_axi_rresp;
  logic           m_axi_rlast;
  logic           m_axi_rready;

  logic           s_axi_arvalid;
  logic [IDW-1:0] s_axi_arid;
  logic [ AW-1:0] s_axi_araddr;
  logic [    7:0] s_axi_arlen;
  logic [    2:0] s_axi_arsize;
  logic [    1:0] s_axi_arburst;
  logic           s_axi_arready;
  logic           s_axi_rvalid;
  logic [IDW-1:0] s_axi_rid;
  logic [ DW-1:0] s_axi_rdata;
  logic [    1:0] s_axi_rresp;
  logic           s_axi_rlast;
  logic           s_axi_rready;

  svc_axi_burst_adapter_rd #(
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
      m_axi_arvalid <= 1'b0;
      m_axi_arid    <= 0;
      m_axi_araddr  <= 0;
      m_axi_arlen   <= 8'h0;
      m_axi_arsize  <= 3'h1;
      m_axi_arburst <= 2'h1;

      m_axi_rready  <= 1'b0;

      s_axi_arready <= 1'b0;

      s_axi_rvalid  <= 1'b0;
      s_axi_rid     <= 0;
      s_axi_rdata   <= 0;
      s_axi_rresp   <= 2'b00;
      s_axi_rlast   <= 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axi_arvalid && m_axi_arready) begin
      m_axi_arvalid <= 1'b0;
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

    // setup the burst
    // length 4, INCR, 2 byte stride
    m_axi_arvalid = 1'b1;
    m_axi_araddr  = addr;
    m_axi_arid    = 4'hD;
    m_axi_arlen   = 8'h03;
    m_axi_arburst = 2'b01;
    m_axi_arsize  = 3'b001;
    m_axi_rready  = 1'b1;

    s_axi_arready = 1'b1;

    // addr beats should be accepted every clock
    `TICK(clk);
    for (int i = 0; i < 4; i++) begin
      `CHECK_WAIT_FOR(clk, s_axi_arvalid && s_axi_arready, 1);
      `CHECK_EQ(s_axi_araddr, addr + AW'(i * 2));

      s_axi_rvalid = 1'b1;
      s_axi_rid    = 4'hD;
      s_axi_rdata  = data + DW'(i);
      s_axi_rlast  = 1'b1;
      `TICK(clk);

      `CHECK_TRUE(s_axi_rready);
      `CHECK_TRUE(m_axi_rvalid && m_axi_rready);
      `CHECK_EQ(m_axi_rdata, data + DW'(i));
      `CHECK_EQ(m_axi_rid, 4'hD);
      `CHECK_EQ(m_axi_rresp, 2'b00);
      `CHECK_TRUE(m_axi_rlast || i != 3);
    end

    s_axi_rvalid = 1'b0;
    `CHECK_FALSE(s_axi_arvalid);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_burst_adapter_rd_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
