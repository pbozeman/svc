`include "svc_unit.sv"

`include "svc_axi_axil_reflect_wr.sv"

// This is just a quick smoke test. The formal verification is more comprehensive.

// verilator lint_off: UNUSEDSIGNAL
module svc_axi_axil_reflect_wr_tbi;
  parameter AW = 20;
  parameter DW = 16;
  parameter SW = DW / 8;
  parameter IW = 4;
  parameter UW = 2;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic          m_axi_awvalid;
  logic [AW-1:0] m_axi_awaddr;
  logic [IW-1:0] m_axi_awid;
  logic [   7:0] m_axi_awlen;
  logic [   2:0] m_axi_awsize;
  logic [   1:0] m_axi_awburst;
  logic [UW-1:0] m_axi_awuser;
  logic          m_axi_awready;
  logic          m_axi_wvalid;
  logic [DW-1:0] m_axi_wdata;
  logic [SW-1:0] m_axi_wstrb;
  logic          m_axi_wlast;
  logic          m_axi_wready;
  logic          m_axi_bvalid;
  logic [IW-1:0] m_axi_bid;
  logic [   1:0] m_axi_bresp;
  logic [UW-1:0] m_axi_buser;
  logic          m_axi_bready;

  logic [AW-1:0] s_axil_awaddr;
  logic          s_axil_awvalid;
  logic          s_axil_awready;
  logic [DW-1:0] s_axil_wdata;
  logic [SW-1:0] s_axil_wstrb;
  logic          s_axil_wvalid;
  logic          s_axil_wready;
  logic [   1:0] s_axil_bresp;
  logic          s_axil_bvalid;
  logic          s_axil_bready;

  svc_axi_axil_reflect_wr #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_STRB_WIDTH(SW),
      .AXI_ID_WIDTH  (IW),
      .AXI_USER_WIDTH(UW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_awuser (m_axi_awuser),
      .s_axi_awready(m_axi_awready),
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wlast  (m_axi_wlast),
      .s_axi_wready (m_axi_wready),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bid    (m_axi_bid),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_buser  (m_axi_buser),
      .s_axi_bready (m_axi_bready),

      .m_axil_awaddr (s_axil_awaddr),
      .m_axil_awvalid(s_axil_awvalid),
      .m_axil_awready(s_axil_awready),
      .m_axil_wdata  (s_axil_wdata),
      .m_axil_wstrb  (s_axil_wstrb),
      .m_axil_wvalid (s_axil_wvalid),
      .m_axil_wready (s_axil_wready),
      .m_axil_bresp  (s_axil_bresp),
      .m_axil_bvalid (s_axil_bvalid),
      .m_axil_bready (s_axil_bready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_awvalid  <= 1'b0;
      m_axi_awid     <= 0;
      m_axi_awaddr   <= 0;
      m_axi_awlen    <= 8'h0;
      m_axi_awsize   <= 3'h1;
      m_axi_awburst  <= 2'h1;
      m_axi_awuser   <= 0;

      m_axi_wvalid   <= 0;
      m_axi_wdata    <= 0;
      m_axi_wstrb    <= 0;
      m_axi_wlast    <= 1'b0;

      m_axi_bready   <= 1'b0;

      s_axil_awready <= 1'b0;
      s_axil_wready  <= 1'b0;
      s_axil_bvalid  <= 1'b0;
      s_axil_bresp   <= 2'b00;
    end
  end

  always_ff @(posedge clk) begin
    if (m_axi_awvalid && m_axi_awready) begin
      m_axi_awvalid <= 1'b0;
    end

    if (m_axi_wvalid && m_axi_wready) begin
      m_axi_wvalid <= 1'b0;
    end

    if (s_axil_bvalid && s_axil_bready) begin
      s_axil_bvalid <= 1'b0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_axil_awvalid);
    `CHECK_FALSE(m_axi_wvalid);
    `CHECK_FALSE(m_axi_bvalid);
  endtask

  // Basic smoke test
  task automatic test_basic;
    begin
      logic [AW-1:0] addr = AW'(16'hA000);
      logic [DW-1:0] data = DW'(16'hD000);
      logic [IW-1:0] id = IW'(4'h5);
      logic [UW-1:0] user = UW'('1);

      m_axi_awvalid  = 1'b1;
      m_axi_awid     = id;
      m_axi_awaddr   = addr;
      m_axi_awlen    = 8'h0;
      m_axi_awsize   = 3'h1;
      m_axi_awburst  = 2'h0;
      m_axi_awuser   = user;

      m_axi_wvalid   = 1'b1;
      m_axi_wdata    = data;
      m_axi_wstrb    = '1;
      m_axi_wlast    = 1'b1;

      m_axi_bready   = 1'b1;

      s_axil_awready = 1'b1;
      s_axil_wready  = 1'b1;

      `CHECK_WAIT_FOR(clk, s_axil_awvalid && s_axil_awready);
      `CHECK_WAIT_FOR(clk, s_axil_wvalid && s_axil_wready);
      s_axil_bvalid = 1'b1;
      s_axil_bresp  = 2'b00;

      `CHECK_WAIT_FOR(clk, m_axi_bvalid && m_axi_bready);
      `CHECK_EQ(m_axi_bid, id);
      `CHECK_EQ(m_axi_bresp, 2'b00);
      `CHECK_EQ(m_axi_buser, user);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_axi_axil_reflect_wr_tbi);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
