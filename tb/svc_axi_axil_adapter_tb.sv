`include "svc_unit.sv"

`include "svc_axi_axil_adapter.sv"

// This is just a quick smoke test

module svc_axi_axil_adapter_tb;
  parameter AW = 20;
  parameter DW = 16;
  parameter SW = DW / 8;
  parameter IDW = 4;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic           m_axi_awvalid;
  logic [ AW-1:0] m_axi_awaddr;
  logic [IDW-1:0] m_axi_awid;
  logic [    7:0] m_axi_awlen;
  logic [    2:0] m_axi_awsize;
  logic [    1:0] m_axi_awburst;
  logic           m_axi_awready;
  logic           m_axi_wvalid;
  logic [ DW-1:0] m_axi_wdata;
  logic [ SW-1:0] m_axi_wstrb;
  logic           m_axi_wlast;
  logic           m_axi_wready;
  logic           m_axi_bvalid;
  logic [IDW-1:0] m_axi_bid;
  logic [    1:0] m_axi_bresp;
  logic           m_axi_bready;

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

  logic [ AW-1:0] s_axil_awaddr;
  logic           s_axil_awvalid;
  logic           s_axil_awready;
  logic [ DW-1:0] s_axil_wdata;
  logic [ SW-1:0] s_axil_wstrb;
  logic           s_axil_wvalid;
  logic           s_axil_wready;
  logic [    1:0] s_axil_bresp;
  logic           s_axil_bvalid;
  logic           s_axil_bready;

  logic           s_axil_arvalid;
  logic [ AW-1:0] s_axil_araddr;
  logic           s_axil_arready;
  logic           s_axil_rvalid;
  logic [ DW-1:0] s_axil_rdata;
  logic [    1:0] s_axil_rresp;
  logic           s_axil_rready;

  svc_axi_axil_adapter #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW),
      .AXI_ID_WIDTH  (IDW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awid   (m_axi_awid),
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
      .s_axi_rready (m_axi_rready),

      .m_axil_awaddr (s_axil_awaddr),
      .m_axil_awvalid(s_axil_awvalid),
      .m_axil_awready(s_axil_awready),
      .m_axil_wdata  (s_axil_wdata),
      .m_axil_wstrb  (s_axil_wstrb),
      .m_axil_wvalid (s_axil_wvalid),
      .m_axil_wready (s_axil_wready),
      .m_axil_bresp  (s_axil_bresp),
      .m_axil_bvalid (s_axil_bvalid),
      .m_axil_bready (s_axil_bready),

      .m_axil_arvalid(s_axil_arvalid),
      .m_axil_araddr (s_axil_araddr),
      .m_axil_arready(s_axil_arready),
      .m_axil_rvalid (s_axil_rvalid),
      .m_axil_rdata  (s_axil_rdata),
      .m_axil_rresp  (s_axil_rresp),
      .m_axil_rready (s_axil_rready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_awvalid  <= 1'b0;
      m_axi_awid     <= 0;
      m_axi_awaddr   <= 0;
      m_axi_awlen    <= 8'h0;
      m_axi_awsize   <= 3'h1;
      m_axi_awburst  <= 2'h1;

      m_axi_wvalid   <= 0;
      m_axi_wdata    <= 0;
      m_axi_wstrb    <= 0;
      m_axi_wlast    <= 1'b0;

      m_axi_arvalid  <= 1'b0;
      m_axi_arid     <= 0;
      m_axi_araddr   <= 0;
      m_axi_arlen    <= 8'h0;
      m_axi_arsize   <= 3'h1;
      m_axi_arburst  <= 2'h1;

      m_axi_bready   <= 1'b0;
      m_axi_rready   <= 1'b0;

      s_axil_awready <= 1'b0;
      s_axil_wready  <= 1'b0;
      s_axil_bvalid  <= 1'b0;
      s_axil_bresp   <= 2'b00;

      s_axil_arready <= 1'b0;
      s_axil_rvalid  <= 1'b0;
      s_axil_rdata   <= 0;
      s_axil_rresp   <= 2'b00;
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
    `CHECK_FALSE(s_axil_awvalid);
    `CHECK_FALSE(s_axil_wvalid);
    `CHECK_FALSE(s_axil_arvalid);

    `CHECK_FALSE(m_axi_bvalid);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  // Basic smoke test
  task automatic test_basic_write;
    begin
      logic [AW-1:0] addr = AW'(16'hA000);
      logic [DW-1:0] data = DW'(16'hD000);

      // setup the burst
      // length 4, INCR, 2 byte stride
      m_axi_awvalid  = 1'b1;
      m_axi_awaddr   = addr;
      m_axi_awid     = 4'hD;
      m_axi_awlen    = 8'h03;
      m_axi_awburst  = 2'b01;
      m_axi_awsize   = 3'b001;

      m_axi_bready   = 1'b1;

      s_axil_awready = 1'b1;
      s_axil_wready  = 1'b1;

      // writes should be issued every clock
      `TICK(clk);
      for (int i = 0; i < 4; i++) begin
        m_axi_wvalid = 1'b1;
        m_axi_wdata  = data + DW'(i);
        m_axi_wstrb  = '1;
        m_axi_wlast  = i == 3;

        `CHECK_TRUE(s_axil_awvalid && s_axil_awready);
        `CHECK_EQ(s_axil_awaddr, addr + AW'(i * 2));

        `CHECK_TRUE(m_axi_wready);
        `CHECK_TRUE(s_axil_wvalid && s_axil_wready);
        `CHECK_EQ(s_axil_wdata, data + DW'(i));
        `CHECK_EQ(s_axil_wstrb, '1);
        s_axil_bvalid = 1'b1;

        `CHECK_TRUE(s_axil_bready);
        `CHECK_FALSE(m_axi_bvalid);
        `TICK(clk);
      end

      m_axi_wvalid  = 1'b0;
      s_axil_bvalid = 1'b0;

      `CHECK_TRUE(m_axi_bvalid && m_axi_bready);
      `CHECK_EQ(m_axi_bid, 4'hD);
      `CHECK_EQ(m_axi_bresp, 2'b00);
      `TICK(clk);

      `CHECK_FALSE(s_axil_awvalid);
      `CHECK_FALSE(s_axil_wvalid);
      `CHECK_FALSE(m_axi_bvalid);
    end
  endtask

  task automatic test_basic_read;
    begin
      logic [AW-1:0] addr = AW'(16'hA000);
      logic [DW-1:0] data = DW'(16'hD000);

      // setup the burst
      // length 4, INCR, 2 byte stride
      m_axi_arvalid  = 1'b1;
      m_axi_araddr   = addr;
      m_axi_arid     = 4'hD;
      m_axi_arlen    = 8'h03;
      m_axi_arburst  = 2'b01;
      m_axi_arsize   = 3'b001;
      m_axi_rready   = 1'b1;

      s_axil_arready = 1'b1;

      // addr beats should be accepted every clock, and read responses
      // should be immediate.
      `TICK(clk);
      for (int i = 0; i < 4; i++) begin
        `CHECK_TRUE(s_axil_arvalid && s_axil_arready);
        `CHECK_EQ(s_axil_araddr, addr + AW'(i * 2));

        s_axil_rvalid = 1'b1;
        s_axil_rdata  = data + DW'(i);

        `CHECK_TRUE(s_axil_rready);
        `CHECK_TRUE(m_axi_rvalid && m_axi_rready);
        `CHECK_EQ(m_axi_rdata, data + DW'(i));
        `CHECK_EQ(m_axi_rid, 4'hD);
        `CHECK_EQ(m_axi_rresp, 2'b00);
        `CHECK_TRUE(m_axi_rlast || i != 3);
        `TICK(clk);
      end

      s_axil_rvalid = 1'b0;
      `CHECK_FALSE(s_axil_arvalid);
      `CHECK_FALSE(m_axi_rvalid);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_axi_axil_adapter_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic_write);
  `TEST_CASE(test_basic_read);
  `TEST_SUITE_END();

endmodule
