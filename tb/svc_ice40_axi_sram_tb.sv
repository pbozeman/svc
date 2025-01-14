`include "svc_unit.sv"

`include "svc_ice40_axi_sram.sv"
`include "svc_model_sram.sv"

module svc_ice40_axi_sram_tb;
  parameter AW = 16;
  parameter DW = 8;
  parameter IDW = 4;
  parameter SW = (DW / 8);
  parameter LSB = $clog2(DW) - 3;
  parameter SAW = AW - LSB;

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

  logic [SAW-1:0] sram_io_addr;
  wire  [ DW-1:0] sram_io_data;
  logic           sram_io_we_n;
  logic           sram_io_oe_n;
  logic           sram_io_ce_n;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  svc_ice40_axi_sram #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_DATA_WIDTH(DW)
  ) svc_ice40_axi_sram_i (
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

      .sram_io_addr(sram_io_addr),
      .sram_io_data(sram_io_data),
      .sram_io_we_n(sram_io_we_n),
      .sram_io_oe_n(sram_io_oe_n),
      .sram_io_ce_n(sram_io_ce_n)
  );

  svc_model_sram #(
      .ADDR_WIDTH(SAW),
      .DATA_WIDTH(DW)
  ) svc_model_sram_i (
      .rst_n  (rst_n),
      .we_n   (sram_io_we_n),
      .oe_n   (sram_io_oe_n),
      .ce_n   (sram_io_ce_n),
      .addr   (sram_io_addr),
      .data_io(sram_io_data)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_axi_awvalid <= 1'b0;
      m_axi_awid    <= 0;
      m_axi_awaddr  <= 0;
      m_axi_awlen   <= 8'h0;
      m_axi_awsize  <= 3'h1;
      m_axi_awburst <= 2'h1;

      m_axi_wvalid  <= 0;
      m_axi_wdata   <= 0;
      m_axi_wstrb   <= 0;
      m_axi_wlast   <= 1'b0;

      m_axi_arvalid <= 1'b0;
      m_axi_arid    <= 0;
      m_axi_araddr  <= 0;
      m_axi_arlen   <= 8'h0;
      m_axi_arsize  <= 3'h1;
      m_axi_arburst <= 2'h1;

      m_axi_bready  <= 1'b0;
      m_axi_rready  <= 1'b0;
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
    `CHECK_FALSE(m_axi_bvalid);
    `CHECK_FALSE(m_axi_rvalid);
  endtask

  // Basic smoke test
  task automatic test_basic_io;
    begin
      logic [AW-1:0] addr = AW'(16'hA000);
      logic [DW-1:0] data = DW'(16'hD000);

      // setup the burst
      // length 4, INCR, 2 byte stride
      m_axi_awvalid = 1'b1;
      m_axi_awaddr  = addr;
      m_axi_awid    = 4'hD;
      m_axi_awlen   = 8'h03;
      m_axi_awburst = 2'b01;
      m_axi_awsize  = 3'b001;

      m_axi_bready  = 1'b1;

      for (int i = 0; i < 4; i++) begin
        m_axi_wvalid = 1'b1;
        m_axi_wdata  = data + DW'(i);
        m_axi_wstrb  = '1;
        m_axi_wlast  = i == 3;

        `CHECK_TRUE(m_axi_wvalid && m_axi_wready);
        `TICK(clk);
      end
      m_axi_wvalid = 1'b0;

      `CHECK_WAIT_FOR(clk, m_axi_bvalid && m_axi_bready);
      `CHECK_EQ(m_axi_bid, 4'hD);
      `CHECK_EQ(m_axi_bresp, 2'b00);

      `TICK(clk);
      `CHECK_FALSE(m_axi_bvalid);

      // read it back
      m_axi_arvalid = 1'b1;
      m_axi_araddr  = addr;
      m_axi_arid    = 4'hD;
      m_axi_arlen   = 8'h03;
      m_axi_arburst = 2'b01;
      m_axi_arsize  = 3'b001;
      m_axi_rready  = 1'b1;

      for (int i = 0; i < 4; i++) begin
        `CHECK_WAIT_FOR(clk, m_axi_rvalid && m_axi_rready);
        `CHECK_EQ(m_axi_rdata, data + DW'(i));
        `CHECK_EQ(m_axi_rid, 4'hD);
        `CHECK_EQ(m_axi_rresp, 2'b00);
        `CHECK_TRUE(m_axi_rlast || i != 3);
        `TICK(clk);
      end
      `CHECK_FALSE(m_axi_rvalid);

    end
  endtask


  `TEST_SUITE_BEGIN(svc_ice40_axi_sram_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic_io);
  `TEST_SUITE_END();

endmodule
