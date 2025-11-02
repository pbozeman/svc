`include "svc_unit.sv"

`include "svc_mem_bram.sv"

module svc_mem_bram_tb;
  localparam DW = 32;
  localparam AW = 10;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [31:0] araddr;
  logic        arvalid;
  logic        arready;
  logic [31:0] rdata;
  logic        rvalid;
  logic        rready;

  logic [31:0] awaddr;
  logic        awvalid;
  logic        awready;
  logic [31:0] wdata;
  logic [ 3:0] wstrb;
  logic        wvalid;
  logic        wready;

  svc_mem_bram #(
      .DW(DW),
      .AW(AW)
  ) uut (
      .clk    (clk),
      .rst_n  (rst_n),
      .araddr (araddr),
      .arvalid(arvalid),
      .arready(arready),
      .rdata  (rdata),
      .rvalid (rvalid),
      .rready (rready),
      .awaddr (awaddr),
      .awvalid(awvalid),
      .awready(awready),
      .wdata  (wdata),
      .wstrb  (wstrb),
      .wvalid (wvalid),
      .wready (wready)
  );

  task automatic test_reset;
    arvalid = 1'b0;
    awvalid = 1'b0;
    wvalid  = 1'b0;
    araddr  = '0;
    awaddr  = '0;
    wdata   = '0;
    wstrb   = '0;
    rready  = 1'b1;

    `TICK(clk);

    `CHECK_TRUE(arready);
    `CHECK_TRUE(awready);
    `CHECK_TRUE(wready);
    `CHECK_FALSE(rvalid);
  endtask

  task automatic test_init_zero;
    araddr  = 32'h0000;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'h0000_0000);

    araddr  = 32'h0004;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'h0000_0000);

    arvalid = 1'b0;
  endtask

  task automatic test_write_read_word;
    awaddr  = 32'h0000;
    awvalid = 1'b1;
    wdata   = 32'hDEAD_BEEF;
    wstrb   = 4'b1111;
    wvalid  = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(awready);
    `CHECK_TRUE(wready);

    awvalid = 1'b0;
    wvalid  = 1'b0;

    araddr  = 32'h0000;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'hDEAD_BEEF);

    arvalid = 1'b0;
  endtask

  task automatic test_one_cycle_read_latency;
    awaddr  = 32'h0008;
    awvalid = 1'b1;
    wdata   = 32'hCAFE_BABE;
    wstrb   = 4'b1111;
    wvalid  = 1'b1;

    `TICK(clk);

    awvalid = 1'b0;
    wvalid  = 1'b0;

    araddr  = 32'h0008;
    arvalid = 1'b1;

    `CHECK_FALSE(rvalid);

    `TICK(clk);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'hCAFE_BABE);

    arvalid = 1'b0;
  endtask

  task automatic test_rvalid_tracks_arvalid;
    araddr  = 32'h0000;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(rvalid);

    arvalid = 1'b0;

    `TICK(clk);
    `CHECK_FALSE(rvalid);

    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(rvalid);

    arvalid = 1'b0;
  endtask

  task automatic test_byte_write_strobes;
    awaddr  = 32'h0010;
    awvalid = 1'b1;
    wdata   = 32'hAA00_0000;
    wstrb   = 4'b1000;
    wvalid  = 1'b1;

    `TICK(clk);

    awaddr = 32'h0010;
    wdata  = 32'h00BB_0000;
    wstrb  = 4'b0100;

    `TICK(clk);

    awaddr = 32'h0010;
    wdata  = 32'h0000_CC00;
    wstrb  = 4'b0010;

    `TICK(clk);

    awaddr = 32'h0010;
    wdata  = 32'h0000_00DD;
    wstrb  = 4'b0001;

    `TICK(clk);

    awvalid = 1'b0;
    wvalid  = 1'b0;

    araddr  = 32'h0010;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'hAABB_CCDD);

    arvalid = 1'b0;
  endtask

  task automatic test_halfword_writes;
    awaddr  = 32'h0020;
    awvalid = 1'b1;
    wdata   = 32'h1234_0000;
    wstrb   = 4'b1100;
    wvalid  = 1'b1;

    `TICK(clk);

    awaddr = 32'h0020;
    wdata  = 32'h0000_5678;
    wstrb  = 4'b0011;

    `TICK(clk);

    awvalid = 1'b0;
    wvalid  = 1'b0;

    araddr  = 32'h0020;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'h1234_5678);

    arvalid = 1'b0;
  endtask

  task automatic test_read_during_write;
    awaddr  = 32'h0030;
    awvalid = 1'b1;
    wdata   = 32'h0000_0001;
    wstrb   = 4'b1111;
    wvalid  = 1'b1;

    `TICK(clk);

    araddr  = 32'h0030;
    arvalid = 1'b1;
    awaddr  = 32'h0030;
    awvalid = 1'b1;
    wdata   = 32'h0000_0002;
    wstrb   = 4'b1111;
    wvalid  = 1'b1;

    `TICK(clk);

    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'h0000_0001);

    awvalid = 1'b0;
    wvalid  = 1'b0;
    arvalid = 1'b0;

    `TICK(clk);

    `CHECK_FALSE(rvalid);
  endtask

  task automatic test_multiple_addresses;
    awaddr  = 32'h0040;
    awvalid = 1'b1;
    wdata   = 32'hAAAA_AAAA;
    wstrb   = 4'b1111;
    wvalid  = 1'b1;

    `TICK(clk);

    awaddr = 32'h0044;
    wdata  = 32'hBBBB_BBBB;

    `TICK(clk);

    awaddr = 32'h0048;
    wdata  = 32'hCCCC_CCCC;

    `TICK(clk);

    awvalid = 1'b0;
    wvalid  = 1'b0;

    araddr  = 32'h0040;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rdata, 32'hAAAA_AAAA);

    araddr = 32'h0044;

    `TICK(clk);
    `CHECK_EQ(rdata, 32'hBBBB_BBBB);

    araddr = 32'h0048;

    `TICK(clk);
    `CHECK_EQ(rdata, 32'hCCCC_CCCC);

    arvalid = 1'b0;
  endtask

  task automatic test_word_addressing;
    awaddr  = 32'h0000;
    awvalid = 1'b1;
    wdata   = 32'h1111_1111;
    wstrb   = 4'b1111;
    wvalid  = 1'b1;

    `TICK(clk);

    awaddr = 32'h0004;
    wdata  = 32'h2222_2222;

    `TICK(clk);

    awvalid = 1'b0;
    wvalid  = 1'b0;

    araddr  = 32'h0001;
    arvalid = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rdata, 32'h1111_1111);

    araddr = 32'h0005;

    `TICK(clk);
    `CHECK_EQ(rdata, 32'h2222_2222);

    arvalid = 1'b0;
  endtask

  task automatic test_rready_backpressure;
    awaddr  = 32'h0050;
    awvalid = 1'b1;
    wdata   = 32'hAAAA_AAAA;
    wstrb   = 4'b1111;
    wvalid  = 1'b1;

    `TICK(clk);

    awvalid = 1'b0;
    wvalid  = 1'b0;

    araddr  = 32'h0050;
    arvalid = 1'b1;
    rready  = 1'b0;

    `TICK(clk);

    `CHECK_FALSE(arready);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'hAAAA_AAAA);

    arvalid = 1'b0;

    `TICK(clk);

    `CHECK_FALSE(arready);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'hAAAA_AAAA);

    `TICK(clk);

    `CHECK_FALSE(arready);
    `CHECK_TRUE(rvalid);
    `CHECK_EQ(rdata, 32'hAAAA_AAAA);

    rready = 1'b1;

    `TICK(clk);

    `CHECK_TRUE(arready);
    `CHECK_FALSE(rvalid);

    rready = 1'b1;
  endtask

  `TEST_SUITE_BEGIN(svc_mem_bram_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_init_zero);
  `TEST_CASE(test_write_read_word);
  `TEST_CASE(test_one_cycle_read_latency);
  `TEST_CASE(test_rvalid_tracks_arvalid);
  `TEST_CASE(test_byte_write_strobes);
  `TEST_CASE(test_halfword_writes);
  `TEST_CASE(test_read_during_write);
  `TEST_CASE(test_multiple_addresses);
  `TEST_CASE(test_word_addressing);
  `TEST_CASE(test_rready_backpressure);
  `TEST_SUITE_END();

endmodule
