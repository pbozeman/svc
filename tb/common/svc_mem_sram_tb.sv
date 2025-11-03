`include "svc_unit.sv"

`include "svc_mem_sram.sv"

module svc_mem_sram_tb;
  localparam DW = 32;
  localparam AW = 10;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [31:0] rd_addr;
  logic [31:0] rd_data;

  logic [31:0] wr_addr;
  logic [31:0] wr_data;
  logic [ 3:0] wr_strb;
  logic        wr_en;

  svc_mem_sram #(
      .DW(DW),
      .AW(AW)
  ) uut (
      .clk    (clk),
      .rst_n  (rst_n),
      .rd_addr(rd_addr),
      .rd_data(rd_data),
      .wr_addr(wr_addr),
      .wr_data(wr_data),
      .wr_strb(wr_strb),
      .wr_en  (wr_en)
  );

  task automatic test_reset;
    wr_en   = 1'b0;
    rd_addr = '0;
    wr_addr = '0;
    wr_data = '0;
    wr_strb = '0;

    `TICK(clk);
  endtask

  task automatic test_init_zero;
    rd_addr = 32'h0000;

    `CHECK_EQ(rd_data, 32'h0000_0000);

    rd_addr = 32'h0004;

    `CHECK_EQ(rd_data, 32'h0000_0000);
  endtask

  task automatic test_write_read_word;
    wr_addr = 32'h0000;
    wr_data = 32'hDEAD_BEEF;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0000;

    `CHECK_EQ(rd_data, 32'hDEAD_BEEF);
  endtask

  task automatic test_zero_cycle_read_latency;
    wr_addr = 32'h0008;
    wr_data = 32'hCAFE_BABE;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0008;

    `CHECK_EQ(rd_data, 32'hCAFE_BABE);
  endtask

  task automatic test_byte_write_strobes;
    wr_addr = 32'h0010;
    wr_data = 32'hAA00_0000;
    wr_strb = 4'b1000;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_addr = 32'h0010;
    wr_data = 32'h00BB_0000;
    wr_strb = 4'b0100;

    `TICK(clk);

    wr_addr = 32'h0010;
    wr_data = 32'h0000_CC00;
    wr_strb = 4'b0010;

    `TICK(clk);

    wr_addr = 32'h0010;
    wr_data = 32'h0000_00DD;
    wr_strb = 4'b0001;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0010;

    `CHECK_EQ(rd_data, 32'hAABB_CCDD);
  endtask

  task automatic test_halfword_writes;
    wr_addr = 32'h0020;
    wr_data = 32'h1234_0000;
    wr_strb = 4'b1100;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_addr = 32'h0020;
    wr_data = 32'h0000_5678;
    wr_strb = 4'b0011;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0020;

    `CHECK_EQ(rd_data, 32'h1234_5678);
  endtask

  task automatic test_read_during_write;
    wr_addr = 32'h0030;
    wr_data = 32'h0000_0001;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    rd_addr = 32'h0030;
    wr_addr = 32'h0030;
    wr_data = 32'h0000_0002;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `CHECK_EQ(rd_data, 32'h0000_0001);

    `TICK(clk);

    wr_en = 1'b0;

    `CHECK_EQ(rd_data, 32'h0000_0002);
  endtask

  task automatic test_multiple_addresses;
    wr_addr = 32'h0040;
    wr_data = 32'hAAAA_AAAA;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_addr = 32'h0044;
    wr_data = 32'hBBBB_BBBB;

    `TICK(clk);

    wr_addr = 32'h0048;
    wr_data = 32'hCCCC_CCCC;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0040;

    `CHECK_EQ(rd_data, 32'hAAAA_AAAA);

    rd_addr = 32'h0044;

    `CHECK_EQ(rd_data, 32'hBBBB_BBBB);

    rd_addr = 32'h0048;

    `CHECK_EQ(rd_data, 32'hCCCC_CCCC);
  endtask

  task automatic test_word_addressing;
    wr_addr = 32'h0000;
    wr_data = 32'h1111_1111;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_addr = 32'h0004;
    wr_data = 32'h2222_2222;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0001;

    `CHECK_EQ(rd_data, 32'h1111_1111);

    rd_addr = 32'h0005;

    `CHECK_EQ(rd_data, 32'h2222_2222);
  endtask

  `TEST_SUITE_BEGIN(svc_mem_sram_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_init_zero);
  `TEST_CASE(test_write_read_word);
  `TEST_CASE(test_zero_cycle_read_latency);
  `TEST_CASE(test_byte_write_strobes);
  `TEST_CASE(test_halfword_writes);
  `TEST_CASE(test_read_during_write);
  `TEST_CASE(test_multiple_addresses);
  `TEST_CASE(test_word_addressing);
  `TEST_SUITE_END();

endmodule
