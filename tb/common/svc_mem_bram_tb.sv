`include "svc_unit.sv"

`include "svc_mem_bram.sv"

module svc_mem_bram_tb;
  localparam int DW = 32;
  localparam int DEPTH = 1024;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic        rd_en;
  logic [31:0] rd_addr;
  logic [31:0] rd_data;

  logic        wr_en;
  logic [31:0] wr_addr;
  logic [31:0] wr_data;
  logic [ 3:0] wr_strb;

  svc_mem_bram #(
      .DW   (DW),
      .DEPTH(DEPTH)
  ) uut (
      .clk    (clk),
      .rst_n  (rst_n),
      .rd_en  (rd_en),
      .rd_addr(rd_addr),
      .rd_data(rd_data),
      .wr_en  (wr_en),
      .wr_addr(wr_addr),
      .wr_data(wr_data),
      .wr_strb(wr_strb)
  );

  task automatic test_reset;
    rd_en   = 1'b1;
    wr_en   = 1'b0;
    rd_addr = '0;
    wr_addr = '0;
    wr_data = '0;
    wr_strb = '0;

    `TICK(clk);
  endtask

  task automatic test_init_zero;
    rd_addr = 32'h0000;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h0000_0000);

    rd_addr = 32'h0004;

    `TICK(clk);
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

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hDEAD_BEEF);
  endtask

  task automatic test_one_cycle_read_latency;
    wr_addr = 32'h0008;
    wr_data = 32'hCAFE_BABE;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0008;

    `TICK(clk);
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

    `TICK(clk);
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

    `TICK(clk);
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

    `TICK(clk);

    wr_en = 1'b0;

    `CHECK_EQ(rd_data, 32'h0000_0001);

    `TICK(clk);

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

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hAAAA_AAAA);

    rd_addr = 32'h0044;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hBBBB_BBBB);

    rd_addr = 32'h0048;

    `TICK(clk);
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

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h1111_1111);

    rd_addr = 32'h0005;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h2222_2222);
  endtask

  task automatic test_rd_en_holds_data;
    wr_addr = 32'h0050;
    wr_data = 32'hFEED_FACE;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_addr = 32'h0054;
    wr_data = 32'h1234_5678;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0050;
    rd_en   = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hFEED_FACE);

    rd_addr = 32'h0054;
    rd_en   = 1'b0;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hFEED_FACE);

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hFEED_FACE);

    rd_en = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h1234_5678);
  endtask

  task automatic test_rd_en_with_changing_address;
    wr_addr = 32'h0060;
    wr_data = 32'hAAAA_AAAA;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_addr = 32'h0064;
    wr_data = 32'hBBBB_BBBB;

    `TICK(clk);

    wr_addr = 32'h0068;
    wr_data = 32'hCCCC_CCCC;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0060;
    rd_en   = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hAAAA_AAAA);

    rd_addr = 32'h0064;
    rd_en   = 1'b0;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hAAAA_AAAA);

    rd_addr = 32'h0068;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hAAAA_AAAA);

    rd_en = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'hCCCC_CCCC);
  endtask

  task automatic test_rd_en_back_to_back_reads;
    wr_addr = 32'h0070;
    wr_data = 32'h1111_1111;
    wr_strb = 4'b1111;
    wr_en   = 1'b1;

    `TICK(clk);

    wr_addr = 32'h0074;
    wr_data = 32'h2222_2222;

    `TICK(clk);

    wr_addr = 32'h0078;
    wr_data = 32'h3333_3333;

    `TICK(clk);

    wr_addr = 32'h007C;
    wr_data = 32'h4444_4444;

    `TICK(clk);

    wr_en   = 1'b0;

    rd_addr = 32'h0070;
    rd_en   = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h1111_1111);

    rd_addr = 32'h0074;
    rd_en   = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h2222_2222);

    rd_addr = 32'h0078;
    rd_en   = 1'b0;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h2222_2222);

    rd_addr = 32'h007C;
    rd_en   = 1'b1;

    `TICK(clk);
    `CHECK_EQ(rd_data, 32'h4444_4444);
  endtask

  task automatic test_reset_value;
    rd_en   = 1'b1;
    rd_addr = 32'h0000;

    `CHECK_EQ(rd_data, 32'h00000000);
  endtask

  `TEST_SUITE_BEGIN(svc_mem_bram_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_reset_value);
  `TEST_CASE(test_init_zero);
  `TEST_CASE(test_write_read_word);
  `TEST_CASE(test_one_cycle_read_latency);
  `TEST_CASE(test_byte_write_strobes);
  `TEST_CASE(test_halfword_writes);
  `TEST_CASE(test_read_during_write);
  `TEST_CASE(test_multiple_addresses);
  `TEST_CASE(test_word_addressing);
  `TEST_CASE(test_rd_en_holds_data);
  `TEST_CASE(test_rd_en_with_changing_address);
  `TEST_CASE(test_rd_en_back_to_back_reads);
  `TEST_SUITE_END();

endmodule
