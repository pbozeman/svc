`include "svc_unit.sv"
`include "svc_rv_ext_zmmul.sv"

module svc_rv_ext_zmmul_mul_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic        en;
  logic [31:0] rs1;
  logic [31:0] rs2;
  logic [ 2:0] op;
  logic        busy;
  logic [31:0] result;
  logic        result_valid;

  svc_rv_ext_zmmul dut (.*);

  //
  // Initialize inputs
  //
  initial begin
    en  = 1'b0;
    rs1 = 32'h0;
    rs2 = 32'h0;
    op  = 3'b000;
  end

  //
  // Test reset state
  //
  task automatic test_reset;
    en = 1'b0;
    `TICK(clk);
    `CHECK_EQ(busy, 1'b0);
    `CHECK_EQ(result_valid, 1'b0);
  endtask

  //
  // Test MUL (lower 32 bits)
  //
  task automatic test_mul_positive;
    en  = 1'b1;
    rs1 = 32'd7;
    rs2 = 32'd6;
    op  = 3'b000;
    `TICK(clk);
    `CHECK_EQ(result, 32'd42);
    `CHECK_EQ(result_valid, 1'b1);
    `CHECK_EQ(busy, 1'b0);

    en = 1'b0;
    `TICK(clk);
    `CHECK_EQ(result_valid, 1'b0);
  endtask

  task automatic test_mul_negative;
    en  = 1'b1;
    rs1 = -32'sd7;
    rs2 = 32'sd6;
    op  = 3'b000;
    `TICK(clk);
    `CHECK_EQ($signed(result), -32'sd42);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  task automatic test_mul_overflow;
    en  = 1'b1;
    rs1 = 32'h8000_0000;
    rs2 = 32'h0000_0002;
    op  = 3'b000;
    `TICK(clk);
    `CHECK_EQ(result, 32'h0000_0000);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  //
  // Test MULH (upper 32 bits, signed × signed)
  //
  task automatic test_mulh_positive;
    en  = 1'b1;
    rs1 = 32'h8000_0000;
    rs2 = 32'h0000_0002;
    op  = 3'b001;
    `TICK(clk);
    `CHECK_EQ($signed(result), -32'sd1);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  task automatic test_mulh_large;
    en  = 1'b1;
    rs1 = 32'h7FFF_FFFF;
    rs2 = 32'h7FFF_FFFF;
    op  = 3'b001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h3FFF_FFFF);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  //
  // Test MULHSU (upper 32 bits, signed × unsigned)
  //
  task automatic test_mulhsu_positive_unsigned;
    en  = 1'b1;
    rs1 = 32'sd100;
    rs2 = 32'hFFFF_FFFF;
    op  = 3'b010;
    `TICK(clk);
    `CHECK_EQ(result, 32'd99);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  task automatic test_mulhsu_negative_unsigned;
    en  = 1'b1;
    rs1 = -32'sd100;
    rs2 = 32'hFFFF_FFFF;
    op  = 3'b010;
    `TICK(clk);
    `CHECK_EQ($signed(result), -32'sd100);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  //
  // Test MULHU (upper 32 bits, unsigned × unsigned)
  //
  task automatic test_mulhu_large;
    en  = 1'b1;
    rs1 = 32'hFFFF_FFFF;
    rs2 = 32'hFFFF_FFFF;
    op  = 3'b011;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFF_FFFE);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  task automatic test_mulhu_half_max;
    en  = 1'b1;
    rs1 = 32'h8000_0000;
    rs2 = 32'h8000_0000;
    op  = 3'b011;
    `TICK(clk);
    `CHECK_EQ(result, 32'h4000_0000);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  //
  // Test multiply by zero
  //
  task automatic test_mul_by_zero;
    en  = 1'b1;
    rs1 = 32'hFFFF_FFFF;
    rs2 = 32'h0000_0000;
    op  = 3'b000;
    `TICK(clk);
    `CHECK_EQ(result, 32'h0000_0000);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  //
  // Test multiply by one
  //
  task automatic test_mul_by_one;
    en  = 1'b1;
    rs1 = 32'hDEAD_BEEF;
    rs2 = 32'h0000_0001;
    op  = 3'b000;
    `TICK(clk);
    `CHECK_EQ(result, 32'hDEAD_BEEF);
    `CHECK_EQ(result_valid, 1'b1);
  endtask

  //
  // Test that result_valid follows en
  //
  task automatic test_valid_timing;
    en  = 1'b0;
    rs1 = 32'd10;
    rs2 = 32'd20;
    op  = 3'b000;
    `TICK(clk);
    `CHECK_EQ(result_valid, 1'b0);

    en = 1'b1;
    `TICK(clk);
    `CHECK_EQ(result_valid, 1'b1);
    `CHECK_EQ(result, 32'd200);

    en = 1'b0;
    `TICK(clk);
    `CHECK_EQ(result_valid, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_ext_zmmul_mul_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_mul_positive);
  `TEST_CASE(test_mul_negative);
  `TEST_CASE(test_mul_overflow);
  `TEST_CASE(test_mulh_positive);
  `TEST_CASE(test_mulh_large);
  `TEST_CASE(test_mulhsu_positive_unsigned);
  `TEST_CASE(test_mulhsu_negative_unsigned);
  `TEST_CASE(test_mulhu_large);
  `TEST_CASE(test_mulhu_half_max);
  `TEST_CASE(test_mul_by_zero);
  `TEST_CASE(test_mul_by_one);
  `TEST_CASE(test_valid_timing);
  `TEST_SUITE_END();
endmodule
