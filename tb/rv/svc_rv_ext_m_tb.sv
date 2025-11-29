`ifndef SVC_RV_EXT_M_TB_SV
`define SVC_RV_EXT_M_TB_SV

`include "svc_unit.sv"
`include "svc_rv_ext_mul_ex.sv"
`include "svc_rv_ext_div.sv"
`include "svc_rv_ext_mul_mem.sv"
`include "svc_rv_ext_mul_wb.sv"

// verilator lint_off UNUSEDSIGNAL

module svc_rv_ext_m_tb;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic        en;
  logic [31:0] rs1;
  logic [31:0] rs2;
  logic [ 2:0] op;
  logic        busy;
  logic [31:0] div_result;
  logic [31:0] mul_ll;
  logic [31:0] mul_lh;
  logic [31:0] mul_hl;
  logic [31:0] mul_hh;
  logic [63:0] product_64;
  logic [31:0] mul_result;
  logic [31:0] result;

  //
  // EX stage: Multiply unit (combinational partial products)
  //
  svc_rv_ext_mul_ex dut_mul (
      .rs1   (rs1),
      .rs2   (rs2),
      .op    (op),
      .mul_ll(mul_ll),
      .mul_lh(mul_lh),
      .mul_hl(mul_hl),
      .mul_hh(mul_hh)
  );

  //
  // EX stage: Division unit (multi-cycle)
  //
  // Only enable for division operations (op[2] = 1)
  //
  logic div_en;

  assign div_en = en && op[2];

  svc_rv_ext_div dut_div (
      .clk   (clk),
      .rst_n (rst_n),
      .en    (div_en),
      .rs1   (rs1),
      .rs2   (rs2),
      .op    (op),
      .busy  (busy),
      .result(div_result)
  );

  //
  // MEM stage: combine partial products (unsigned)
  //
  svc_rv_ext_mul_mem dut_mem (
      .mul_ll    (mul_ll),
      .mul_lh    (mul_lh),
      .mul_hl    (mul_hl),
      .mul_hh    (mul_hh),
      .div_result(div_result),
      .product_64(product_64)
  );

  //
  // WB stage: apply sign correction to multiply result
  //
  svc_rv_ext_mul_wb dut_wb (
      .product_64(product_64),
      .rs1_data  (rs1),
      .rs2_data  (rs2),
      .op        (op),
      .result    (mul_result)
  );

  //
  // Result selection: multiply or division
  //
  assign result = op[2] ? div_result : mul_result;

  //
  // Test helper for multiplication (1 cycle)
  //
  task automatic test_mul(input logic [31:0] a, input logic [31:0] b,
                          input logic [2:0] operation,
                          input logic [31:0] expected);
    rs1 = a;
    rs2 = b;
    op  = operation;
    en  = 1'b1;
    `TICK(clk);
    `CHECK_EQ(result, expected);
    en = 1'b0;
  endtask

  //
  // Test helper for division (32+ cycles)
  //
  task automatic test_div(input logic [31:0] a, input logic [31:0] b,
                          input logic [2:0] operation,
                          input logic [31:0] expected);
    rs1 = a;
    rs2 = b;
    op  = operation;
    en  = 1'b1;
    `TICK(clk);
    en = 1'b0;

    `CHECK_WAIT_FOR(clk, !busy, 40);
    `CHECK_EQ(result, expected);

    `TICK(clk);
  endtask

  //
  // MUL tests
  //
  task automatic test_mul_basic();
    logic [31:0] a;
    logic [31:0] b;
    logic [63:0] product_full;

    //
    // Basic MUL (lower 32 bits)
    //
    test_mul(32'd5, 32'd3, 3'b000, 32'd15);
    test_mul(32'd100, 32'd200, 3'b000, 32'd20000);

    //
    // MUL with negative numbers
    //
    test_mul(-32'sd5, 32'sd3, 3'b000, -32'sd15);
    test_mul(-32'sd5, -32'sd3, 3'b000, 32'sd15);

    //
    // MUL overflow (lower bits)
    //
    a            = 32'h80000000;
    b            = 32'h00000002;
    product_full = 64'h0000000100000000;
    test_mul(a, b, 3'b000, product_full[31:0]);
  endtask

  //
  // MULH tests
  //
  task automatic test_mulh();
    logic        [31:0] a;
    logic        [31:0] b;
    logic signed [63:0] product_full;

    //
    // MULH (upper 32 bits, signed × signed)
    //
    a            = 32'h80000000;
    b            = 32'h00000002;
    product_full = $signed(a) * $signed(b);
    test_mul(a, b, 3'b001, product_full[63:32]);

    a            = 32'h7FFFFFFF;
    b            = 32'h00000002;
    product_full = $signed(a) * $signed(b);
    test_mul(a, b, 3'b001, product_full[63:32]);

    //
    // Negative × negative
    //
    a            = -32'sd1000;
    b            = -32'sd2000;
    product_full = $signed(a) * $signed(b);
    test_mul(a, b, 3'b001, product_full[63:32]);
  endtask

  //
  // MULHSU tests
  //
  task automatic test_mulhsu();
    logic signed [31:0] a;
    logic        [31:0] b;
    logic signed [63:0] product_full;

    //
    // MULHSU (upper 32 bits, signed × unsigned)
    //
    a            = -32'sd1;
    b            = 32'hFFFFFFFF;
    product_full = $signed({a[31], a}) * $signed({1'b0, b});
    test_mul(a, b, 3'b010, product_full[63:32]);

    a            = 32'sd1000;
    b            = 32'd2000;
    product_full = $signed({a[31], a}) * $signed({1'b0, b});
    test_mul(a, b, 3'b010, product_full[63:32]);
  endtask

  //
  // MULHU tests
  //
  task automatic test_mulhu();
    logic [31:0] a;
    logic [31:0] b;
    logic [63:0] product_full;

    //
    // MULHU (upper 32 bits, unsigned × unsigned)
    //
    a            = 32'hFFFFFFFF;
    b            = 32'hFFFFFFFF;
    product_full = a * b;
    test_mul(a, b, 3'b011, product_full[63:32]);

    a            = 32'h80000000;
    b            = 32'h00000002;
    product_full = a * b;
    test_mul(a, b, 3'b011, product_full[63:32]);
  endtask

  //
  // DIVU tests
  //
  task automatic test_divu();
    //
    // Basic unsigned division
    //
    test_div(32'd100, 32'd10, 3'b101, 32'd10);
    test_div(32'd15, 32'd3, 3'b101, 32'd5);
    test_div(32'd7, 32'd2, 3'b101, 32'd3);

    //
    // Division with remainder
    //
    test_div(32'd10, 32'd3, 3'b101, 32'd3);

    //
    // Division by zero (should return all 1s)
    //
    test_div(32'd100, 32'd0, 3'b101, 32'hFFFFFFFF);
  endtask

  //
  // DIV tests
  //
  task automatic test_div_signed();
    //
    // Basic signed division
    //
    test_div(32'sd100, 32'sd10, 3'b100, 32'sd10);
    test_div(-32'sd100, 32'sd10, 3'b100, -32'sd10);
    test_div(32'sd100, -32'sd10, 3'b100, -32'sd10);
    test_div(-32'sd100, -32'sd10, 3'b100, 32'sd10);

    //
    // Division with remainder
    //
    test_div(32'sd10, 32'sd3, 3'b100, 32'sd3);
    test_div(-32'sd10, 32'sd3, 3'b100, -32'sd3);

    //
    // Division by zero (should return all 1s)
    //
    test_div(32'sd100, 32'sd0, 3'b100, 32'hFFFFFFFF);
  endtask

  //
  // REMU tests
  //
  task automatic test_remu();
    //
    // Basic unsigned remainder
    //
    test_div(32'd100, 32'd10, 3'b111, 32'd0);
    test_div(32'd15, 32'd4, 3'b111, 32'd3);
    test_div(32'd10, 32'd3, 3'b111, 32'd1);

    //
    // Remainder by zero (should return dividend)
    //
    test_div(32'd100, 32'd0, 3'b111, 32'd100);
  endtask

  //
  // REM tests
  //
  task automatic test_rem();
    //
    // Basic signed remainder
    //
    test_div(32'sd100, 32'sd10, 3'b110, 32'sd0);
    test_div(32'sd10, 32'sd3, 3'b110, 32'sd1);
    test_div(-32'sd10, 32'sd3, 3'b110, -32'sd1);
    test_div(32'sd10, -32'sd3, 3'b110, 32'sd1);
    test_div(-32'sd10, -32'sd3, 3'b110, -32'sd1);

    //
    // Remainder by zero (should return dividend)
    //
    test_div(32'sd100, 32'sd0, 3'b110, 32'sd100);
    test_div(-32'sd100, 32'sd0, 3'b110, -32'sd100);
  endtask

  //
  // Back-to-back multiplication tests
  //
  task automatic test_back_to_back_mul();
    //
    // Multiple MUL operations in consecutive cycles
    //
    test_mul(32'd5, 32'd3, 3'b000, 32'd15);
    test_mul(32'd7, 32'd2, 3'b000, 32'd14);
    test_mul(32'd10, 32'd10, 3'b000, 32'd100);
  endtask

  //
  // Division busy signal test
  //
  task automatic test_div_busy();
    int i;

    rs1 = 32'd100;
    rs2 = 32'd10;
    op  = 3'b101;
    en  = 1'b1;
    `TICK(clk);
    en = 1'b0;

    //
    // Should be busy during division
    //
    for (i = 0; i < 5; i = i + 1) begin
      `TICK(clk);
    end
    `CHECK_TRUE(busy);

    //
    // Wait for completion
    //
    `CHECK_WAIT_FOR(clk, !busy, 35);
    `CHECK_EQ(result, 32'd10);

    `TICK(clk);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_ext_m_tb);
  `TEST_CASE(test_mul_basic);
  `TEST_CASE(test_mulh);
  `TEST_CASE(test_mulhsu);
  `TEST_CASE(test_mulhu);
  `TEST_CASE(test_divu);
  `TEST_CASE(test_div_signed);
  `TEST_CASE(test_remu);
  `TEST_CASE(test_rem);
  `TEST_CASE(test_back_to_back_mul);
  `TEST_CASE(test_div_busy);
  `TEST_SUITE_END();

endmodule

`endif
