`include "svc_unit.sv"
`include "svc_divu.sv"

module svc_divu_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic        en;
  logic        busy;
  logic        valid;
  logic        div_zero;
  logic [31:0] dividend;
  logic [31:0] divisor;
  logic [31:0] quotient;
  logic [31:0] remainder;

  svc_divu #(
      .WIDTH(32)
  ) uut (
      .clk      (clk),
      .rst_n    (rst_n),
      .en       (en),
      .dividend (dividend),
      .divisor  (divisor),
      .busy     (busy),
      .valid    (valid),
      .div_zero (div_zero),
      .quotient (quotient),
      .remainder(remainder)
  );

  //
  // Reset inputs on reset
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      en       <= 1'b0;
      dividend <= '0;
      divisor  <= '0;
    end
  end

  //
  // Helper task to perform division
  //
  task automatic test_div(input logic [31:0] a, input logic [31:0] b,
                          input logic [31:0] expected_quo,
                          input logic [31:0] expected_rem);
    @(posedge clk);
    dividend = a;
    divisor  = b;
    en       = 1;
    @(posedge clk);
    en = 0;

    `CHECK_WAIT_FOR(clk, valid, 40);
    `CHECK_TRUE(valid);
    `CHECK_FALSE(busy);
    `CHECK_FALSE(div_zero);
    `CHECK_EQ(quotient, expected_quo);
    `CHECK_EQ(remainder, expected_rem);
  endtask

  //
  // Reset test
  //
  task automatic test_reset();
    @(posedge clk);
    `CHECK_FALSE(busy);
    `CHECK_FALSE(valid);
    `CHECK_FALSE(div_zero);
  endtask

  //
  // Helper task to test divide by zero
  //
  task automatic test_div_by_zero(input logic [31:0] a);
    @(posedge clk);
    dividend = a;
    divisor  = 0;
    en       = 1;
    @(posedge clk);
    en = 0;
    @(posedge clk);

    `CHECK_FALSE(busy);
    `CHECK_TRUE(div_zero);
    `CHECK_FALSE(valid);
  endtask

  //
  // Basic division tests
  //
  task automatic test_basic();
    test_div(32'd42, 32'd7, 32'd6, 32'd0);
  endtask

  task automatic test_with_remainder();
    test_div(32'd10, 32'd3, 32'd3, 32'd1);
  endtask

  task automatic test_dividend_smaller();
    test_div(32'd5, 32'd10, 32'd0, 32'd5);
  endtask

  task automatic test_divide_by_one();
    test_div(32'd42, 32'd1, 32'd42, 32'd0);
  endtask

  task automatic test_divide_by_self();
    test_div(32'd42, 32'd42, 32'd1, 32'd0);
  endtask

  task automatic test_zero_dividend();
    test_div(32'd0, 32'd7, 32'd0, 32'd0);
  endtask

  //
  // Large number tests
  //
  task automatic test_large();
    test_div(32'hFFFFFFFF, 32'd2, 32'h7FFFFFFF, 32'd1);
  endtask

  task automatic test_large_divisor();
    test_div(32'hFFFFFFFF, 32'hFFFFFFFF, 32'd1, 32'd0);
  endtask

  //
  // Edge cases
  //
  task automatic test_power_of_two();
    test_div(32'd256, 32'd16, 32'd16, 32'd0);
  endtask

  task automatic test_max_remainder();
    test_div(32'd100, 32'd7, 32'd14, 32'd2);
  endtask

  //
  // Divide by zero test
  //
  task automatic test_dbz();
    test_div_by_zero(32'd42);
  endtask

  //
  // Cycle count test
  //
  task automatic test_cycle_count();
    int cycle_count;
    @(posedge clk);
    dividend = 32'd100;
    divisor  = 32'd7;
    en       = 1;
    @(posedge clk);
    en          = 0;

    cycle_count = 0;
    while (!valid) begin
      @(posedge clk);
      cycle_count++;
    end

    `CHECK_EQ(cycle_count, 33);
    `CHECK_EQ(quotient, 32'd14);
    `CHECK_EQ(remainder, 32'd2);
  endtask

  `TEST_SUITE_BEGIN(svc_divu_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic);
  `TEST_CASE(test_with_remainder);
  `TEST_CASE(test_dividend_smaller);
  `TEST_CASE(test_divide_by_one);
  `TEST_CASE(test_divide_by_self);
  `TEST_CASE(test_zero_dividend);
  `TEST_CASE(test_large);
  `TEST_CASE(test_large_divisor);
  `TEST_CASE(test_power_of_two);
  `TEST_CASE(test_max_remainder);
  `TEST_CASE(test_dbz);
  `TEST_CASE(test_cycle_count);
  `TEST_SUITE_END();
endmodule
