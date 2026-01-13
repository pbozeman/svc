`include "svc_unit.sv"
`include "svc_accumulator.sv"

module svc_accumulator_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam WIDTH = 8;
  localparam BITS_PER_STAGE = 4;
  localparam STAGES = WIDTH / BITS_PER_STAGE;

  logic             clr;
  logic             en;
  logic [WIDTH-1:0] val;
  logic [WIDTH-1:0] acc;

  svc_accumulator #(
      .WIDTH         (WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) uut (
      .clk(clk),
      .clr(clr),
      .en (en),
      .val(val),
      .acc(acc)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      clr <= 1'b1;
      en  <= 1'b0;
      val <= '0;
    end
  end

  task automatic test_basic_accumulation();
    logic [WIDTH-1:0] expected;

    // Initialize
    expected = '0;
    clr      = 1'b0;
    en       = 1'b0;
    val      = '0;

    // Add value 5
    val      = 8'h05;
    en       = 1'b1;
    `TICK(clk);
    en = 1'b0;

    // Wait for pipeline delay (STAGES + 1 cycles)
    repeat (STAGES + 1) `TICK(clk);
    expected = 8'h05;
    `CHECK_EQ(acc, expected);

    // Add value 3
    val = 8'h03;
    en  = 1'b1;
    `TICK(clk);
    en = 1'b0;

    // Wait for pipeline delay
    repeat (STAGES + 1) `TICK(clk);
    expected = 8'h08;  // 5 + 3 = 8
    `CHECK_EQ(acc, expected);

    // Add value 10
    val = 8'h0A;
    en  = 1'b1;
    `TICK(clk);
    en = 1'b0;

    // Wait for pipeline delay
    repeat (STAGES + 1) `TICK(clk);
    expected = 8'h12;  // 8 + 10 = 18 (0x12)
    `CHECK_EQ(acc, expected);
  endtask

  // Test accumulation with multiple consecutive inputs
  task automatic test_consecutive_inputs();
    logic [WIDTH-1:0] expected;

    // Clear accumulator
    clr = 1'b1;
    `TICK(clk);
    clr = 1'b0;

    // Ensure accumulator is reset
    `CHECK_EQ(acc, '0);

    // Send consecutive inputs
    expected = '0;

    // Add 1, 2, 3, 4, 5 valsequence
    for (int i = 1; i <= 5; i++) begin
      val = 8'(i);
      en  = 1'b1;
      `TICK(clk);
      expected = expected + 8'(i);
    end

    // Disable input
    en = 1'b0;

    // Wait for pipeline delay
    repeat (STAGES + 1) `TICK(clk);

    // Check result: 1 + 2 + 3 + 4 + 5 = 15
    `CHECK_EQ(acc, 8'h0F);
  endtask

  // Test overflow behavior
  task automatic test_overflow();
    // Clear accumulator
    clr = 1'b1;
    `TICK(clk);
    clr = 1'b0;

    // Add maximum value
    val = '1;  // All 1s (0xFF for 8-bit)
    en  = 1'b1;
    `TICK(clk);
    en = 1'b0;

    // Wait for pipeline delay
    repeat (STAGES + 1) `TICK(clk);
    `CHECK_EQ(acc, '1);

    // Add 1 more to cause overflow
    val = 8'h01;
    en  = 1'b1;
    `TICK(clk);
    en = 1'b0;

    // Wait for pipeline delay
    repeat (STAGES + 1) `TICK(clk);
    `CHECK_EQ(acc, 8'h00);
  endtask

  // Test clear behavior during accumulation
  task automatic test_clear_during_accumulation();
    // Start accumulation
    val = 8'h05;
    en  = 1'b1;
    `TICK(clk);

    val = 8'h03;
    `TICK(clk);

    // Clear during accumulation
    clr = 1'b1;
    `TICK(clk);
    clr = 1'b0;
    en  = 1'b0;

    // Wait for pipeline delay
    repeat (STAGES + 1) `TICK(clk);

    // Check if accumulator was cleared
    `CHECK_EQ(acc, '0);

    // Start new accumulation
    val = 8'h07;
    en  = 1'b1;
    `TICK(clk);
    en = 1'b0;

    // Wait for pipeline delay
    repeat (STAGES + 1) `TICK(clk);
    `CHECK_EQ(acc, 8'h07);
  endtask

  // Test suite definition
  `TEST_SUITE_BEGIN(svc_accumulator_tbi);
  `TEST_CASE(test_basic_accumulation);
  `TEST_CASE(test_consecutive_inputs);
  `TEST_CASE(test_overflow);
  `TEST_CASE(test_clear_during_accumulation);
  `TEST_SUITE_END();
endmodule
