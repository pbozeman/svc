`include "svc_unit.sv"
`include "svc_stats_max.sv"

module svc_stats_max_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic       clr;
  logic       en;
  logic [7:0] val;
  logic [7:0] max;

  // Module with no pipeline stages
  svc_stats_max #(
      .WIDTH         (8),
      .BITS_PER_STAGE(8)
  ) uut_direct (
      .clk(clk),
      .clr(clr),
      .en (en),
      .val(val),
      .max(max)
  );

  // Pipeline-specific signals
  logic [7:0] max_pipe;

  // Module with pipeline stages
  svc_stats_max #(
      .WIDTH         (8),
      .BITS_PER_STAGE(4)
  ) uut_pipe (
      .clk(clk),
      .clr(clr),
      .en (en),
      .val(val),
      .max(max_pipe)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      clr <= 1'b1;
      en  <= 1'b0;
      val <= 8'h00;
    end
  end

  task automatic test_reset();
    // rst was removed from the module, but in the tb we raise clr
    `CHECK_EQ(max, 8'h00);
    `CHECK_EQ(max_pipe, 8'h00);
  endtask

  // Test direct comparison (STAGES=0)
  task automatic test_direct_update();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h42;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(max, 8'h42);

    // Test larger value
    en  = 1'b1;
    val = 8'h64;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(max, 8'h64);

    // Test smaller value (should not update max)
    en  = 1'b1;
    val = 8'h32;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(max, 8'h64);

    // Test maximum possible value
    en  = 1'b1;
    val = 8'hFF;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(max, 8'hFF);
  endtask

  // Test pipelined implementation (STAGES>0)
  task automatic test_pipeline_update();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h10;
    `TICK(clk);
    en = 1'b0;

    // Need to wait for pipeline to propagate (2 stages + 1 cycle for final comparison)
    repeat (3) `TICK(clk);
    `CHECK_EQ(max_pipe, 8'h10);

    // Test with new larger value
    en  = 1'b1;
    val = 8'hA5;
    `TICK(clk);
    en = 1'b0;

    // Wait for pipeline
    repeat (3) `TICK(clk);
    `CHECK_EQ(max_pipe, 8'hA5);

    // Test with smaller value (max should not change)
    en  = 1'b1;
    val = 8'h20;
    `TICK(clk);
    en = 1'b0;

    repeat (3) `TICK(clk);
    `CHECK_EQ(max_pipe, 8'hA5);
  endtask

  // Test clear functionality
  task automatic test_clear();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h7F;
    `TICK(clk);
    en = 1'b0;

    // For pipelined version, wait for propagation
    repeat (3) `TICK(clk);

    // Verify max values
    `CHECK_EQ(max, 8'h7F);
    `CHECK_EQ(max_pipe, 8'h7F);

    // Clear the max value
    clr = 1'b1;
    `TICK(clk);
    clr = 1'b0;

    // Verify values are reset
    `CHECK_EQ(max, 8'h00);
    `CHECK_EQ(max_pipe, 8'h00);
  endtask

  // Test rapid updates with enable toggling
  task automatic test_enable_behavior();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h30;
    `TICK(clk);

    // Update with enable high
    val = 8'h40;
    `TICK(clk);

    // Update with enable low (should not update max)
    en  = 1'b0;
    val = 8'hFF;
    `TICK(clk);

    // Check direct implementation
    `CHECK_EQ(max, 8'h40);

    // For pipeline, wait for propagation and check
    repeat (3) `TICK(clk);
    `CHECK_EQ(max_pipe, 8'h40);
  endtask

  // Test continuous updates
  task automatic test_continuous_updates();
    // Create sequence of increasing and decreasing values
    logic [7:0] test_values[10];

    test_values[0] = 8'h10;
    test_values[1] = 8'h20;
    test_values[2] = 8'h15;
    test_values[3] = 8'h25;
    test_values[4] = 8'h30;
    test_values[5] = 8'h28;
    test_values[6] = 8'h40;
    test_values[7] = 8'h35;
    test_values[8] = 8'h50;
    test_values[9] = 8'h45;

    // Send values one by one
    clr            = 1'b0;
    for (int i = 0; i < 10; i++) begin
      en  = 1'b1;
      val = test_values[i];
      `TICK(clk);
    end

    en = 1'b0;

    // Direct max should be updated immediately
    `CHECK_EQ(max, 8'h50);

    // For pipeline, wait for all stages to complete
    repeat (3) `TICK(clk);
    `CHECK_EQ(max_pipe, 8'h50);
  endtask

  // Test register for test suite
  `TEST_SUITE_BEGIN(svc_stats_max_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_direct_update);
  `TEST_CASE(test_pipeline_update);
  `TEST_CASE(test_clear);
  `TEST_CASE(test_enable_behavior);
  `TEST_CASE(test_continuous_updates);
  `TEST_SUITE_END();
endmodule
