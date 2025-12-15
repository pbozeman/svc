`include "svc_unit.sv"

`include "svc_rv_pipe_ctrl.sv"

module svc_rv_pipe_ctrl_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  //
  // Test signals for default configuration (REG=1)
  //
  logic valid_i;
  logic valid_o;
  logic ready_i;
  logic stall_i;
  logic flush_i;
  logic bubble_i;
  logic advance_o;
  logic flush_o;
  logic bubble_o;

  svc_rv_pipe_ctrl #(
      .REG(1)
  ) uut (
      .clk      (clk),
      .rst_n    (rst_n),
      .valid_i  (valid_i),
      .valid_o  (valid_o),
      .ready_i  (ready_i),
      .stall_i  (stall_i),
      .flush_i  (flush_i),
      .bubble_i (bubble_i),
      .advance_o(advance_o),
      .flush_o  (flush_o),
      .bubble_o (bubble_o)
  );

  //
  // Test signals for passthrough configuration (REG=0)
  //
  logic valid_o_pt;
  logic advance_o_pt;
  logic flush_o_pt;
  logic bubble_o_pt;

  svc_rv_pipe_ctrl #(
      .REG(0)
  ) uut_passthrough (
      .clk      (clk),
      .rst_n    (rst_n),
      .valid_i  (valid_i),
      .valid_o  (valid_o_pt),
      .ready_i  (ready_i),
      .stall_i  (stall_i),
      .flush_i  (flush_i),
      .bubble_i (bubble_i),
      .advance_o(advance_o_pt),
      .flush_o  (flush_o_pt),
      .bubble_o (bubble_o_pt)
  );

  //
  // Initialize signals in reset
  //
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      valid_i  <= 1'b0;
      ready_i  <= 1'b1;
      stall_i  <= 1'b0;
      flush_i  <= 1'b0;
      bubble_i <= 1'b0;
    end
  end

  //
  // Test: Reset clears valid
  //
  task automatic test_reset();
    `CHECK_FALSE(valid_o);
  endtask

  //
  // Test: advance signal when valid_i and can_accept
  //
  task automatic test_advance();
    valid_i  = 1'b1;
    ready_i  = 1'b1;
    flush_i  = 1'b0;
    bubble_i = 1'b0;
    `TICK(clk);

    `CHECK_TRUE(advance_o);
    `CHECK_FALSE(flush_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_TRUE(valid_o);
  endtask

  //
  // Test: hold when backpressured (valid_o && !ready_i)
  //
  task automatic test_hold();
    //
    // First advance some valid data
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Now backpressure - should hold
    //
    ready_i = 1'b0;
    `TICK(clk);

    `CHECK_FALSE(advance_o);
    `CHECK_FALSE(flush_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_TRUE(valid_o);

    ready_i = 1'b1;
  endtask

  //
  // Test: flush signal when flush_i=1
  //
  task automatic test_flush();
    //
    // First advance some valid data
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Flush
    //
    flush_i = 1'b1;
    `TICK(clk);

    `CHECK_FALSE(advance_o);
    `CHECK_TRUE(flush_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_FALSE(valid_o);

    flush_i = 1'b0;
  endtask

  //
  // Test: bubble signal when bubble_i=1 and can_accept
  //
  task automatic test_bubble();
    //
    // First advance some valid data
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Bubble (with can_accept since ready_i=1)
    //
    bubble_i = 1'b1;
    `TICK(clk);

    `CHECK_FALSE(advance_o);
    `CHECK_FALSE(flush_o);
    `CHECK_TRUE(bubble_o);
    `CHECK_FALSE(valid_o);

    bubble_i = 1'b0;
  endtask

  //
  // Test: Bubble requires can_accept (hold takes priority when backpressured)
  //
  task automatic test_bubble_requires_can_accept();
    //
    // First advance some valid data
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Bubble during backpressure (ready_i=0, valid_o=1)
    //
    ready_i  = 1'b0;
    bubble_i = 1'b1;
    `TICK(clk);

    //
    // Should hold since !can_accept
    //
    `CHECK_FALSE(advance_o);
    `CHECK_FALSE(flush_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_TRUE(valid_o);

    bubble_i = 1'b0;
    ready_i  = 1'b1;
  endtask

  //
  // Test: Flush overrides bubble
  //
  task automatic test_flush_overrides_bubble();
    //
    // First advance some valid data
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Flush and bubble at the same time
    //
    flush_i  = 1'b1;
    bubble_i = 1'b1;
    `TICK(clk);

    //
    // Flush should take priority
    //
    `CHECK_FALSE(advance_o);
    `CHECK_TRUE(flush_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_FALSE(valid_o);

    flush_i  = 1'b0;
    bubble_i = 1'b0;
  endtask

  //
  // Test: Flush works even when backpressured
  //
  task automatic test_flush_when_backpressured();
    //
    // First advance some valid data
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Backpressure, then flush
    //
    ready_i = 1'b0;
    flush_i = 1'b1;
    `TICK(clk);

    //
    // Flush should still work
    //
    `CHECK_FALSE(advance_o);
    `CHECK_TRUE(flush_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_FALSE(valid_o);

    flush_i = 1'b0;
    ready_i = 1'b1;
  endtask

  //
  // Test: Passthrough signals
  //
  task automatic test_passthrough();
    //
    // Passthrough should directly connect valid_i to valid_o
    //
    valid_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o_pt);
    `CHECK_TRUE(advance_o_pt);
    `CHECK_FALSE(flush_o_pt);
    `CHECK_FALSE(bubble_o_pt);

    valid_i = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(valid_o_pt);
    `CHECK_TRUE(advance_o_pt);

    //
    // flush_i, bubble_i, ready_i should have no effect
    //
    valid_i  = 1'b1;
    flush_i  = 1'b1;
    bubble_i = 1'b1;
    ready_i  = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(valid_o_pt);
    `CHECK_TRUE(advance_o_pt);

    flush_i  = 1'b0;
    bubble_i = 1'b0;
    ready_i  = 1'b1;
  endtask

  //
  // Test: Hold retains valid for multiple cycles
  //
  task automatic test_hold_multiple_cycles();
    //
    // First advance some valid data
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Hold for multiple cycles (backpressure)
    //
    ready_i = 1'b0;
    valid_i = 1'b0;
    repeat (3) begin
      `TICK(clk);
      `CHECK_FALSE(advance_o);
      `CHECK_TRUE(valid_o);
    end

    ready_i = 1'b1;
  endtask

  //
  // Test: Back-to-back advances
  //
  task automatic test_back_to_back();
    valid_i = 1'b1;
    ready_i = 1'b1;

    repeat (3) begin
      `TICK(clk);
      `CHECK_TRUE(advance_o);
      `CHECK_TRUE(valid_o);
    end
  endtask

  //
  // Test: Idle state (no valid data)
  //
  task automatic test_idle();
    //
    // With valid_i=0 and valid_o=0, nothing to do
    //
    valid_i = 1'b0;
    ready_i = 1'b1;
    `TICK(clk);

    `CHECK_FALSE(advance_o);
    `CHECK_FALSE(flush_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_FALSE(valid_o);
  endtask

  //
  // Test: Stall prevents advance
  //
  task automatic test_stall_prevents_advance();
    valid_i = 1'b1;
    ready_i = 1'b1;
    stall_i = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Enable stall - should prevent advance even with valid_i
    //
    stall_i = 1'b1;
    `TICK(clk);

    `CHECK_FALSE(advance_o);
    `CHECK_FALSE(bubble_o);
    `CHECK_TRUE(valid_o);

    stall_i = 1'b0;
  endtask

  //
  // Test: Stall holds valid_o stable
  //
  task automatic test_stall_holds_valid();
    //
    // First get valid_o=1
    //
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Stall with valid_i=0 - valid_o should remain stable
    //
    stall_i = 1'b1;
    valid_i = 1'b0;
    repeat (3) begin
      `TICK(clk);
      `CHECK_TRUE(valid_o);
    end

    stall_i = 1'b0;
  endtask

  //
  // Test: Stall prevents bubble
  //
  task automatic test_stall_prevents_bubble();
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Try to bubble while stalled - should be ignored
    //
    stall_i  = 1'b1;
    bubble_i = 1'b1;
    `TICK(clk);

    `CHECK_FALSE(bubble_o);
    `CHECK_TRUE(valid_o);

    stall_i  = 1'b0;
    bubble_i = 1'b0;
  endtask

  //
  // Test: Flush overrides stall
  //
  task automatic test_flush_overrides_stall();
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Flush should work even when stalled
    //
    stall_i = 1'b1;
    flush_i = 1'b1;
    `TICK(clk);

    `CHECK_TRUE(flush_o);
    `CHECK_FALSE(valid_o);

    stall_i = 1'b0;
    flush_i = 1'b0;
  endtask

  //
  // Test: Stall release allows normal operation
  //
  task automatic test_stall_release();
    valid_i = 1'b1;
    ready_i = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(valid_o);

    //
    // Stall for several cycles
    //
    stall_i = 1'b1;
    repeat (3) begin
      `TICK(clk);
      `CHECK_FALSE(advance_o);
    end

    //
    // Release stall - should resume normal operation
    //
    stall_i = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(advance_o);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_pipe_ctrl_tb);

  `TEST_CASE(test_reset);
  `TEST_CASE(test_advance);
  `TEST_CASE(test_hold);
  `TEST_CASE(test_flush);
  `TEST_CASE(test_bubble);
  `TEST_CASE(test_bubble_requires_can_accept);
  `TEST_CASE(test_flush_overrides_bubble);
  `TEST_CASE(test_flush_when_backpressured);
  `TEST_CASE(test_passthrough);
  `TEST_CASE(test_hold_multiple_cycles);
  `TEST_CASE(test_back_to_back);
  `TEST_CASE(test_idle);
  `TEST_CASE(test_stall_prevents_advance);
  `TEST_CASE(test_stall_holds_valid);
  `TEST_CASE(test_stall_prevents_bubble);
  `TEST_CASE(test_flush_overrides_stall);
  `TEST_CASE(test_stall_release);

  `TEST_SUITE_END();

endmodule
