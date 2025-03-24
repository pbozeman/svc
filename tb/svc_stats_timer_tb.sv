`include "svc_unit.sv"
`include "svc_stats_timer.sv"

module svc_stats_timer_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic        stat_clear;
  logic        stat_start;
  logic        stat_end;
  logic [31:0] drop_cnt;
  logic [31:0] stat_min;
  logic [31:0] stat_max;
  logic [31:0] stat_cnt;
  logic [31:0] stat_sum;

  localparam ADDR_WIDTH = 4;
  localparam DEPTH = 1 << ADDR_WIDTH;

  // TODO: add clear test
  assign stat_clear = 1'b0;

  svc_stats_timer #(
      .ADDR_WIDTH(ADDR_WIDTH)
  ) uut (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_start(stat_start),
      .stat_end  (stat_end),
      .drop_cnt  (drop_cnt),
      .stat_min  (stat_min),
      .stat_max  (stat_max),
      .stat_cnt  (stat_cnt),
      .stat_sum  (stat_sum)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      stat_start <= 1'b0;
      stat_end   <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(drop_cnt, 32'h0);
    `CHECK_EQ(stat_min, 32'hFFFFFFFF);
    `CHECK_EQ(stat_max, 32'h0);
    `CHECK_EQ(stat_cnt, 32'h0);
  endtask

  task automatic test_basic_start_end_pairs();
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;

    repeat (3) `TICK(clk);

    stat_end = 1'b1;
    `TICK(clk);
    stat_end = 1'b0;

    `TICK(clk);

    `CHECK_EQ(drop_cnt, 0);
    `CHECK_EQ(stat_cnt, 1);
    `CHECK_EQ(stat_min, 4);
    `CHECK_EQ(stat_max, 4);

    // Test multiple start-end pairs
    for (int i = 0; i < 3; i++) begin
      stat_start = 1'b1;
      `TICK(clk);
      stat_start = 1'b0;

      repeat (2) `TICK(clk);
      stat_end = 1'b1;

      `TICK(clk);
      stat_end = 1'b0;

      `TICK(clk);
    end

    `CHECK_EQ(drop_cnt, 0);
    `CHECK_EQ(stat_cnt, 4);

    `CHECK_EQ(stat_min, 3);
    `CHECK_EQ(stat_max, 4);
    `CHECK_EQ(stat_sum, 13);
  endtask

  task automatic test_outstanding_count();
    // Fill half the buffer with start events
    for (int i = 0; i < DEPTH / 2; i++) begin
      stat_start = 1'b1;
      `TICK(clk);
      stat_start = 1'b0;
      `TICK(clk);
    end

    // End half of those events
    for (int i = 0; i < DEPTH / 4; i++) begin
      stat_end = 1'b1;
      `TICK(clk);
      stat_end = 1'b0;
      `TICK(clk);
    end

    // Still no drops expected
    `CHECK_EQ(drop_cnt, 0);

    // Should have DEPTH/4 completed events
    `CHECK_EQ(stat_cnt, (DEPTH / 4));
  endtask

  task automatic test_buffer_full();
    // Fill the buffer completely
    for (int i = 0; i < DEPTH; i++) begin
      stat_start = 1'b1;
      `TICK(clk);
      stat_start = 1'b0;
      `TICK(clk);
    end

    // Buffer now full, next start should cause a drop
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;
    `CHECK_EQ(drop_cnt, 1);

    // Additional start should cause additional drops
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;
    `CHECK_EQ(drop_cnt, 2);

    // we filled to 16 (full), then added 2 more (dropped). We need to
    // remove 3 to have room to start more
    repeat (3) begin
      stat_end = 1'b1;
      `TICK(clk);
      stat_end = 1'b0;
      `CHECK_EQ(drop_cnt, 2);
    end
    stat_end = 1'b0;
    `TICK(clk);

    // Another start should now be accepted
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;

    `CHECK_EQ(drop_cnt, 2);
    `CHECK_EQ(stat_cnt, 3);
  endtask

  task automatic test_simultaneous_start_end();
    // Fill buffer halfway
    for (int i = 0; i < DEPTH / 2; i++) begin
      stat_start = 1'b1;
      `TICK(clk);
      stat_start = 1'b0;
      `TICK(clk);
    end

    // Simultaneous start and end
    stat_start = 1'b1;
    stat_end   = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;
    stat_end   = 1'b0;

    // Outstanding count should remain the same
    // (checked indirectly by making sure buffer isn't full)

    // Fill the rest of the buffer
    for (int i = 0; i < DEPTH / 2 - 1; i++) begin
      stat_start = 1'b1;
      `TICK(clk);
      stat_start = 1'b0;
      `TICK(clk);
    end

    // One more start should still work
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;

    // No drops expected
    `CHECK_EQ(drop_cnt, 0);
  endtask

  task automatic test_timing_statistics();
    // Reset counters by toggling reset
    `TICK(clk);
    rst_n = 1'b0;
    `TICK(clk);
    rst_n = 1'b1;
    `TICK(clk);

    // Create events with specific timing patterns
    // Event 1: 5 cycle latency
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;
    repeat (4) `TICK(clk);
    stat_end = 1'b1;
    `TICK(clk);
    stat_end = 1'b0;
    `TICK(clk);

    `CHECK_EQ(stat_cnt, 1);
    `CHECK_EQ(stat_min, 5);
    `CHECK_EQ(stat_max, 5);

    // Event 2: 10 cycle latency
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;
    repeat (9) `TICK(clk);
    stat_end = 1'b1;
    `TICK(clk);
    stat_end = 1'b0;
    `TICK(clk);

    `CHECK_EQ(stat_cnt, 2);
    `CHECK_EQ(stat_min, 5);
    `CHECK_EQ(stat_max, 10);

    // Event 3: 2 cycle latency (new min)
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;
    repeat (1) `TICK(clk);
    stat_end = 1'b1;
    `TICK(clk);
    stat_end = 1'b0;
    `TICK(clk);

    `CHECK_EQ(stat_cnt, 3);
    `CHECK_EQ(stat_min, 2);
    `CHECK_EQ(stat_max, 10);

    // Event 4: 15 cycle latency (new max)
    stat_start = 1'b1;
    `TICK(clk);
    stat_start = 1'b0;
    repeat (14) `TICK(clk);
    stat_end = 1'b1;
    `TICK(clk);
    stat_end = 1'b0;
    `TICK(clk);

    `CHECK_EQ(stat_cnt, 4);
    `CHECK_EQ(stat_min, 2);
    `CHECK_EQ(stat_max, 15);
  endtask

  `TEST_SUITE_BEGIN(svc_stats_timer_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_start_end_pairs);
  `TEST_CASE(test_outstanding_count);
  `TEST_CASE(test_buffer_full);
  `TEST_CASE(test_simultaneous_start_end);
  `TEST_CASE(test_timing_statistics);
  `TEST_SUITE_END();
endmodule
