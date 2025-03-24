`include "svc_unit.sv"
`include "svc_stats_counter.sv"
module svc_stats_counter_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);
  localparam STAT_WIDTH = 32;
  logic                  stat_clear;
  logic                  stat_inc;
  logic                  stat_dec;
  logic [STAT_WIDTH-1:0] stat_cnt;
  logic [STAT_WIDTH-1:0] stat_max;

  svc_stats_counter #(
      .STAT_WIDTH(STAT_WIDTH)
  ) uut (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_inc  (stat_inc),
      .stat_dec  (stat_dec),
      .stat_cnt  (stat_cnt),
      .stat_max  (stat_max)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      stat_clear <= 1'b0;
      stat_inc   <= 1'b0;
      stat_dec   <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(stat_cnt, 0);
    `CHECK_EQ(stat_max, 0);
  endtask

  task automatic test_basic_increment();
    `CHECK_EQ(stat_cnt, 0);

    stat_inc = 1'b1;
    `TICK(clk);

    `CHECK_EQ(stat_cnt, 1);
    `CHECK_EQ(stat_max, 1);

    stat_inc = 1'b0;
    `TICK(clk);
    `CHECK_EQ(stat_cnt, 1);

    stat_inc = 1'b1;
    repeat (5) `TICK(clk);
    `CHECK_EQ(stat_cnt, 6);
    `CHECK_EQ(stat_max, 6);
  endtask

  task automatic test_basic_decrement();
    stat_inc = 1'b1;
    repeat (10) `TICK(clk);
    `CHECK_EQ(stat_cnt, 10);
    `CHECK_EQ(stat_max, 10);

    stat_inc = 1'b0;
    `TICK(clk);

    stat_dec = 1'b1;
    `TICK(clk);
    `CHECK_EQ(stat_cnt, 9);

    repeat (5) `TICK(clk);
    `CHECK_EQ(stat_cnt, 4);
  endtask

  task automatic test_clear();
    stat_inc = 1'b1;
    stat_dec = 1'b0;
    repeat (5) `TICK(clk);
    `CHECK_EQ(stat_cnt, 5);

    stat_inc   = 1'b0;
    stat_clear = 1'b1;
    `TICK(clk);

    `CHECK_EQ(stat_cnt, 0);
    `CHECK_EQ(stat_max, 0);

    stat_inc = 1'b1;
    `TICK(clk);
    `CHECK_EQ(stat_cnt, 0);

    stat_clear = 1'b0;
    `TICK(clk);
    `CHECK_EQ(stat_cnt, 1);
    `CHECK_EQ(stat_max, 1);
  endtask

  task automatic test_simultaneous_inc_dec();
    stat_clear = 1'b1;
    `TICK(clk);

    stat_clear = 1'b0;
    stat_inc   = 1'b1;
    repeat (5) `TICK(clk);
    `CHECK_EQ(stat_cnt, 5);

    stat_inc = 1'b1;
    stat_dec = 1'b1;
    `TICK(clk);
    `CHECK_EQ(stat_cnt, 5);

    stat_inc = 1'b0;
    stat_dec = 1'b1;
    `TICK(clk);
    `CHECK_EQ(stat_cnt, 4);
  endtask

  task automatic test_max_tracking();
    stat_clear = 1'b1;
    `TICK(clk);
    stat_clear = 1'b0;

    // First go up to 10
    stat_inc   = 1'b1;
    repeat (10) `TICK(clk);
    stat_inc = 1'b0;
    `CHECK_EQ(stat_cnt, 10);
    `CHECK_EQ(stat_max, 10);

    // Then go down to 2
    stat_dec = 1'b1;
    repeat (8) `TICK(clk);
    stat_dec = 1'b0;
    `CHECK_EQ(stat_cnt, 2);

    // Now go up to 15 (new max)
    stat_inc = 1'b1;
    repeat (13) `TICK(clk);
    stat_inc = 1'b0;
    `CHECK_EQ(stat_cnt, 15);
    `CHECK_EQ(stat_max, 15);

    // And finally to 0
    stat_dec = 1'b1;
    repeat (15) `TICK(clk);
    stat_dec = 1'b0;
    `CHECK_EQ(stat_cnt, 0);

    // Verify final values
    `CHECK_EQ(stat_max, 15);
  endtask

  `TEST_SUITE_BEGIN(svc_stats_counter_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_increment);
  `TEST_CASE(test_basic_decrement);
  `TEST_CASE(test_clear);
  `TEST_CASE(test_simultaneous_inc_dec);
  `TEST_CASE(test_max_tracking);
  `TEST_SUITE_END();
endmodule
