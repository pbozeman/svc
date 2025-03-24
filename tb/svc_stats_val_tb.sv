`include "svc_unit.sv"
`include "svc_stats_val.sv"

module svc_stats_val_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam WIDTH = 8;
  localparam STAT_WIDTH = 32;

  logic                  stat_clear;
  logic                  stat_en;
  logic [     WIDTH-1:0] stat_val;
  logic [     WIDTH-1:0] stat_min;
  logic [     WIDTH-1:0] stat_max;
  logic [STAT_WIDTH-1:0] stat_sum;

  svc_stats_val #(
      .WIDTH     (WIDTH),
      .STAT_WIDTH(STAT_WIDTH)
  ) uut (
      .clk       (clk),
      .rst_n     (rst_n),
      .stat_clear(stat_clear),
      .stat_en   (stat_en),
      .stat_val  (stat_val),
      .stat_min  (stat_min),
      .stat_max  (stat_max),
      .stat_sum  (stat_sum)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      stat_clear <= 1'b0;
      stat_en    <= 1'b0;
      stat_val   <= 0;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(stat_min, {WIDTH{1'b1}});
    `CHECK_EQ(stat_max, 0);
    `CHECK_EQ(stat_sum, 0);
  endtask

  task automatic test_basic_operation();
    logic [STAT_WIDTH-1:0] expected_sum;
    expected_sum = 0;
    stat_en      = 1'b1;

    // First value
    stat_val     = 66;
    expected_sum += 66;
    `TICK(clk);
    `CHECK_EQ(stat_min, 66);
    `CHECK_EQ(stat_max, 66);
    `CHECK_EQ(stat_sum, expected_sum);

    // Second value
    stat_val = 24;
    expected_sum += 24;
    `TICK(clk);
    `CHECK_EQ(stat_min, 24);
    `CHECK_EQ(stat_max, 66);
    `CHECK_EQ(stat_sum, expected_sum);

    // Third value
    stat_val = 127;
    expected_sum += 127;
    `TICK(clk);
    `CHECK_EQ(stat_min, 24);
    `CHECK_EQ(stat_max, 127);
    `CHECK_EQ(stat_sum, expected_sum);

    // Fourth value
    stat_val = 1;
    expected_sum += 1;
    `TICK(clk);
    `CHECK_EQ(stat_min, 1);
    `CHECK_EQ(stat_max, 127);
    `CHECK_EQ(stat_sum, expected_sum);

    stat_en = 1'b0;
  endtask

  task automatic test_stat_enable();
    logic [     WIDTH-1:0] prev_min;
    logic [     WIDTH-1:0] prev_max;
    logic [STAT_WIDTH-1:0] prev_sum;

    stat_en  = 1'b0;
    stat_val = 170;

    `TICK(clk);

    prev_min = stat_min;
    prev_max = stat_max;
    prev_sum = stat_sum;

    `TICK(clk);
    `CHECK_EQ(stat_min, prev_min);
    `CHECK_EQ(stat_max, prev_max);
    `CHECK_EQ(stat_sum, prev_sum);

    stat_en = 1'b1;
    `TICK(clk);
    `CHECK_NEQ(stat_sum, prev_sum);
  endtask

  task automatic test_stat_clear();
    stat_en  = 1'b1;
    stat_val = 85;

    `TICK(clk);
    `CHECK_NEQ(stat_sum, 0);

    stat_clear = 1'b1;
    `TICK(clk);
    `CHECK_EQ(stat_min, {WIDTH{1'b1}});
    `CHECK_EQ(stat_max, 8'h00);
    `CHECK_EQ(stat_sum, 0);

    stat_clear = 1'b0;
  endtask

  task automatic test_edge_cases();
    stat_en  = 1'b1;

    stat_val = 0;
    `TICK(clk);
    `CHECK_EQ(stat_min, 0);

    stat_val = 255;
    `TICK(clk);
    `CHECK_EQ(stat_max, 255);

    stat_en = 1'b0;
  endtask

  `TEST_SUITE_BEGIN(svc_stats_val_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_operation);
  `TEST_CASE(test_stat_enable);
  `TEST_CASE(test_stat_clear);
  `TEST_CASE(test_edge_cases);
  `TEST_SUITE_END();
endmodule
