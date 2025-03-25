`include "svc_unit.sv"
`include "svc_stats_sum.sv"

module svc_stats_sum_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam WIDTH = 8;
  localparam STAT_WIDTH = 32;
  localparam STAGES = 0;

  logic                  clr;
  logic                  en;
  logic [     WIDTH-1:0] val;
  logic [STAT_WIDTH-1:0] sum;

  svc_stats_sum #(
      .WIDTH     (WIDTH),
      .STAT_WIDTH(STAT_WIDTH),
      .STAGES    (STAGES)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (clr),
      .en   (en),
      .val  (val),
      .sum  (sum)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      clr <= 1'b0;
      en  <= 1'b0;
      val <= '0;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(sum, 0);
  endtask

  task automatic test_basic_sum();
    en  = 1'b1;
    val = 8'd5;
    `TICK(clk);
    `CHECK_EQ(sum, 32'd5);

    val = 8'd10;
    `TICK(clk);
    `CHECK_EQ(sum, 32'd15);

    en  = 1'b0;
    val = 8'd20;
    `TICK(clk);
    `CHECK_EQ(sum, 32'd15);
  endtask

  task automatic test_clear();
    en  = 1'b1;
    val = 8'd25;
    `TICK(clk);

    clr = 1'b1;
    `TICK(clk);
    `CHECK_EQ(sum, 0);

    clr = 1'b0;
    val = 8'd7;
    `TICK(clk);
    `CHECK_EQ(sum, 32'd7);
  endtask

  task automatic test_accumulate_large_values();
    clr = 1'b1;
    `TICK(clk);
    clr = 1'b0;

    en  = 1'b1;
    val = 8'hFF;

    for (int i = 0; i < 100; i++) begin
      `TICK(clk);
    end

    `CHECK_EQ(sum, 255 * 100);
  endtask

  `TEST_SUITE_BEGIN(svc_stats_sum_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_sum);
  `TEST_CASE(test_clear);
  `TEST_CASE(test_accumulate_large_values);
  `TEST_SUITE_END();
endmodule
