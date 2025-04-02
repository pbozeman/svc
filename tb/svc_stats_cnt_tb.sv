`include "svc_unit.sv"
`include "svc_stats_cnt.sv"

module svc_stats_cnt_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam STAT_WIDTH = 32;
  localparam BITS_PER_STAGE = 32;

  logic                  clr;
  logic                  inc;
  logic                  dec;
  logic [STAT_WIDTH-1:0] cnt;

  svc_stats_cnt #(
      .STAT_WIDTH    (STAT_WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (clr),
      .inc  (inc),
      .dec  (dec),
      .cnt  (cnt)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      clr <= 1'b0;
      inc <= 1'b0;
      dec <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(cnt, 0);
  endtask

  task automatic test_basic_increment();
    `CHECK_EQ(cnt, 0);

    inc = 1'b1;
    `TICK(clk);

    `CHECK_EQ(cnt, 1);

    inc = 1'b0;
    `TICK(clk);
    `CHECK_EQ(cnt, 1);

    inc = 1'b1;
    repeat (5) `TICK(clk);
    `CHECK_EQ(cnt, 6);
  endtask

  task automatic test_basic_decrement();
    inc = 1'b1;
    repeat (10) `TICK(clk);
    `CHECK_EQ(cnt, 10);

    inc = 1'b0;
    `TICK(clk);

    dec = 1'b1;
    `TICK(clk);
    `CHECK_EQ(cnt, 9);

    repeat (5) `TICK(clk);
    `CHECK_EQ(cnt, 4);
  endtask

  task automatic test_clr();
    inc = 1'b1;
    dec = 1'b0;
    repeat (5) `TICK(clk);
    `CHECK_EQ(cnt, 5);

    inc = 1'b0;
    clr = 1'b1;
    `TICK(clk);

    `CHECK_EQ(cnt, 0);

    inc = 1'b1;
    `TICK(clk);
    `CHECK_EQ(cnt, 0);

    clr = 1'b0;
    `TICK(clk);
    `CHECK_EQ(cnt, 1);
  endtask

  task automatic test_simultaneous_inc_dec();
    clr = 1'b1;
    `TICK(clk);

    clr = 1'b0;
    inc = 1'b1;
    repeat (5) `TICK(clk);
    `CHECK_EQ(cnt, 5);

    inc = 1'b1;
    dec = 1'b1;
    `TICK(clk);
    `CHECK_EQ(cnt, 5);

    inc = 1'b0;
    dec = 1'b1;
    `TICK(clk);
    `CHECK_EQ(cnt, 4);
  endtask

  `TEST_SUITE_BEGIN(svc_stats_cnt_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_increment);
  `TEST_CASE(test_basic_decrement);
  `TEST_CASE(test_clr);
  `TEST_CASE(test_simultaneous_inc_dec);
  `TEST_SUITE_END();
endmodule
