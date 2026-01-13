`include "svc_unit.sv"
`include "svc_stats_min.sv"

module svc_stats_min_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic       clr;
  logic       en;
  logic [7:0] val;
  logic [7:0] min;

  svc_stats_min #(
      .WIDTH         (8),
      .BITS_PER_STAGE(8)
  ) uut_direct (
      .clk(clk),
      .clr(clr),
      .en (en),
      .val(val),
      .min(min)
  );

  logic [7:0] min_pipe;

  svc_stats_min #(
      .WIDTH         (8),
      .BITS_PER_STAGE(4)
  ) uut_pipe (
      .clk(clk),
      .clr(clr),
      .en (en),
      .val(val),
      .min(min_pipe)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      clr <= 1'b1;
      en  <= 1'b0;
      val <= 8'h00;
    end
  end

  task automatic test_direct_update();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h42;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(min, 8'h42);

    en  = 1'b1;
    val = 8'h20;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(min, 8'h20);

    en  = 1'b1;
    val = 8'h30;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(min, 8'h20);

    en  = 1'b1;
    val = 8'h00;
    `TICK(clk);
    en = 1'b0;
    `CHECK_EQ(min, 8'h00);
  endtask

  task automatic test_pipeline_update();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h80;
    `TICK(clk);
    en = 1'b0;

    repeat (3) `TICK(clk);
    `CHECK_EQ(min_pipe, 8'h80);

    en  = 1'b1;
    val = 8'h40;
    `TICK(clk);
    en = 1'b0;

    repeat (3) `TICK(clk);
    `CHECK_EQ(min_pipe, 8'h40);

    en  = 1'b1;
    val = 8'h60;
    `TICK(clk);
    en = 1'b0;

    repeat (3) `TICK(clk);
    `CHECK_EQ(min_pipe, 8'h40);
  endtask

  task automatic test_clear();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h10;
    `TICK(clk);
    en = 1'b0;

    repeat (3) `TICK(clk);

    `CHECK_EQ(min, 8'h10);
    `CHECK_EQ(min_pipe, 8'h10);

    clr = 1'b1;
    `TICK(clk);
    clr = 1'b0;

    `CHECK_EQ(min, 8'hFF);
    `CHECK_EQ(min_pipe, 8'hFF);
  endtask

  task automatic test_enable_behavior();
    clr = 1'b0;
    en  = 1'b1;
    val = 8'h70;
    `TICK(clk);

    val = 8'h60;
    `TICK(clk);

    en  = 1'b0;
    val = 8'h10;
    `TICK(clk);

    `CHECK_EQ(min, 8'h60);

    repeat (3) `TICK(clk);
    `CHECK_EQ(min_pipe, 8'h60);
  endtask

  task automatic test_continuous_updates();
    logic [7:0] test_values[10];

    test_values[0] = 8'h80;
    test_values[1] = 8'h70;
    test_values[2] = 8'h90;
    test_values[3] = 8'h50;
    test_values[4] = 8'h60;
    test_values[5] = 8'h40;
    test_values[6] = 8'h30;
    test_values[7] = 8'h45;
    test_values[8] = 8'h20;
    test_values[9] = 8'h35;

    clr            = 1'b1;
    `TICK(clk);
    clr = 1'b0;

    for (int i = 0; i < 10; i++) begin
      en  = 1'b1;
      val = test_values[i];
      `TICK(clk);
    end

    en = 1'b0;

    `CHECK_EQ(min, 8'h20);

    repeat (3) `TICK(clk);
    `CHECK_EQ(min_pipe, 8'h20);
  endtask

  `TEST_SUITE_BEGIN(svc_stats_min_tbi);
  `TEST_CASE(test_direct_update);
  `TEST_CASE(test_pipeline_update);
  `TEST_CASE(test_clear);
  `TEST_CASE(test_enable_behavior);
  `TEST_CASE(test_continuous_updates);
  `TEST_SUITE_END();
endmodule
