`include "svc_unit.sv"

`include "svc_edge_fell.sv"

module svc_edge_fell_tbi;
  `TEST_CLK_NS(clk, 10);

  logic signal = 0;
  logic fell;

  svc_edge_fell uut (
      .clk (clk),
      .i   (signal),
      .fell(fell)
  );

  task automatic test_initial;
    `CHECK_FALSE(fell);
  endtask

  task automatic test_basic;
    `CHECK_FALSE(fell);

    signal = 1;
    `TICK(clk);
    `CHECK_FALSE(fell);

    `TICK(clk);
    `CHECK_FALSE(fell);

    signal = 0;
    `CHECK_TRUE(fell);

    `TICK(clk);
    `CHECK_FALSE(fell);
  endtask

  `TEST_SUITE_BEGIN(svc_edge_fell_tbi);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
