`include "svc_unit.sv"

`include "svc_edge_rose.sv"

module svc_edge_rose_tbi;
  `TEST_CLK_NS(clk, 10);

  logic signal = 0;
  logic rose;

  svc_edge_rose uut (
      .clk (clk),
      .i   (signal),
      .rose(rose)
  );

  task automatic test_initial;
    `CHECK_FALSE(rose);
  endtask

  task automatic test_basic;
    signal = 1;
    `CHECK_TRUE(rose);

    `TICK(clk);
    `CHECK_FALSE(rose);

    signal = 0;
    `CHECK_FALSE(rose);

    `TICK(clk);
    `CHECK_FALSE(rose);

    signal = 1;
    `CHECK_TRUE(rose);
  endtask

  `TEST_SUITE_BEGIN(svc_edge_rose_tbi);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
