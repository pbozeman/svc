`include "svc_unit.sv"

module svc_unit_tb;
  `TEST_CLK_NS(clk, 10);

  int clk_cnt = 0;
  always @(posedge clk) begin
    clk_cnt <= clk_cnt + 1;
  end

  task test_clk();
    // This is dependent on being the first test case
    `CHECK_EQ(clk_cnt, 0);
    repeat (4) `TICK(clk);
    `CHECK_EQ(clk_cnt, 4);
  endtask

  logic setup_ran = 1'b0;
  task setup();
    setup_ran = 1'b1;
  endtask

  task test_no_setup();
    `CHECK_FALSE(setup_ran);
  endtask

  task test_setup();
    `CHECK_TRUE(setup_ran);
  endtask

  task test_another();
    `TICK(clk);
    `CHECK_EQ(1, 1);
  endtask

  `TEST_SUITE_BEGIN(svc_unit_tb);

  // Must run first to know clock is at 0
  `TEST_CASE(test_clk);

  // Must run before setup was defined
  `TEST_CASE(test_no_setup);

  `TEST_SETUP(setup);
  `TEST_CASE(test_setup);

  `TEST_CASE(test_another);

  `TEST_SUITE_END();

endmodule
