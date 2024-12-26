`include "svc_tb_unit.sv"

module svc_tb_unit_tb;
  `TEST_CLK_NS(clk, 10);

  int clk_cnt = 0;
  always @(posedge clk) begin
    clk_cnt <= clk_cnt + 1;
  end

  task test_clk();
    // This is dependent on being the first test case
    `ASSERT_EQ(clk_cnt, 0);
    repeat (4) @(posedge clk);
    #1;
    `ASSERT_EQ(clk_cnt, 4);
  endtask

  logic setup_ran = 1'b0;
  task setup();
    setup_ran = 1'b1;
  endtask

  task test_no_setup();
    `ASSERT_EQ(setup_ran, 1'b0);
  endtask

  task test_setup();
    `ASSERT_EQ(setup_ran, 1'b1);
  endtask

  task test_another();
    @(posedge clk);
    `ASSERT_EQ(1, 1);
  endtask

  `TEST_SUITE_BEGIN(svc_tb_unit_tb);

  // Must run first to know clock is at 0
  `TEST_CASE(test_clk);

  // Must run before setup was defined
  `TEST_CASE(test_no_setup);

  `TEST_SETUP(setup);
  `TEST_CASE(test_setup);

  `TEST_CASE(test_another);

  `TEST_SUITE_END();

endmodule
