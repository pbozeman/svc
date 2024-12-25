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

  task test_another();
    @(posedge clk);
    `ASSERT_EQ(1, 1);
  endtask

  `TEST_SUITE_BEGIN(svc_tb_unit_tb);

  `TEST_CASE(test_clk);
  `TEST_CASE(test_another);

  `TEST_SUITE_END();
endmodule
