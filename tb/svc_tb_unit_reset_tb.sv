`include "svc_tb_unit.sv"

module svc_tb_unit_reset_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic reset_happened = 1'b0;
  always @(posedge clk) begin
    if (~rst_n) begin
      reset_happened <= 1'b1;
    end
  end

  task setup();
  endtask

  task test_no_setup();
    `ASSERT_EQ(reset_happened, 1'b1);
  endtask

  task test_setup();
    `ASSERT_EQ(reset_happened, 1'b1);
  endtask

  `TEST_SUITE_BEGIN(svc_tb_unit_reset_tb);

  // Must run before setup was defined
  `TEST_CASE(test_no_setup);

  `TEST_SETUP(setup);
  `TEST_CASE(test_setup);

  `TEST_SUITE_END();
endmodule
