`include "svc_unit.sv"

module svc_unit_reset_tb;
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

  task automatic test_no_setup();
    `CHECK_TRUE(reset_happened);
  endtask

  task automatic test_setup();
    `CHECK_TRUE(reset_happened);
  endtask

  `TEST_SUITE_BEGIN(svc_unit_reset_tb);

  // Must run before setup was defined
  `TEST_CASE(test_no_setup);

  `TEST_SETUP(setup);
  `TEST_CASE(test_setup);

  `TEST_SUITE_END();
endmodule
