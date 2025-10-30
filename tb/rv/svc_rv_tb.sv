`include "svc_unit.sv"

`include "svc_rv.sv"

module svc_rv_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;

  svc_rv #(
      .IMEM_AW(IMEM_AW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n)
  );

  task automatic test_reset;
    `CHECK_EQ(uut.pc, '0);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_tb);
  `TEST_CASE(test_reset);
  `TEST_SUITE_END();

endmodule
