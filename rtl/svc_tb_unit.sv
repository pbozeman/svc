`ifndef SVC_TB_UNIT_SV
`define SVC_TB_UNIT_SV

`include "svc.sv"

// Super basic test framework that works with iverilog verible-verilog-format.
// I would have just used vunit, but it uses sv class polymorphism which
// isn't supported by iverilog. Also, verible-verilog-format does not parse
// vunit's "`TEST_SUITE begin" syntax.

`define ASSERT_MSG(op, file, line, a, b)                      \
  $display("ASSERT_%s FAILURE: %s:%0d %0d(0x%0h) %0d(0x%0h)", \
           op, file, line, a, a, b, b);                       \
  $fatal;

`define ASSERT_EQ(a, b)                                       \
  if (!(a === b)) begin                                       \
    `ASSERT_MSG("EQ", `__FILE__, `__LINE__, a, b);            \
  end

`define ASSERT_NEQ(a, b)                                      \
  if (!(a !== b)) begin                                       \
    `ASSERT_MSG("NEQ", `__FILE__, `__LINE__, a, b);           \
  end

`define TEST_CLK_NS(clk, ns)                                  \
  logic clk;                                                  \
  initial begin                                               \
    clk = 0;                                                  \
    forever #(ns / 2) clk = ~clk;                             \
  end

`define TEST_SUITE_BEGIN(tb_module_name)                      \
`ifndef VERILATOR                                             \
  int line_num;                                               \
`endif                                                        \
                                                              \
  initial begin                                               \
    $dumpfile({".build/", `"tb_module_name`", ".vcd"});       \
    $dumpvars(0, tb_module_name);                             \
  end                                                         \
                                                              \
  initial begin

`define TEST_CASE(test_task)            \
`ifndef VERILATOR                       \
  line_num = `__LINE__;                 \
`endif                                  \
  test_task();

`define TEST_SUITE_END(arg = "")        \
  #100;                                 \
  $finish;                              \
  end

`endif
