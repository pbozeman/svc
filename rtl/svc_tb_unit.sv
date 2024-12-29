`ifndef SVC_TB_UNIT_SV
`define SVC_TB_UNIT_SV

`include "svc.sv"

// Super basic test framework that works with iverilog verible-verilog-format.
// I would have just used vunit, but it uses sv class polymorphism which
// isn't supported by iverilog. Also, verible-verilog-format does not parse
// vunit's "`TEST_SUITE begin" syntax.

`define ASSERT_MSG(op, file, line, a, b)                                   \
  $display("FAIL\n       ASSERT_%s FAILURE: %s:%0d %0d(0x%0h) %0d(0x%0h)", \
           op, file, line, a, a, b, b);                                    \
  $fatal;

`define CHECK_EQ(a, b)                                        \
  if (!(a === b)) begin                                       \
    `ASSERT_MSG("EQ", `__FILE__, `__LINE__, a, b);            \
  end

`define CHECK_NEQ(a, b)                                       \
  if (!(a !== b)) begin                                       \
    `ASSERT_MSG("NEQ", `__FILE__, `__LINE__, a, b);           \
  end

`define TEST_CLK_NS(clk, ns)                                  \
  logic clk;                                                  \
  initial begin                                               \
    clk = 0;                                                  \
    forever #(ns / 2) clk = ~clk;                             \
  end

`define TEST_RST_N(clk, rst_n, cycles = 10)                   \
  logic rst_n;                                                \
  `TEST_TASK_RESET_N(clk, rst_n, cycles)

`define TEST_TASK_RESET_N(clk, rst_n, cycles = 10)            \
  task reset_``rst_n``();                                     \
    rst_n = 0;                                                \
    repeat (cycles) @(posedge clk);                           \
    rst_n = 1;                                                \
    @(posedge clk);                                           \
  endtask                                                     \
  `define TEST_RESET_TASK reset_``rst_n``();

`define TEST_SUITE_BEGIN(tb_module_name)                                  \
`ifndef VERILATOR                                                         \
  int line_num;                                                           \
  string svc_tb_module_name;                                              \
  string svc_tb_test_name;                                                \
                                                                          \
  initial begin                                                           \
    svc_tb_module_name = `"tb_module_name`";                              \
  end                                                                     \
`endif                                                                    \
                                                                          \
  initial begin                                                           \
    $dumpfile({".build/", `"tb_module_name`", ".vcd"});                   \
    $dumpvars(0, tb_module_name);                                         \
  end                                                                     \
                                                                          \
  initial begin

`define TEST_SETUP(setup_task) \
  `define TEST_SETUP_TASK setup_task();

`define TEST_CASE(test_task)                                               \
`ifndef VERILATOR                                                          \
  line_num = `__LINE__;                                                    \
`endif                                                                     \
`ifdef TEST_SETUP_TASK                                                     \
  `TEST_SETUP_TASK                                                         \
`endif                                                                     \
`ifdef TEST_RESET_TASK                                                     \
  `TEST_RESET_TASK                                                         \
`endif                                                                     \
`ifndef VERILATOR                                                          \
  if (!$value$plusargs("run=%s", svc_tb_test_name) ||                      \
      svc_tb_test_name == "" ||                                            \
      svc_tb_test_name == `"test_task`") begin                             \
    $fwrite(1, "%-50s: ", {svc_tb_module_name, ":", `"test_task`"});       \
    test_task();                                                           \
    $fwrite(1, "PASS\n");                                                  \
  end                                                                      \
`else                                                                      \
    test_task();                                                           \
`endif

`define TEST_SUITE_END(arg = "")               \
  #100;                                        \
  $finish;                                     \
  end

`endif
