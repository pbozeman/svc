`ifndef SVC_TB_UNIT_SV
`define SVC_TB_UNIT_SV

`include "svc.sv"

// Super basic test framework that works with iverilog verible-verilog-format.
// I would have just used vunit, but it uses sv class polymorphism which
// isn't supported by iverilog. Also, verible-verilog-format does not parse
// vunit's "`TEST_SUITE begin" syntax.

`define COLOR_BLACK "\033[30m"
`define COLOR_RED "\033[31m"
`define COLOR_GREEN "\033[32m"
`define COLOR_YELLOW "\033[33m"
`define COLOR_BLUE "\033[34m"
`define COLOR_MAGENTA "\033[34m"
`define COLOR_CYAN "\033[36m"
`define COLOR_WHITE "\033[36m"
`define COLOR_RESET "\033[0m"

`define ASSERT_MSG(op, file, line, a, b)                                     \
  $display("%sFAIL%s\nASSERT_%s FAILURE: %s%s:%0d%s %0d(0x%0h) %0d(0x%0h)",  \
           `COLOR_RED, `COLOR_RESET,                                         \
            op, `COLOR_YELLOW, file, line, `COLOR_RESET,  a, a, b, b);       \
  $display("%smake %s RUN=%s%s",                                             \
           `COLOR_CYAN, svc_tb_module_name, svc_tb_test_name, `COLOR_RESET); \
  $display("%sgtkwave .build/%s.vcd%s",                                      \
           `COLOR_YELLOW, svc_tb_module_name, `COLOR_RESET);                 \
  $fatal;

`define CHECK_EQ(a, b)                                                       \
  if (!(a === b)) begin                                                      \
    `ASSERT_MSG("EQ", `__FILE__, `__LINE__, a, b);                           \
  end

`define CHECK_NEQ(a, b)                                                      \
  if (!(a !== b)) begin                                                      \
    `ASSERT_MSG("NEQ", `__FILE__, `__LINE__, a, b);                          \
  end

`define TEST_CLK_NS(clk, ns)                                                 \
  logic clk;                                                                 \
  initial begin                                                              \
    clk = 0;                                                                 \
    forever #(ns / 2) clk = ~clk;                                            \
  end

`define TEST_RST_N(clk, rst_n, cycles = 5)                                   \
  logic rst_n;                                                               \
  `TEST_TASK_RESET_N(clk, rst_n, cycles)

`define TEST_TASK_RESET_N(clk, rst_n, cycles = 5)                            \
  task reset_``rst_n``();                                                    \
    rst_n = 0;                                                               \
    repeat (cycles) @(posedge clk);                                          \
    rst_n = 1;                                                               \
    @(posedge clk);                                                          \
  endtask                                                                    \
  `define TEST_RESET_TASK reset_``rst_n``();

`define TEST_SUITE_BEGIN(tb_module_name)                                     \
`ifndef VERILATOR                                                            \
  int line_num;                                                              \
`endif                                                                       \
  string svc_tb_module_name;                                                 \
  string svc_tb_test_name;                                                   \
  string svc_tb_test_name_run;                                               \
                                                                             \
  initial begin                                                              \
    svc_tb_module_name = `"tb_module_name`";                                 \
  end                                                                        \
                                                                             \
  initial begin                                                              \
    $dumpfile({".build/", `"tb_module_name`", ".vcd"});                      \
    $dumpvars(0, tb_module_name);                                            \
  end                                                                        \
                                                                             \
  initial begin

`define TEST_SETUP(setup_task) \
  `define TEST_SETUP_TASK setup_task();

`define TEST_CASE(test_task)                                                 \
`ifndef VERILATOR                                                            \
  line_num = `__LINE__;                                                      \
`endif                                                                       \
  svc_tb_test_name = `"test_task`";                                          \
  if (!$value$plusargs("run=%s", svc_tb_test_name_run) ||                    \
      svc_tb_test_name_run == "" ||                                          \
      svc_tb_test_name_run == svc_tb_test_name) begin                        \
    $fwrite(1, "%-50s: ", {svc_tb_module_name, ":", svc_tb_test_name});      \
`ifdef TEST_SETUP_TASK                                                       \
    `TEST_SETUP_TASK                                                         \
`endif                                                                       \
`ifdef TEST_RESET_TASK                                                       \
    `TEST_RESET_TASK                                                         \
`endif                                                                       \
    test_task();                                                             \
    $fwrite(1, "%sPASS%s\n", `COLOR_GREEN, `COLOR_RESET);                    \
  end                                                                        \

`define TEST_SUITE_END(arg = "")                                             \
  #100;                                                                      \
  $finish(0);                                                                \
  end

`endif