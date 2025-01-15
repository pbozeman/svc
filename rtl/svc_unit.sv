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
`define COLOR_MGENTA "\033[34m"
`define COLOR_CYAN "\033[36m"
`define COLOR_WHITE "\033[36m"
`define COLOR_RESET "\033[0m"

`define CHECK_MSG_1(op, file, line, a)                                       \
  $display("%sFAIL%s\n%s%s%s:%s%0d%s CHECK_%s(%s%s%s=0x%0h)",                \
           `COLOR_RED, `COLOR_RESET,                                         \
           `COLOR_YELLOW, file, `COLOR_RESET,                                \
           `COLOR_RED, line, `COLOR_RESET,                                   \
           op, `COLOR_YELLOW, `"a`", `COLOR_RESET,  a) ;                     \
  $display("%smake %s RUN=%s%s",                                             \
           `COLOR_CYAN, svc_tb_module_name, svc_tb_test_name, `COLOR_RESET); \
  $display("%sgtkwave .build/%s.vcd%s",                                      \
           `COLOR_YELLOW, svc_tb_module_name, `COLOR_RESET);                 \
  $fatal;

`define CHECK_MSG_2(op, file, line, a, b)                                    \
  $display("%sFAIL%s\n%s%s%s:%s%0d%s CHECK_%s(%s%s%s=0x%0h, %s=0x%0h)",      \
           `COLOR_RED, `COLOR_RESET,                                         \
           `COLOR_YELLOW, file, `COLOR_RESET,                                \
           `COLOR_RED, line, `COLOR_RESET,                                   \
           op, `COLOR_YELLOW, `"a`", `COLOR_RESET,  a, `"b`", b) ;           \
  $display("%smake %s RUN=%s%s",                                             \
           `COLOR_CYAN, svc_tb_module_name, svc_tb_test_name, `COLOR_RESET); \
  $display("%sgtkwave .build/%s.vcd%s",                                      \
           `COLOR_YELLOW, svc_tb_module_name, `COLOR_RESET);                 \
  $fatal;

// Tiny tick lets async logic propagate after a clock before asserts.
// The initial #0 makes sure other clocked blocks run first, and then,
// we do a #0.1 on the first check so that async logic can propagate and
// before we start doing assertion checks.
`define SVC_TINY_TICK                                                         \
`ifndef VERILATOR                                                             \
  #0;                                                                         \
  if (!svc_tiny_ticked) begin                                                 \
    svc_tiny_ticked = 1'b1;                                                   \
    #0.1;                                                                     \
  end                                                                         \
`endif

`define CHECK_TRUE(a)                                                         \
  `SVC_TINY_TICK;                                                             \
  if ((a) !== 1) begin                                                        \
    `CHECK_MSG_1("TRUE", `__FILE__, `__LINE__, a);                            \
  end

`define CHECK_FALSE(a)                                                        \
  `SVC_TINY_TICK;                                                             \
  if ((a) !== 0) begin                                                        \
    `CHECK_MSG_1("FALSE", `__FILE__, `__LINE__, a);                           \
  end

`define CHECK_EQ(a, b)                                                        \
  `SVC_TINY_TICK;                                                             \
  if ((a) !== (b)) begin                                                      \
    `CHECK_MSG_2("EQ", `__FILE__, `__LINE__, a, b);                           \
  end

`define CHECK_NEQ(a, b)                                                       \
  `SVC_TINY_TICK;                                                             \
  if ((a) === (b)) begin                                                      \
    `CHECK_MSG_2("NEQ", `__FILE__, `__LINE__, a, b);                          \
  end

`define CHECK_LT(a, b)                                                        \
  `SVC_TINY_TICK;                                                             \
  if (((a) >= (b)) || ((a) === 'x) || ((b) === 'x) ||                         \
      ((a) === 'z) || ((b) === 'z)) begin                                     \
    `CHECK_MSG_2("LT", `__FILE__, `__LINE__, a, b);                           \
  end

`define CHECK_LTE(a, b)                                                       \
  `SVC_TINY_TICK;                                                             \
  if (((a) > (b)) || ((a) === 'x) || ((b) === 'x) ||                          \
      ((a) === 'z) || ((b) === 'z)) begin                                     \
    `CHECK_MSG_2("LT", `__FILE__, `__LINE__, a, b);                           \
  end

`define CHECK_GT(a, b)                                                        \
  `SVC_TINY_TICK;                                                             \
  if (((a) <= (b)) || ((a) === 'x) || ((b) === 'x) ||                         \
      ((a) === 'z) || ((b) === 'z)) begin                                     \
    `CHECK_MSG_2("GT", `__FILE__, `__LINE__, a, b);                           \
  end

`define CHECK_GTE(a, b)                                                       \
  `SVC_TINY_TICK;                                                             \
  if (((a) < (b)) || ((a) === 'x) || ((b) === 'x) ||                          \
      ((a) === 'z) || ((b) === 'z)) begin                                     \
    `CHECK_MSG_2("GTE", `__FILE__, `__LINE__, a, b);                          \
  end

`define TEST_CLK_NS(clk, ns)                                                 \
`define SVC_CLK clk                                                          \
  logic clk;                                                                 \
  initial begin                                                              \
    clk = 0;                                                                 \
    forever #(ns / 2) clk = ~clk;                                            \
  end                                                                        \
`ifndef VERILATOR                                                            \
  always_ff @(posedge clk) svc_tiny_ticked = 1'b0;                           \
`endif

`define TEST_RST_N(clk, rst_n, cycles = 5)                                   \
  logic rst_n;                                                               \
  `TEST_TASK_RESET_N(clk, rst_n, cycles)

`define TICK(clk)                                                            \
  @(posedge clk);                                                            \
  #0;

`ifndef VERILATOR
`define CHECK_WAIT_FOR(clk, signal, max_cnt = 16)                            \
    svc_wait_cnt = 0;                                                        \
    `SVC_TINY_TICK;                                                          \
    while ((signal) === 0 && svc_wait_cnt < max_cnt) begin                   \
      @(posedge clk);                                                        \
      svc_wait_cnt = svc_wait_cnt + 1;                                       \
      `SVC_TINY_TICK;                                                        \
    end                                                                      \
    if ((signal) !== 1) begin                                                \
      `CHECK_MSG_1("WAIT_FOR", `__FILE__, `__LINE__, signal);                \
    end
`else
`define CHECK_WAIT_FOR(clk, signal, max_cnt = 16)
`endif

`define TEST_TASK_RESET_N(clk, rst_n, cycles = 5)                            \
  task reset_``rst_n``();                                                    \
    rst_n = 0;                                                               \
    repeat (cycles) @(posedge clk);                                          \
`ifndef VERILATOR                                                            \
    rst_n <= 1;                                                              \
`endif                                                                       \
    #0.1;                                                                    \
  endtask                                                                    \
  `define TEST_RESET_TASK reset_``rst_n``();

`define TEST_SUITE_BEGIN(tb_module_name)                                     \
`ifndef VERILATOR                                                            \
  int line_num;                                                              \
  int svc_wait_cnt;                                                          \
  logic svc_tiny_ticked;                                                     \
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
`ifdef SVC_CLK                                                               \
    @(posedge `SVC_CLK);                                                     \
`endif                                                                       \
    $fwrite(1, "%sPASS%s\n", `COLOR_GREEN, `COLOR_RESET);                    \
  end                                                                        \

`define TEST_SUITE_END(arg = "")                                             \
  #100;                                                                      \
  $finish(0);                                                                \
  end

`endif
