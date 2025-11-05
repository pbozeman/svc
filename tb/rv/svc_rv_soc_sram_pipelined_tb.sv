`include "svc_unit.sv"

`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_pipelined_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;

  //
  // CPI expectations without regfile internal forwarding
  //
  // No regfile forwarding for better fmax on ice40 and similar FPGAs.
  // WB hazards require stalling, increasing CPI.
  //
  localparam real alu_indep_max_cpi = 1.35;
  localparam real alu_chain_max_cpi = 3.5;
  localparam real br_taken_max_cpi = 3.5;
  localparam real br_not_taken_max_cpi = 3.0;
  localparam real load_use_max_cpi = 3.0;
  localparam real mixed_alu_max_cpi = 3.3;
  localparam real fib12_max_cpi = 1.7;
  localparam real fib100_max_cpi = 1.7;
  localparam real bubble_max_cpi = 2.5;
  logic ebreak;

  svc_rv_soc_sram #(
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (1),
      .FWD_REGFILE(0)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .io_raddr(),
      .io_rdata(),

      .io_wen  (),
      .io_waddr(),
      .io_wdata(),
      .io_wstrb(),

      .ebreak(ebreak)
  );

  `include "svc_rv_soc_test_defs.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_pipelined_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
