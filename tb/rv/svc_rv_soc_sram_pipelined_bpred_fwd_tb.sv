`include "svc_unit.sv"

`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_pipelined_bpred_fwd_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;

  //
  // CPI expectations with SRAM, pipelined mode, forwarding, and branch prediction
  //
  // This is the most aggressive configuration with best expected CPI
  //
  localparam real alu_indep_max_cpi = 1.35;
  localparam real alu_chain_max_cpi = 1.5;
  localparam real br_taken_max_cpi = 3.0;
  localparam real br_not_taken_max_cpi = 2.5;
  localparam real load_use_max_cpi = 2.5;
  localparam real mixed_alu_max_cpi = 1.5;
  localparam real fib12_max_cpi = 1.4;
  localparam real fib100_max_cpi = 1.4;
  localparam real bubble_max_cpi = 1.5;
  logic ebreak;

  svc_rv_soc_sram #(
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1),
      .BPRED      (1)
  ) uut (
      .clk   (clk),
      .rst_n (rst_n),
      .ebreak(ebreak)
  );

  `include "svc_rv_soc_test_defs.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_pipelined_bpred_fwd_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
