`include "svc_unit.sv"

`include "svc_rv_soc_bram.sv"

module svc_rv_soc_bram_bpred_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;

  //
  // CPI expectations with BRAM memories and branch prediction
  //
  // With predictor enabled, expect improved CPI on branch-heavy workloads
  //
  localparam real alu_indep_max_cpi = 1.5;
  localparam real alu_chain_max_cpi = 2.9;
  localparam real br_taken_max_cpi = 3.5;
  localparam real br_not_taken_max_cpi = 2.8;
  localparam real load_use_max_cpi = 2.8;
  localparam real mixed_alu_max_cpi = 2.7;
  localparam real fib12_max_cpi = 1.7;
  localparam real fib100_max_cpi = 1.7;
  localparam real bubble_max_cpi = 2.2;
  logic ebreak;

  svc_rv_soc_bram #(
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
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
  `TEST_SUITE_BEGIN(svc_rv_soc_bram_bpred_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
