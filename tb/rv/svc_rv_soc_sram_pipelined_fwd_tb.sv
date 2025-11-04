`include "svc_unit.sv"

`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_pipelined_fwd_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;

  //
  // CPI expectations with MEM->EX forwarding enabled
  //
  // With forwarding, EX and MEM hazards are handled without stalling.
  // Expected major improvements in ALU chain and mixed ALU workloads.
  //
  // Note: Branch penalties (2 cycles for taken branches) are unavoidable
  // without branch prediction, so workloads with many branches will still
  // show elevated CPI even with perfect data forwarding.
  //
  // CPI expectations with forwarding enabled
  //
  localparam real alu_indep_max_cpi = 1.35;
  localparam real alu_chain_max_cpi = 1.5;
  localparam real br_taken_max_cpi = 3.0;
  localparam real br_not_taken_max_cpi = 2.5;
  localparam real load_use_max_cpi = 2.5;
  localparam real mixed_alu_max_cpi = 1.45;
  localparam real fib12_max_cpi = 1.37;
  localparam real bubble_max_cpi = 1.5;
  logic ebreak;

  svc_rv_soc_sram #(
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (1)
  ) uut (
      .clk   (clk),
      .rst_n (rst_n),
      .ebreak(ebreak)
  );

  `include "svc_rv_soc_test_defs.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_pipelined_fwd_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
