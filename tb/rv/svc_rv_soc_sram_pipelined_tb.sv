`include "svc_unit.sv"

`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_pipelined_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;

  // These cpi are terrible, but these are our current cpi. Aside from
  // optimizations like branch prediction, there are currently 2 design issues
  // that need to be addressed. 1) We have WB hazards that could be addressed by
  // forwarding within the reg file. 2) We are overly conservative with rs2 in
  // the hazard unit because it doesn't know the difference between rs2
  // conflicts and immediate. Also, we don't have forwarding in general yet
  // because it synthesizes poorly on lattice fpga.
  localparam real alu_indep_max_cpi = 2.0;
  localparam real alu_chain_max_cpi = 3.5;
  localparam real br_taken_max_cpi = 3.5;
  localparam real br_not_taken_max_cpi = 3.5;
  localparam real load_use_max_cpi = 3.1;
  localparam real mixed_alu_max_cpi = 3.5;
  localparam real fib12_max_cpi = 2.2;
  localparam real bubble_max_cpi = 2.5;
  logic ebreak;

  svc_rv_soc_sram #(
      .IMEM_AW   (IMEM_AW),
      .DMEM_AW   (DMEM_AW),
      .IF_ID_REG (1),
      .ID_EX_REG (1),
      .EX_MEM_REG(1),
      .MEM_WB_REG(1)
  ) uut (
      .clk   (clk),
      .rst_n (rst_n),
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
