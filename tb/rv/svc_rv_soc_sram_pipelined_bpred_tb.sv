`include "svc_unit.sv"

`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_pipelined_bpred_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;

  //
  // CPI expectations with SRAM, pipelined mode, no forwarding, with branch prediction
  //
  // JAL early resolution helps, but lack of forwarding increases stalls
  //
  localparam real alu_indep_max_cpi = 1.17;
  localparam real alu_chain_max_cpi = 2.65;
  localparam real br_taken_max_cpi = 2.5;
  localparam real br_not_taken_max_cpi = 2.25;
  localparam real load_use_max_cpi = 2.25;
  localparam real mixed_alu_max_cpi = 2.45;
  localparam real fib12_max_cpi = 1.37;
  localparam real fib100_max_cpi = 1.34;
  localparam real bubble_max_cpi = 1.94;
  logic ebreak;

  svc_rv_soc_sram #(
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .FWD        (0),
      .BPRED      (1)
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
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_pipelined_bpred_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
