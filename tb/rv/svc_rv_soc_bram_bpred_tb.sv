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
  // With JAL early resolution and BTFNT prediction, improved CPI
  // BRAM latency still adds overhead compared to SRAM
  //
  localparam real alu_indep_max_cpi = 1.34;
  localparam real alu_chain_max_cpi = 2.75;
  localparam real br_taken_max_cpi = 3.0;
  localparam real br_not_taken_max_cpi = 2.5;
  localparam real load_use_max_cpi = 2.5;
  localparam real mixed_alu_max_cpi = 2.56;
  localparam real fib12_max_cpi = 1.54;
  localparam real fib100_max_cpi = 1.51;
  localparam real bubble_max_cpi = 2.08;
  logic ebreak;

  svc_rv_soc_bram #(
      .IMEM_AW    (IMEM_AW),
      .DMEM_AW    (DMEM_AW),
      .PIPELINED  (1),
      .FWD_REGFILE(1),
      .BPRED      (1)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .io_ren  (),
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
  `TEST_SUITE_BEGIN(svc_rv_soc_bram_bpred_tb, 100000);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
