`include "svc_unit.sv"

`include "svc_rv_soc_sram.sv"

module svc_rv_soc_sram_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  localparam int DMEM_AW = 10;
  logic ebreak;

  svc_rv_soc_sram #(
      .IMEM_AW   (IMEM_AW),
      .DMEM_AW   (DMEM_AW),
      .IF_ID_REG (0),
      .ID_EX_REG (0),
      .EX_MEM_REG(0),
      .MEM_WB_REG(0)
  ) uut (
      .clk   (clk),
      .rst_n (rst_n),
      .ebreak(ebreak)
  );

  `include "svc_rv_soc_test_defs.svh"

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_soc_sram_tb);
  `include "svc_rv_soc_test_list.svh"
  `TEST_SUITE_END();

endmodule
