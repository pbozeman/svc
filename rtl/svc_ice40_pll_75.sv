`ifndef SVC_ICE40_PLL_75_SV
`define SVC_ICE40_PLL_75_SV

`include "svc.sv"

`define PLL_DIVR (4'd0)
`define PLL_DIVF (7'd5)
`define PLL_DIVQ (3'd3)
`define PLL_FILTER_RANGE (3'd5)

// verilator lint_off UNUSEDSIGNAL
// verilator lint_off UNDRIVEN
module svc_ice40_pll_75 (
    input  logic clk_i,
    output logic clk_o
);
`ifndef VERILATOR
  logic pll_lock;

  SB_PLL40_CORE #(
      .FEEDBACK_PATH("SIMPLE"),
      .DIVR         (`PLL_DIVR),
      .DIVF         (`PLL_DIVF),
      .DIVQ         (`PLL_DIVQ),
      .FILTER_RANGE (`PLL_FILTER_RANGE)
  ) sb_pll40_core_i (
      .LOCK        (pll_lock),
      .RESETB      (1'b1),
      .BYPASS      (1'b0),
      .REFERENCECLK(clk_i),
      .PLLOUTGLOBAL(clk_o)
  );
`endif

endmodule
// verilator lint_on UNUSEDSIGNAL
// verilator lint_on UNDRIVEN

`endif
