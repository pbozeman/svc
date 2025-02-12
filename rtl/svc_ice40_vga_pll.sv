`ifndef SVC_ICE40_VGA_PLL_SV
`define SVC_ICE40_VGA_PLL_SV

`include "svc.sv"
`include "svc_ice40_vga_mode.sv"

// verilator lint_off UNUSEDSIGNAL
// verilator lint_off UNDRIVEN
module svc_ice40_vga_pll (
    input  logic clk_i,
    output logic clk_o
);
`ifndef VERILATOR
  logic pll_lock;

  // An intermediate clock to pass to a GB is not necessary because this is
  // using PLLOUTGLOBAL, which already puts the signal on a global buffer

  SB_PLL40_CORE #(
      .FEEDBACK_PATH("SIMPLE"),
      .DIVR         (`VGA_MODE_PLL_DIVR),
      .DIVF         (`VGA_MODE_PLL_DIVF),
      .DIVQ         (`VGA_MODE_PLL_DIVQ),
      .FILTER_RANGE (`VGA_MODE_PLL_FILTER_RANGE)
  ) pll_inst (
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
