`ifndef SVC_RV_EXT_MUL_MEM_SV
`define SVC_RV_EXT_MUL_MEM_SV

`include "svc.sv"

//
// RISC-V multiply MEM stage
//
// Combines partial products from EX stage to compute final multiply result.
// Also handles division results pass-through.
//
// Input: 4x 32-bit partial products from 16x16 multiplies (from EX stage)
// Output: Final 32-bit multiply result
//
module svc_rv_ext_mul_mem (
    //
    // Partial products from EX stage (for multiply)
    //
    input logic [31:0] mul_ll,
    input logic [31:0] mul_lh,
    input logic [31:0] mul_hl,
    input logic [31:0] mul_hh,

    //
    // Division result from EX stage (pass-through)
    //
    input logic [31:0] div_result,

    //
    // Combined product output (unsigned, before sign correction)
    //
    output logic [63:0] product_64
);

  //
  // Multiply result computation
  //
  // Combine partial products using VexRiscv algorithm:
  //   mid_sum = lh + hl (33 bits with carry)
  //   product = {(hh || ll[31:16]) + mid_sum, ll[15:0]}
  //
  // This produces an unsigned 64-bit product.
  // Sign correction is applied in WB stage for better timing.
  //
  logic [32:0] mid_sum;

  assign mid_sum = {1'b0, mul_lh} + {1'b0, mul_hl};

  assign product_64 = {
    ({mul_hh, mul_ll[31:16]} + {{15{1'b0}}, mid_sum}), mul_ll[15:0]
  };

  //
  // Note: div_result is unused here - division results are handled separately
  //
  logic unused_div_result;
  assign unused_div_result = |div_result;

endmodule

`endif
