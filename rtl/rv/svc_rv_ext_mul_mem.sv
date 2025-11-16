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
    // Original operands for sign correction
    //
    input logic [31:0] rs1_data,
    input logic [31:0] rs2_data,

    //
    // Operation type
    //
    input logic [2:0] op,

    //
    // Final result
    //
    output logic [31:0] result
);

  //
  // Operation type decode
  //
  logic is_mul;

  assign is_mul = !op[2];

  //
  // Multiply result computation
  //
  // Combine partial products using VexRiscv algorithm:
  //   mid_sum = lh + hl (33 bits with carry)
  //   product = {(hh || ll[31:16]) + mid_sum, ll[15:0]}
  //
  logic [32:0] mid_sum;
  logic [63:0] product_64;
  logic [31:0] mul_result;

  assign mid_sum = {1'b0, mul_lh} + {1'b0, mul_hl};

  assign product_64 = {
    ({mul_hh, mul_ll[31:16]} + {{15{1'b0}}, mid_sum}), mul_ll[15:0]
  };

  //
  // Sign correction for MULH/MULHSU/MULHU (VexRiscv algorithm)
  //
  // For signed multiplication of the upper bits, we need correction terms:
  //   correction_a = (rs1_signed && rs1[31]) ? rs2 : 0
  //   correction_b = (rs2_signed && rs2[31]) ? rs1 : 0
  //   corrected_result = product[63:32] - correction_a - correction_b
  //
  // Operation encoding:
  //   00 (MUL):    Lower 32 bits (no correction needed)
  //   01 (MULH):   Upper 32 bits, signed × signed
  //   10 (MULHSU): Upper 32 bits, signed × unsigned
  //   11 (MULHU):  Upper 32 bits, unsigned × unsigned
  //
  logic        rs1_signed;
  logic        rs2_signed;
  logic [31:0] correction_a;
  logic [31:0] correction_b;
  logic [31:0] product_upper_corrected;

  assign rs1_signed = (op[1:0] == 2'b01) || (op[1:0] == 2'b10);
  assign rs2_signed = (op[1:0] == 2'b01);

  assign correction_a = (rs1_signed && rs1_data[31]) ? rs2_data : 32'h0;
  assign correction_b = (rs2_signed && rs2_data[31]) ? rs1_data : 32'h0;

  assign
      product_upper_corrected = product_64[63:32] - correction_a - correction_b;

  //
  // Select result based on operation
  //
  // MUL (op[1:0] == 2'b00): Lower 32 bits
  // MULH* (op[1:0] != 2'b00): Upper 32 bits with sign correction
  //
  assign mul_result = (op[1:0] == 2'b00) ? product_64[31:0] :
      product_upper_corrected;

  //
  // Output selection: multiply result or division result
  //
  assign result = is_mul ? mul_result : div_result;

endmodule

`endif
