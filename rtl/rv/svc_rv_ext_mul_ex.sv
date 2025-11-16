`ifndef SVC_RV_EXT_MUL_EX_SV
`define SVC_RV_EXT_MUL_EX_SV

`include "svc.sv"

//
// RISC-V M extension multiply unit (EX stage)
//
// Computes 16-bit partial products for 32x32 multiplication.
// These partial products are combined in the MEM stage.
//
// This approach maps efficiently to FPGA DSP blocks (16x16 or 18x18)
// and allows the multiply to be pipelined across EX and MEM stages.
//
// Used by both ZMMUL (multiply-only) and M (multiply + divide) extensions.
//
// Operation encoding (matches funct3):
//   000 (MUL):    Lower 32 bits of rs1 * rs2 (signed × signed)
//   001 (MULH):   Upper 32 bits of rs1 * rs2 (signed × signed)
//   010 (MULHSU): Upper 32 bits of rs1 * rs2 (signed × unsigned)
//   011 (MULHU):  Upper 32 bits of rs1 * rs2 (unsigned × unsigned)
//
module svc_rv_ext_mul_ex (
    input  logic [31:0] rs1,
    input  logic [31:0] rs2,
    input  logic [ 2:0] op,
    output logic [31:0] mul_ll,
    output logic [31:0] mul_lh,
    output logic [31:0] mul_hl,
    output logic [31:0] mul_hh
);

  //
  // Split operands into 16-bit halves
  //
  logic [15:0] rs1_low;
  logic [15:0] rs1_high;
  logic [15:0] rs2_low;
  logic [15:0] rs2_high;

  assign rs1_low  = rs1[15:0];
  assign rs1_high = rs1[31:16];
  assign rs2_low  = rs2[15:0];
  assign rs2_high = rs2[31:16];

  //
  // Compute 4x 16-bit unsigned partial products
  //
  // Each 16x16 multiply produces a full 32-bit result
  //
  assign mul_ll   = rs1_low * rs2_low;
  assign mul_lh   = rs1_low * rs2_high;
  assign mul_hl   = rs1_high * rs2_low;
  assign mul_hh   = rs1_high * rs2_high;

  //
  // Note: op is unused here - operation type is used in MEM stage
  // for sign correction and result selection
  //
  logic unused_op;
  assign unused_op = |op;

endmodule

`endif
