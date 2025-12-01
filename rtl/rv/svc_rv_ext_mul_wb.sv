`ifndef SVC_RV_EXT_MUL_WB_SV
`define SVC_RV_EXT_MUL_WB_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V multiply WB stage
//
// Applies sign correction to multiply result (VexRiscv algorithm).
// This is done in WB stage to improve timing.
//
// For unsigned multiplication, the 64-bit product from MEM stage is correct.
// For signed multiplication, correction terms must be subtracted from upper bits.
//
// Operation encoding (matches funct3):
//   000 (MUL):    Lower 32 bits (no correction needed)
//   001 (MULH):   Upper 32 bits, signed × signed
//   010 (MULHSU): Upper 32 bits, signed × unsigned
//   011 (MULHU):  Upper 32 bits, unsigned × unsigned
//
module svc_rv_ext_mul_wb (
    input  logic [63:0] product_64,
    input  logic [31:0] rs1_data,
    input  logic [31:0] rs2_data,
    input  logic [ 2:0] op,
    output logic [31:0] result
);

  //
  // Sign correction for MULH/MULHSU/MULHU (VexRiscv algorithm)
  //
  // For signed multiplication of the upper bits, we need correction terms:
  //   correction_a = (rs1_signed && rs1[31]) ? rs2 : 0
  //   correction_b = (rs2_signed && rs2[31]) ? rs1 : 0
  //   corrected_result = product[63:32] - correction_a - correction_b
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

  assign product_upper_corrected = (product_64[63:32] - correction_a -
                                    correction_b);

  //
  // Select result based on operation
  //
  // MUL (op[1:0] == 2'b00): Lower 32 bits
  // MULH* (op[1:0] != 2'b00): Upper 32 bits with sign correction
  //
`ifndef RISCV_FORMAL_ALTOPS
  assign result = ((op[1:0] == 2'b00) ? product_64[31:0] :
                   product_upper_corrected);

  `SVC_UNUSED({op[2]});
`else
  //
  // RISCV_FORMAL_ALTOPS: Alternative operations for formal verification.
  //
  // Multiplication is beyond practical capabilities of hardware model
  // checkers. riscv-formal defines alternative operations using simple
  // add/sub + XOR to verify bypassing and pipeline behavior.
  //
  // See: https://yosyshq.readthedocs.io/projects/riscv-formal/en/latest/rvfi.html#alternative-arithmetic-operations
  //
  logic [31:0] altops_result;
  logic [ 1:0] op_sel;
  assign op_sel = op[1:0];

  always_comb begin
    case (op_sel)
      2'b00:   altops_result = (rs1_data + rs2_data) ^ 32'h5876063e;
      2'b01:   altops_result = (rs1_data + rs2_data) ^ 32'hf6583fb7;
      2'b10:   altops_result = (rs1_data - rs2_data) ^ 32'hecfbe137;
      2'b11:   altops_result = (rs1_data + rs2_data) ^ 32'h949ce5e8;
      default: altops_result = '0;
    endcase
  end

  assign result = altops_result;

  `SVC_UNUSED({op[2], product_64, product_upper_corrected});
`endif

endmodule

`endif
