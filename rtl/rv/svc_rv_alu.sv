`ifndef SVC_RV_ALU_SV
`define SVC_RV_ALU_SV

`include "svc.sv"

//
// RISC-V ALU
//
// Arithmetic Logic Unit supporting standard RV32I operations:
// - ADD, SUB: Addition and subtraction
// - AND, OR, XOR: Bitwise logical operations
// - SLT, SLTU: Set less than (signed and unsigned comparison)
// - SLL, SRL, SRA: Logical and arithmetic shifts
//
// The ALU is purely combinational. The alu_op input is expected to come from
// svc_rv_alu_dec, which decodes the instruction type, funct3, and funct7_b5
// fields.
//
module svc_rv_alu #(
    parameter int XLEN = 32
) (
    input  logic [XLEN-1:0] a,
    input  logic [XLEN-1:0] b,
    input  logic [     3:0] alu_op,
    output logic [XLEN-1:0] result
);
  `include "svc_rv_defs.svh"

  logic [4:0] shamt;

  //
  // Extract shift amount
  //
  assign shamt = b[4:0];

  //
  // Combinational ALU operations
  //
  always_comb begin
    case (alu_op)
      ALU_ADD:  result = a + b;
      ALU_SUB:  result = a - b;
      ALU_AND:  result = a & b;
      ALU_OR:   result = a | b;
      ALU_XOR:  result = a ^ b;
      ALU_SLT:  result = {{(XLEN - 1) {1'b0}}, ($signed(a) < $signed(b))};
      ALU_SLTU: result = {{(XLEN - 1) {1'b0}}, (a < b)};
      ALU_SLL:  result = a << shamt;
      ALU_SRL:  result = a >> shamt;
      ALU_SRA:  result = $unsigned($signed(a) >>> shamt);
      default:  result = {XLEN{1'bx}};
    endcase
  end

endmodule

`endif
