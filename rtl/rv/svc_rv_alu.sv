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

  //
  // Combinational ALU operations
  //
  // verilog_format: off
  assign result = (alu_op == ALU_ADD)  ? a + b :
                  (alu_op == ALU_SUB)  ? a - b :
                  (alu_op == ALU_AND)  ? a & b :
                  (alu_op == ALU_OR)   ? a | b :
                  (alu_op == ALU_XOR)  ? a ^ b :
                  (alu_op == ALU_SLT)  ? {{(XLEN - 1) {1'b0}}, ($signed(a) < $signed(b))} :
                  (alu_op == ALU_SLTU) ? {{(XLEN - 1) {1'b0}}, (a < b)} :
                  (alu_op == ALU_SLL)  ? a << b[4:0] :
                  (alu_op == ALU_SRL)  ? a >> b[4:0] :
                  (alu_op == ALU_SRA)  ? $unsigned($signed(a) >>> b[4:0]) : {XLEN{1'bx}};
  // verilog_format: on

endmodule

`endif
