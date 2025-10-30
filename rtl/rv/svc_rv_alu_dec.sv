`ifndef SVC_RV_ALU_DEC_SV
`define SVC_RV_ALU_DEC_SV

`include "svc.sv"

//
// RISC-V ALU decoder
//
// Decodes the ALU instruction type, funct3, and funct7_b5 into a specific
// ALU operation. The op_b5 input (instr[5]) distinguishes R-type from I-type
// instructions, ensuring that subtract only occurs for R-type SUB, not I-type
// ADDI with bit 5 set in the immediate.
//
// Design note: This could have been merged into the instruction decoder, but
// is kept separate because it adds additional layers of combinational logic.
// Separating it allows flexibility to move it around for timing closure.
//
module svc_rv_alu_dec (
    input logic [1:0] alu_instr,
    input logic [2:0] funct3,
    input logic       funct7_b5,
    input logic       op_b5,

    output logic [3:0] alu_op
);
  `include "svc_rv_defs.svh"

  logic rtype_sub;
  assign rtype_sub = funct7_b5 & op_b5;

  //
  // Combinational ALU control decode
  //
  always_comb begin
    case (alu_instr)
      2'b00: alu_op = ALU_ADD;
      2'b01: alu_op = ALU_SUB;
      default: begin
        case (funct3)
          3'b000:  alu_op = rtype_sub ? ALU_SUB : ALU_ADD;
          3'b001:  alu_op = ALU_SLL;
          3'b010:  alu_op = ALU_SLT;
          3'b011:  alu_op = ALU_SLTU;
          3'b100:  alu_op = ALU_XOR;
          3'b101:  alu_op = funct7_b5 ? ALU_SRA : ALU_SRL;
          3'b110:  alu_op = ALU_OR;
          3'b111:  alu_op = ALU_AND;
          default: alu_op = 4'bxxxx;
        endcase
      end
    endcase
  end

endmodule

`endif
