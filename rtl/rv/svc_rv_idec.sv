`ifndef SVC_RV_IDEC_SV
`define SVC_RV_IDEC_SV

`include "svc.sv"

//
// RISC-V instruction decoder
//
// Decodes 32-bit RISC-V instructions into control signals and extracts
// instruction fields. Supports load, store, R-type, I-type, B-type, J-type,
// and U-type instructions (LW, SW, ADD, BEQ, ADDI, JAL, JALR, AUIPC, LUI).
//
// The decoder is purely combinational. Control signal constants are provided
// as localparams that callers can access hierarchically (e.g., idec_i.IMM_I).
//
// Design note: The ALU decode logic is separated into svc_rv_alu_dec to keep
// this module's combinational depth manageable and allow flexibility in
// pipeline placement for timing closure.
//
module svc_rv_idec #(
    parameter int XLEN = 32
) (
    input logic [31:0] instr,

    output logic       reg_write,
    output logic       mem_write,
    output logic       alu_a_src,
    output logic [1:0] alu_b_src,
    output logic [1:0] alu_instr,
    output logic [1:0] res_src,
    output logic [2:0] imm_type,
    output logic       is_branch,
    output logic       is_jump,

    output logic [4:0] rd,
    output logic [4:0] rs1,
    output logic [4:0] rs2,
    output logic [2:0] funct3,
    output logic [6:0] funct7,

    output logic [XLEN-1:0] imm_i,
    output logic [XLEN-1:0] imm_s,
    output logic [XLEN-1:0] imm_b,
    output logic [XLEN-1:0] imm_u,
    output logic [XLEN-1:0] imm_j
);
  //
  // Control signal constants
  //
  `include "svc_rv_defs.svh"

  logic [6:0] opcode;

  // Extract instruction fields
  assign opcode = instr[6:0];
  assign rd     = instr[11:7];
  assign rs1    = instr[19:15];
  assign rs2    = instr[24:20];
  assign funct3 = instr[14:12];
  assign funct7 = instr[31:25];

  //
  // Control signal decoder
  //
  always_comb begin
    logic [13:0] c;

    case (opcode)
      OP_LOAD:   c = 14'b1_0_0_01_00_01_000_0_0;
      OP_STORE:  c = 14'b0_1_0_01_00_00_001_0_0;
      OP_RTYPE:  c = 14'b1_0_0_00_10_00_xxx_0_0;
      OP_BRANCH: c = 14'b0_0_0_00_01_00_010_1_0;
      OP_ITYPE:  c = 14'b1_0_0_01_10_00_000_0_0;
      OP_JAL:    c = 14'b1_0_0_00_00_10_011_0_1;
      OP_AUIPC:  c = 14'b1_0_1_10_00_00_100_0_0;
      OP_LUI:    c = 14'b1_0_1_01_00_00_100_0_0;
      OP_JALR:   c = 14'b1_0_0_01_00_10_000_0_1;
      OP_SYSTEM: c = 14'b0_0_0_00_00_00_000_0_0;
      OP_RESET:  c = 14'b0_0_0_00_00_00_000_0_0;
      default:   c = 14'bx_x_x_xx_xx_xx_xxx_x_x;
    endcase

    {reg_write, mem_write, alu_a_src, alu_b_src, alu_instr, res_src, imm_type,
     is_branch, is_jump} = c;
  end

  // Extract immediates
  assign imm_i = {{(XLEN - 12) {instr[31]}}, instr[31:20]};
  assign imm_s = {{(XLEN - 12) {instr[31]}}, instr[31:25], instr[11:7]};
  assign imm_u = {{instr[31:12]}, 12'b0};

  assign imm_b = {
    {(XLEN - 13) {instr[31]}},
    instr[31],
    instr[7],
    instr[30:25],
    instr[11:8],
    1'b0
  };

  assign imm_j = {
    {(XLEN - 21) {instr[31]}},
    instr[31],
    instr[19:12],
    instr[20],
    instr[30:21],
    1'b0
  };

endmodule

`endif
