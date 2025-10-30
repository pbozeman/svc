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
module svc_rv_idec #(
    parameter int XLEN = 32
) (
    input logic [31:0] instr,

    output logic       reg_write,
    output logic       mem_write,
    output logic       alu_a_src,
    output logic [1:0] alu_b_src,
    output logic [1:0] alu_op_type,
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
  // These are not used internally to keep the case statement compact, but
  // callers can access them hierarchically (e.g., idec_i.IMM_I) to make their
  // code more readable.
  //
  // verilator lint_off: UNUSEDPARAM

  // alu_a_src values
  localparam logic ALU_A_RS1 = 1'b0;
  localparam logic ALU_A_PC = 1'b1;

  // alu_b_src values
  localparam logic [1:0] ALU_B_RS2 = 2'b00;
  localparam logic [1:0] ALU_B_IMM = 2'b01;
  localparam logic [1:0] ALU_B_TGT = 2'b10;

  // alu_op_type values
  localparam logic [1:0] ALU_OP_ADD = 2'b00;
  localparam logic [1:0] ALU_OP_SUB = 2'b01;
  localparam logic [1:0] ALU_OP_FN3 = 2'b10;

  // res_src values
  localparam logic [1:0] RES_ALU = 2'b00;
  localparam logic [1:0] RES_MEM = 2'b01;
  localparam logic [1:0] RES_PC4 = 2'b10;

  // imm_type values
  localparam logic [2:0] IMM_I = 3'b000;
  localparam logic [2:0] IMM_S = 3'b001;
  localparam logic [2:0] IMM_B = 3'b010;
  localparam logic [2:0] IMM_J = 3'b011;
  localparam logic [2:0] IMM_U = 3'b100;
  // verilator lint_on: UNUSEDPARAM

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
      7'b0000011: c = 14'b1_0_0_01_00_01_000_0_0;  // lw
      7'b0100011: c = 14'b0_1_0_01_00_00_001_0_0;  // sw
      7'b0110011: c = 14'b1_0_0_00_10_00_xxx_0_0;  // R-type
      7'b1100011: c = 14'b0_0_0_00_01_00_010_1_0;  // B-type
      7'b0010011: c = 14'b1_0_0_01_10_00_000_0_0;  // I-type ALU
      7'b1101111: c = 14'b1_0_0_00_00_10_011_0_1;  // jal
      7'b0010111: c = 14'b1_0_1_10_00_00_100_0_0;  // auipc
      7'b0110111: c = 14'b1_0_1_01_00_00_100_0_0;  // lui
      7'b1100111: c = 14'b1_0_0_01_00_10_000_0_1;  // jalr
      7'b0000000: c = 14'b0_0_0_00_00_00_000_0_0;  // during reset
      default:    c = 14'bx_x_x_xx_xx_xx_xxx_x_x;
    endcase

    {reg_write, mem_write, alu_a_src, alu_b_src, alu_op_type, res_src, imm_type,
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
