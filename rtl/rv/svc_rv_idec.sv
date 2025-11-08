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
    parameter int XLEN      = 32,
    parameter int EXT_ZMMUL = 0
) (
    input logic [31:0] instr,

    output logic       reg_write,
    output logic       mem_read,
    output logic       mem_write,
    output logic [1:0] alu_a_src,
    output logic       alu_b_src,
    output logic [1:0] alu_instr,
    output logic [2:0] res_src,
    output logic [2:0] imm_type,
    output logic       is_branch,
    output logic       is_jump,
    output logic       jb_target_src,
    output logic       is_zmmul,

    output logic [4:0] rd,
    output logic [4:0] rs1,
    output logic [4:0] rs2,
    output logic [2:0] funct3,
    output logic [6:0] funct7,

    output logic rs1_used,
    output logic rs2_used,

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

  //
  // Extract instruction fields
  //
  assign opcode = instr[6:0];
  assign rd = instr[11:7];
  assign funct3 = instr[14:12];
  assign funct7 = instr[31:25];

  //
  // Extract rs1/rs2 directly from instruction
  //
  // Note: These may contain garbage when not used, but that's okay:
  // - Forwarding: Harmless to forward to unused registers (value ignored)
  // - Hazards: We check rs1_used/rs2_used to avoid false stalls
  //
  assign rs1 = instr[19:15];
  assign rs2 = instr[24:20];

  //
  // Fast decode of register usage from opcode
  //
  // Used by hazard unit to avoid stalling on false dependencies.
  // Not needed for forwarding since forwarding to unused registers is harmless.
  //
  // rs1 NOT used: JAL, AUIPC, LUI, RESET
  // rs2 NOT used: everything except STORE, RTYPE, BRANCH
  //
  assign rs1_used = !(opcode == OP_JAL || opcode == OP_AUIPC ||
                      opcode == OP_LUI || opcode == OP_RESET);

  assign rs2_used = (opcode == OP_STORE || opcode == OP_RTYPE ||
                     opcode == OP_BRANCH);

  //
  // Control signal decoder
  //
  always_comb begin
    logic [16:0] c;

    //
    // Short aliases for decode table
    //
    // Yes, these are a bit weird, but it makes it very easy to interpret the
    // table in a quick glance without having to decode binary. It is also hard
    // to see the big picture if each of the control signals is explicitly set
    // in the case statement.
    //
    // verilog_format: off
    localparam logic       y    = 1'b1;
    localparam logic       n    = 1'b0;

    localparam logic       x    = 1'bx;
    localparam logic [1:0] xx   = 2'bxx;
    localparam logic [2:0] xxx  = 3'bxxx;

    localparam logic [1:0] RS1  = ALU_A_RS1;
    localparam logic [1:0] ZERO = ALU_A_ZERO;

    localparam logic       RS2  = ALU_B_RS2;
    localparam logic       IMM  = ALU_B_IMM;

    localparam logic [1:0] ADD = ALU_INSTR_ADD;
    localparam logic [1:0] FN3 = ALU_INSTR_FN3;

    localparam logic [2:0] ALU  = RES_ALU;
    localparam logic [2:0] MEM  = RES_MEM;
    localparam logic [2:0] PC4  = RES_PC4;
    localparam logic [2:0] TGT  = RES_TGT;
    localparam logic [2:0] CSR  = RES_CSR;

    localparam logic [2:0] I    = IMM_I;
    localparam logic [2:0] S    = IMM_S;
    localparam logic [2:0] B    = IMM_B;
    localparam logic [2:0] J    = IMM_J;
    localparam logic [2:0] U    = IMM_U;

    localparam logic       PC   = JB_TARGET_PC;
    localparam logic       ALUR = JB_TARGET_ALU;

    //
    // Control signal decode
    //
    case (opcode)
      //              r mr mw   alu  alu  alu  res    imm  b  j    jb
      //                          a    b   op
      OP_LOAD:   c = {y, y, n,  RS1, IMM, ADD, MEM,     I, n, n,    x};
      OP_STORE:  c = {n, n, y,  RS1, IMM, ADD, xxx,     S, n, n,    x};
      OP_RTYPE:  c = {y, n, n,  RS1, RS2, FN3, ALU,   xxx, n, n,    x};
      OP_BRANCH: c = {n, n, n,   xx,   x,  xx, xxx,     B, y, n,   PC};
      OP_ITYPE:  c = {y, n, n,  RS1, IMM, FN3, ALU,     I, n, n,    x};
      OP_JAL:    c = {y, n, n,   xx,   x,  xx, PC4,     J, n, y,   PC};
      OP_AUIPC:  c = {y, n, n,   xx,   x,  xx, TGT,     U, n, n,   PC};
      OP_LUI:    c = {y, n, n, ZERO, IMM, ADD, ALU,     U, n, n,    x};
      OP_JALR:   c = {y, n, n,  RS1, IMM, ADD, PC4,     I, n, y, ALUR};
      OP_SYSTEM: c = {y, n, n,   xx,   x,  xx, CSR,     I, n, n,    x};
      OP_RESET:  c = {n, n, n,   xx,   x,  xx, xxx,   xxx, n, n,    x};
      default:   c = {x, x, x,   xx,   x,  xx, xxx,   xxx, x, x,    x};
    endcase

    { reg_write, mem_read, mem_write,
      alu_a_src, alu_b_src, alu_instr,
      res_src, imm_type, is_branch, is_jump, jb_target_src } = c;

    //
    // Override res_src for Zmmul instructions
    //
    if (is_zmmul) begin
      res_src = RES_ZMMUL;
    end

  end

  // Extract immediates
  assign imm_i = {{(XLEN - 12) {instr[31]}}, instr[31:20]};
  assign imm_s = {{(XLEN - 12) {instr[31]}}, instr[31:25], instr[11:7]};
  assign imm_u = {{instr[31:12]}, 12'b0};

  assign imm_b = {
    {(XLEN - 13) {instr[31]}},
    instr[31], instr[7], instr[30:25], instr[11:8], 1'b0
  };

  assign imm_j = {
    {(XLEN - 21) {instr[31]}},
    instr[31], instr[19:12], instr[20], instr[30:21], 1'b0
  };
  // verilog_format: on

  //
  // Zmmul extension detection
  //
  // Zmmul instructions are R-type with funct7[0] = 1
  //
  if (EXT_ZMMUL != 0) begin : g_zmmul
    assign is_zmmul = (opcode == OP_RTYPE) && (funct7[0] == 1'b1);
  end else begin : g_no_zmmul
    assign is_zmmul = 1'b0;
  end

endmodule

`endif
