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
    parameter int XLEN,
    parameter int EXT_M
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
    output logic       is_jmp,
    output logic       jb_target_src,
    output logic       is_jal,
    output logic       is_jalr,
    output logic       is_m,
    output logic       is_csr,
    output logic       instr_invalid,

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
  assign rd     = instr[11:7];
  assign funct3 = instr[14:12];
  assign funct7 = instr[31:25];

  //
  // Extract rs1/rs2 directly from instruction
  //
  // Note: These may contain garbage when not used, but that's okay:
  // - Forwarding: Harmless to forward to unused registers (value ignored)
  // - Hazards: We check rs1_used/rs2_used to avoid false stalls
  //
  assign rs1    = instr[19:15];
  assign rs2    = instr[24:20];

  //
  // Control signal decoder
  //
  logic valid_opcode;

  always_comb begin
    logic [22:0] c;

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
      //              v  r mr mw   alu  alu  alu  res    imm  b  j    jb  jal jalr csr r1u r2u
      //                             a    b   op
      OP_LOAD:   c = {y, y, y, n,  RS1, IMM, ADD, MEM,     I, n, n,    x,   n,   n,  n,  y,  n};
      OP_STORE:  c = {y, n, n, y,  RS1, IMM, ADD, xxx,     S, n, n,    x,   n,   n,  n,  y,  y};
      OP_RTYPE:  c = {y, y, n, n,  RS1, RS2, FN3, ALU,   xxx, n, n,    x,   n,   n,  n,  y,  y};
      OP_BRANCH: c = {y, n, n, n,   xx,   x,  xx, xxx,     B, y, n,   PC,   n,   n,  n,  y,  y};
      OP_ITYPE:  c = {y, y, n, n,  RS1, IMM, FN3, ALU,     I, n, n,    x,   n,   n,  n,  y,  n};
      OP_JAL:    c = {y, y, n, n,   xx,   x,  xx, PC4,     J, n, y,   PC,   y,   n,  n,  n,  n};
      OP_AUIPC:  c = {y, y, n, n,   xx,   x,  xx, TGT,     U, n, n,   PC,   n,   n,  n,  n,  n};
      OP_LUI:    c = {y, y, n, n, ZERO, IMM, ADD, ALU,     U, n, n,    x,   n,   n,  n,  n,  n};
      OP_JALR:   c = {y, y, n, n,  RS1, IMM, ADD, PC4,     I, n, y, ALUR,   n,   y,  n,  y,  n};
      OP_SYSTEM: c = {y, y, n, n,   xx,   x,  xx, CSR,     I, n, n,    x,   n,   n,  y,  y,  n};
      OP_RESET:  c = {y, n, n, n,   xx,   x,  xx, xxx,   xxx, n, n,    x,   n,   n,  n,  n,  n};
      default:   c = {n, n, n, n,   xx,   x,  xx, xxx,   xxx, n, n,    x,   n,   n,  n,  n,  n};
    endcase

    { valid_opcode, reg_write, mem_read, mem_write,
      alu_a_src, alu_b_src, alu_instr, res_src, imm_type,
      is_branch, is_jmp, jb_target_src, is_jal, is_jalr, is_csr,
      rs1_used, rs2_used } = c;

    //
    // Override res_src for M extension instructions
    //
    if (is_m) begin
      res_src = RES_M;
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
  // M extension detection
  //
  // Valid M-extension instructions have funct7 == 7'b0000001 exactly.
  // Just checking funct7[0] would incorrectly match invalid encodings.
  //
  if (EXT_M != 0) begin : g_m_ext
    assign is_m = (opcode == OP_RTYPE) && (funct7 == 7'b0000001);
  end else begin : g_no_m_ext
    assign is_m = 1'b0;
  end

  //
  // Invalid instruction detection
  //
  logic invalid_compressed;
  logic invalid_opcode;
  logic invalid_system;

  //
  // Compressed instructions (C extension not supported)
  //
  assign invalid_compressed = (instr[1:0] != 2'b11);

  //
  // Invalid opcodes: Check valid bit from decode table
  //
  // This catches all unsupported opcodes including RV64-only instructions
  //
  assign invalid_opcode     = !valid_opcode;

  //
  // Invalid SYSTEM instructions
  //
  // Valid funct3: 000 (ECALL/EBREAK), 001-011 (CSR reg), 101-111 (CSR imm)
  // For funct3=000, only ECALL and EBREAK are supported
  //
  logic invalid_system_funct3;
  logic invalid_system_priv;

  assign invalid_system_funct3 = (funct3 == 3'b100);
  assign invalid_system_priv = ((funct3 == 3'b000) && (instr != I_ECALL) &&
                                (instr != I_EBREAK));
  assign invalid_system = ((opcode == OP_SYSTEM) &&
                           (invalid_system_funct3 | invalid_system_priv));

  //
  // Invalid M-extension instructions
  //
  // R-type instructions with funct7[0]=1 but not valid M encoding (0000001)
  // are invalid. When EXT_M=0, any such instruction is invalid. When EXT_M=1,
  // only those with incorrect funct7 are invalid.
  //
  logic invalid_m;

  if (EXT_M != 0) begin : g_invalid_m
    assign invalid_m = ((opcode == OP_RTYPE) && funct7[0] &&
                        (funct7 != 7'b0000001));
  end else begin : g_no_invalid_m
    assign invalid_m = (opcode == OP_RTYPE) && funct7[0];
  end

  assign instr_invalid = (invalid_compressed | invalid_opcode | invalid_system |
                          invalid_m);

endmodule

`endif
