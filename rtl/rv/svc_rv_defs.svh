//
// RISC-V shared definitions
//
// Common constants used across RISC-V modules.
//
// Design note: SystemVerilog packages would be the preferred approach for
// sharing constants, but we avoid them due to inconsistent tool support. Yosys
// open-source has limited package support, requiring plugins or commercial
// frontends for full functionality.
//
// Instead, we include this file directly inside module bodies, which scopes
// the localparams to each module. This approach allows us to use simple names
// (e.g., ALU_ADD) without SVC_RV prefixing while avoiding global namespace
// pollution. No include guard is used since each module gets its own scoped
// copy of the constants.
//
// verilog_format: off
// verilator lint_off UNUSEDPARAM

//
// Memory type values
//
localparam int MEM_TYPE_SRAM       = 0;
localparam int MEM_TYPE_BRAM       = 1;
localparam int MEM_TYPE_BRAM_CACHE = 2;

//
// PC selection values
//
localparam logic [1:0] PC_SEL_SEQUENTIAL = 2'b00;
localparam logic [1:0] PC_SEL_PREDICTED  = 2'b01;
localparam logic [1:0] PC_SEL_REDIRECT   = 2'b10;

// ALU operation constants
//
// alu_op values
localparam logic [3:0] ALU_ADD  = 4'b0000;
localparam logic [3:0] ALU_SUB  = 4'b0001;
localparam logic [3:0] ALU_AND  = 4'b0010;
localparam logic [3:0] ALU_OR   = 4'b0011;
localparam logic [3:0] ALU_XOR  = 4'b0100;
localparam logic [3:0] ALU_SLT  = 4'b0101;
localparam logic [3:0] ALU_SLTU = 4'b0110;
localparam logic [3:0] ALU_SLL  = 4'b0111;
localparam logic [3:0] ALU_SRL  = 4'b1000;
localparam logic [3:0] ALU_SRA  = 4'b1001;

//
// Branch comparison funct3 values
//
localparam logic [2:0] FUNCT3_BEQ  = 3'b000;
localparam logic [2:0] FUNCT3_BNE  = 3'b001;
localparam logic [2:0] FUNCT3_BLT  = 3'b100;
localparam logic [2:0] FUNCT3_BGE  = 3'b101;
localparam logic [2:0] FUNCT3_BLTU = 3'b110;
localparam logic [2:0] FUNCT3_BGEU = 3'b111;

//
// Load funct3 values
//
localparam logic [2:0] FUNCT3_LB  = 3'b000;
localparam logic [2:0] FUNCT3_LH  = 3'b001;
localparam logic [2:0] FUNCT3_LW  = 3'b010;
localparam logic [2:0] FUNCT3_LBU = 3'b100;
localparam logic [2:0] FUNCT3_LHU = 3'b101;

//
// Store funct3 values
//
localparam logic [2:0] FUNCT3_SB = 3'b000;
localparam logic [2:0] FUNCT3_SH = 3'b001;
localparam logic [2:0] FUNCT3_SW = 3'b010;

//
// CSR instruction funct3 values
//
localparam logic [2:0] FUNCT3_CSRRW  = 3'b001;
localparam logic [2:0] FUNCT3_CSRRS  = 3'b010;
localparam logic [2:0] FUNCT3_CSRRC  = 3'b011;
localparam logic [2:0] FUNCT3_CSRRWI = 3'b101;
localparam logic [2:0] FUNCT3_CSRRSI = 3'b110;
localparam logic [2:0] FUNCT3_CSRRCI = 3'b111;

//
// CSR addresses (Zicntr - Base Counters and Timers)
//
localparam logic [11:0] CSR_CYCLE    = 12'hC00;
localparam logic [11:0] CSR_CYCLEH   = 12'hC80;
localparam logic [11:0] CSR_INSTRET  = 12'hC02;
localparam logic [11:0] CSR_INSTRETH = 12'hC82;

//
// CSR addresses (RV32F - Floating-Point)
//
localparam logic [11:0] CSR_FFLAGS = 12'h001;
localparam logic [11:0] CSR_FRM    = 12'h002;
localparam logic [11:0] CSR_FCSR   = 12'h003;

//
// Instruction decoder control signal constants
//
// alu_a_src values
localparam logic [1:0] ALU_A_RS1  = 2'b00;
localparam logic [1:0] ALU_A_ZERO = 2'b01;
localparam logic [1:0] ALU_A_PC   = 2'b10;

// alu_b_src values
localparam logic ALU_B_RS2 = 1'b0;
localparam logic ALU_B_IMM = 1'b1;

// alu_instr values
localparam logic [1:0] ALU_INSTR_ADD = 2'b00;
localparam logic [1:0] ALU_INSTR_SUB = 2'b01;
localparam logic [1:0] ALU_INSTR_FN3 = 2'b10;

// res_src values
localparam logic [2:0] RES_ALU = 3'b000;
localparam logic [2:0] RES_MEM = 3'b001;
localparam logic [2:0] RES_PC4 = 3'b010;
localparam logic [2:0] RES_TGT = 3'b011;
localparam logic [2:0] RES_CSR = 3'b100;
localparam logic [2:0] RES_M   = 3'b101;
localparam logic [2:0] RES_FP  = 3'b110;

// imm_type values
localparam logic [2:0] IMM_I = 3'b000;
localparam logic [2:0] IMM_S = 3'b001;
localparam logic [2:0] IMM_B = 3'b010;
localparam logic [2:0] IMM_J = 3'b011;
localparam logic [2:0] IMM_U = 3'b100;

// jb_tgt_src values
localparam logic JB_TARGET_PC  = 1'b0;
localparam logic JB_TARGET_ALU = 1'b1;

//
// RISC-V instruction opcodes
//
localparam logic [6:0] OP_LOAD   = 7'b0000011;
localparam logic [6:0] OP_STORE  = 7'b0100011;
localparam logic [6:0] OP_RTYPE  = 7'b0110011;
localparam logic [6:0] OP_BRANCH = 7'b1100011;
localparam logic [6:0] OP_ITYPE  = 7'b0010011;
localparam logic [6:0] OP_JAL    = 7'b1101111;
localparam logic [6:0] OP_AUIPC  = 7'b0010111;
localparam logic [6:0] OP_LUI    = 7'b0110111;
localparam logic [6:0] OP_JALR   = 7'b1100111;
localparam logic [6:0] OP_SYSTEM = 7'b1110011;
localparam logic [6:0] OP_RESET  = 7'b0000000;

//
// RV32F instruction opcodes
//
localparam logic [6:0] OP_LOAD_FP  = 7'b0000111;
localparam logic [6:0] OP_STORE_FP = 7'b0100111;
localparam logic [6:0] OP_FMADD    = 7'b1000011;
localparam logic [6:0] OP_FMSUB    = 7'b1000111;
localparam logic [6:0] OP_FNMSUB   = 7'b1001011;
localparam logic [6:0] OP_FNMADD   = 7'b1001111;
localparam logic [6:0] OP_FP       = 7'b1010011;

//
// Specific instruction encodings
//
localparam logic [31:0] I_NOP    = 32'h00000013;
localparam logic [31:0] I_ECALL  = 32'h00000073;
localparam logic [31:0] I_EBREAK = 32'h00100073;

//
// Trap type codes
//
localparam logic [1:0] TRAP_NONE            = 2'b00;
localparam logic [1:0] TRAP_INSTR_INVALID   = 2'b01;
localparam logic [1:0] TRAP_INSTR_MISALIGN  = 2'b10;
localparam logic [1:0] TRAP_LDST_MISALIGN   = 2'b11;

//
// RV32F rounding modes
//
localparam logic [2:0] FRM_RNE = 3'b000;  // Round to Nearest, ties to Even
localparam logic [2:0] FRM_RTZ = 3'b001;  // Round towards Zero
localparam logic [2:0] FRM_RDN = 3'b010;  // Round Down (-inf)
localparam logic [2:0] FRM_RUP = 3'b011;  // Round Up (+inf)
localparam logic [2:0] FRM_RMM = 3'b100;  // Round to Nearest, ties Max Magnitude
localparam logic [2:0] FRM_DYN = 3'b111;  // Dynamic (use frm CSR)

//
// RV32F funct7 values (for OP_FP opcode)
//
localparam logic [6:0] FP7_FADD    = 7'b0000000;
localparam logic [6:0] FP7_FSUB    = 7'b0000100;
localparam logic [6:0] FP7_FMUL    = 7'b0001000;
localparam logic [6:0] FP7_FDIV    = 7'b0001100;
localparam logic [6:0] FP7_FSQRT   = 7'b0101100;
localparam logic [6:0] FP7_FSGNJ   = 7'b0010000;
localparam logic [6:0] FP7_FMINMAX = 7'b0010100;
localparam logic [6:0] FP7_FCVTWS  = 7'b1100000;  // FCVT.W.S, FCVT.WU.S
localparam logic [6:0] FP7_FMVXW   = 7'b1110000;  // FMV.X.W, FCLASS.S
localparam logic [6:0] FP7_FCMP    = 7'b1010000;  // FEQ, FLT, FLE
localparam logic [6:0] FP7_FCVTSW  = 7'b1101000;  // FCVT.S.W, FCVT.S.WU
localparam logic [6:0] FP7_FMVWX   = 7'b1111000;  // FMV.W.X

//
// RV32F funct3 values
//
localparam logic [2:0] FP3_FSGNJ  = 3'b000;  // FSGNJ.S
localparam logic [2:0] FP3_FSGNJN = 3'b001;  // FSGNJN.S
localparam logic [2:0] FP3_FSGNJX = 3'b010;  // FSGNJX.S
localparam logic [2:0] FP3_FMIN   = 3'b000;  // FMIN.S
localparam logic [2:0] FP3_FMAX   = 3'b001;  // FMAX.S
localparam logic [2:0] FP3_FMV    = 3'b000;  // FMV.X.W, FMV.W.X
localparam logic [2:0] FP3_FCLASS = 3'b001;  // FCLASS.S
localparam logic [2:0] FP3_FLE    = 3'b000;  // FLE.S
localparam logic [2:0] FP3_FLT    = 3'b001;  // FLT.S
localparam logic [2:0] FP3_FEQ    = 3'b010;  // FEQ.S

// verilator lint_on UNUSEDPARAM
// verilog_format: on
