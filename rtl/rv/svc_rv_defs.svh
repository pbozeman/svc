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
localparam logic [1:0] RES_ALU = 2'b00;
localparam logic [1:0] RES_MEM = 2'b01;
localparam logic [1:0] RES_PC4 = 2'b10;
localparam logic [1:0] RES_TGT = 2'b11;

// imm_type values
localparam logic [2:0] IMM_I = 3'b000;
localparam logic [2:0] IMM_S = 3'b001;
localparam logic [2:0] IMM_B = 3'b010;
localparam logic [2:0] IMM_J = 3'b011;
localparam logic [2:0] IMM_U = 3'b100;

// jb_target_src values
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
// Specific instruction encodings
//
localparam logic [31:0] I_ECALL  = 32'h00000073;
localparam logic [31:0] I_EBREAK = 32'h00100073;

// verilator lint_on UNUSEDPARAM
// verilog_format: on
