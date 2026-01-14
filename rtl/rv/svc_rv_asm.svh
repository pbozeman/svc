`ifndef SVC_RV_ASM_SVH
`define SVC_RV_ASM_SVH

// RISC-V RV32I Assembly Helper for Testbenches
//
// Provides tasks to generate RISC-V machine code instructions in memory
// for simulation and testing purposes.
//
// Usage in testbench:
//   logic [31:0] MEM[0:1023];
//   `include "ipu_rv_asm.svh"
//   initial begin
//     ADDI(x1, x0, 42);
//     ADD(x2, x1, x1);
//   end
//
// Based on FemtoRV's riscv_assembly.v by Bruno Levy
// Adapted for IPU project and SystemVerilog
//
// Reference: RISC-V Unprivileged ISA Specification
// https://docs.riscv.org/reference/isa/_attachments/riscv-unprivileged.pdf
//
// verilator lint_off UNUSEDSIGNAL

// Program counter for assembly - points to next instruction address
integer asm_pc;
initial asm_pc = 0;

//-----------------------------------------------------------------------------
// Register names (architectural)
//-----------------------------------------------------------------------------

localparam bit [4:0] x0 = 0;
localparam bit [4:0] x1 = 1;
localparam bit [4:0] x2 = 2;
localparam bit [4:0] x3 = 3;
localparam bit [4:0] x4 = 4;
localparam bit [4:0] x5 = 5;
localparam bit [4:0] x6 = 6;
localparam bit [4:0] x7 = 7;
localparam bit [4:0] x8 = 8;
localparam bit [4:0] x9 = 9;
localparam bit [4:0] x10 = 10;
localparam bit [4:0] x11 = 11;
localparam bit [4:0] x12 = 12;
localparam bit [4:0] x13 = 13;
localparam bit [4:0] x14 = 14;
localparam bit [4:0] x15 = 15;
localparam bit [4:0] x16 = 16;
localparam bit [4:0] x17 = 17;
localparam bit [4:0] x18 = 18;
localparam bit [4:0] x19 = 19;
localparam bit [4:0] x20 = 20;
localparam bit [4:0] x21 = 21;
localparam bit [4:0] x22 = 22;
localparam bit [4:0] x23 = 23;
localparam bit [4:0] x24 = 24;
localparam bit [4:0] x25 = 25;
localparam bit [4:0] x26 = 26;
localparam bit [4:0] x27 = 27;
localparam bit [4:0] x28 = 28;
localparam bit [4:0] x29 = 29;
localparam bit [4:0] x30 = 30;
localparam bit [4:0] x31 = 31;

// ABI register names
// verilator lint_off UNUSEDPARAM
localparam bit [4:0] zero = x0;
localparam bit [4:0] ra = x1;
localparam bit [4:0] sp = x2;
localparam bit [4:0] gp = x3;
localparam bit [4:0] tp = x4;
localparam bit [4:0] t0 = x5;
localparam bit [4:0] t1 = x6;
localparam bit [4:0] t2 = x7;
localparam bit [4:0] fp = x8;
localparam bit [4:0] s0 = x8;
localparam bit [4:0] s1 = x9;
localparam bit [4:0] a0 = x10;
localparam bit [4:0] a1 = x11;
localparam bit [4:0] a2 = x12;
localparam bit [4:0] a3 = x13;
localparam bit [4:0] a4 = x14;
localparam bit [4:0] a5 = x15;
localparam bit [4:0] a6 = x16;
localparam bit [4:0] a7 = x17;
localparam bit [4:0] s2 = x18;
localparam bit [4:0] s3 = x19;
localparam bit [4:0] s4 = x20;
localparam bit [4:0] s5 = x21;
localparam bit [4:0] s6 = x22;
localparam bit [4:0] s7 = x23;
localparam bit [4:0] s8 = x24;
localparam bit [4:0] s9 = x25;
localparam bit [4:0] s10 = x26;
localparam bit [4:0] s11 = x27;
localparam bit [4:0] t3 = x28;
localparam bit [4:0] t4 = x29;
localparam bit [4:0] t5 = x30;
localparam bit [4:0] t6 = x31;
// verilator lint_on UNUSEDPARAM

//-----------------------------------------------------------------------------
// R-Type instructions: rd <- rs1 OP rs2
//-----------------------------------------------------------------------------

task automatic asm_r_type;
  input [6:0] opcode;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  input [2:0] funct3;
  input [6:0] funct7;
  begin
    MEM[asm_pc[11:2]] = {funct7, rs2, rs1, funct3, rd, opcode};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic ADD;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b000, 7'b0000000);
endtask

task automatic SUB;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b000, 7'b0100000);
endtask

task automatic SLL;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b001, 7'b0000000);
endtask

task automatic SLT;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b010, 7'b0000000);
endtask

task automatic SLTU;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b011, 7'b0000000);
endtask

task automatic XOR;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b100, 7'b0000000);
endtask

task automatic SRL;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b101, 7'b0000000);
endtask

task automatic SRA;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b101, 7'b0100000);
endtask

task automatic OR;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b110, 7'b0000000);
endtask

task automatic AND;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b111, 7'b0000000);
endtask

//-----------------------------------------------------------------------------
// M-Extension instructions (Multiply/Divide)
//-----------------------------------------------------------------------------

task automatic MUL;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b000, 7'b0000001);
endtask

task automatic MULH;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b001, 7'b0000001);
endtask

task automatic MULHSU;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b010, 7'b0000001);
endtask

task automatic MULHU;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b011, 7'b0000001);
endtask

task automatic DIV;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b100, 7'b0000001);
endtask

task automatic DIVU;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b101, 7'b0000001);
endtask

task automatic REM;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b110, 7'b0000001);
endtask

task automatic REMU;
  input [4:0] rd;
  input [4:0] rs1;
  input [4:0] rs2;
  asm_r_type(7'b0110011, rd, rs1, rs2, 3'b111, 7'b0000001);
endtask

//-----------------------------------------------------------------------------
// I-Type instructions: rd <- rs1 OP imm
//-----------------------------------------------------------------------------

task automatic asm_i_type;
  input [6:0] opcode;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  input [2:0] funct3;
  begin
    MEM[asm_pc[11:2]] = {imm[11:0], rs1, funct3, rd, opcode};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic ADDI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0010011, rd, rs1, imm, 3'b000);
endtask

task automatic SLTI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0010011, rd, rs1, imm, 3'b010);
endtask

task automatic SLTIU;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0010011, rd, rs1, imm, 3'b011);
endtask

task automatic XORI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0010011, rd, rs1, imm, 3'b100);
endtask

task automatic ORI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0010011, rd, rs1, imm, 3'b110);
endtask

task automatic ANDI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0010011, rd, rs1, imm, 3'b111);
endtask

// Shift immediate instructions (encoded as R-type with shamt in rs2 field)
task automatic SLLI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] shamt;
  asm_r_type(7'b0010011, rd, rs1, shamt[4:0], 3'b001, 7'b0000000);
endtask

task automatic SRLI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] shamt;
  asm_r_type(7'b0010011, rd, rs1, shamt[4:0], 3'b101, 7'b0000000);
endtask

task automatic SRAI;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] shamt;
  asm_r_type(7'b0010011, rd, rs1, shamt[4:0], 3'b101, 7'b0100000);
endtask

//-----------------------------------------------------------------------------
// Load instructions
//-----------------------------------------------------------------------------

task automatic LB;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0000011, rd, rs1, imm, 3'b000);
endtask

task automatic LH;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0000011, rd, rs1, imm, 3'b001);
endtask

task automatic LW;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0000011, rd, rs1, imm, 3'b010);
endtask

task automatic LBU;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0000011, rd, rs1, imm, 3'b100);
endtask

task automatic LHU;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b0000011, rd, rs1, imm, 3'b101);
endtask

//-----------------------------------------------------------------------------
// S-Type instructions (Store)
//-----------------------------------------------------------------------------

task automatic asm_s_type;
  input [6:0] opcode;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  input [2:0] funct3;
  begin
    MEM[asm_pc[11:2]] = {imm[11:5], rs2, rs1, funct3, imm[4:0], opcode};
    asm_pc            = asm_pc + 4;
  end
endtask

// Note: rs1 and rs2 are swapped in task arguments to match assembly syntax
task automatic SB;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_s_type(7'b0100011, rs2, rs1, imm, 3'b000);
endtask

task automatic SH;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_s_type(7'b0100011, rs2, rs1, imm, 3'b001);
endtask

task automatic SW;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_s_type(7'b0100011, rs2, rs1, imm, 3'b010);
endtask

//-----------------------------------------------------------------------------
// B-Type instructions (Branch)
//-----------------------------------------------------------------------------

task automatic asm_b_type;
  input [6:0] opcode;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  input [2:0] funct3;
  begin
    MEM[asm_pc[11:2]] = {
      imm[12], imm[10:5], rs2, rs1, funct3, imm[4:1], imm[11], opcode
    };
    asm_pc = asm_pc + 4;
  end
endtask

task automatic BEQ;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_b_type(7'b1100011, rs1, rs2, imm, 3'b000);
endtask

task automatic BNE;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_b_type(7'b1100011, rs1, rs2, imm, 3'b001);
endtask

task automatic BLT;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_b_type(7'b1100011, rs1, rs2, imm, 3'b100);
endtask

task automatic BGE;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_b_type(7'b1100011, rs1, rs2, imm, 3'b101);
endtask

task automatic BLTU;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_b_type(7'b1100011, rs1, rs2, imm, 3'b110);
endtask

task automatic BGEU;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  asm_b_type(7'b1100011, rs1, rs2, imm, 3'b111);
endtask

//-----------------------------------------------------------------------------
// U-Type instructions (LUI, AUIPC)
//-----------------------------------------------------------------------------

task automatic asm_u_type;
  input [6:0] opcode;
  input [4:0] rd;
  input [31:0] imm;
  begin
    MEM[asm_pc[11:2]] = {imm[31:12], rd, opcode};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic LUI;
  input [4:0] rd;
  input [31:0] imm;
  asm_u_type(7'b0110111, rd, imm);
endtask

task automatic AUIPC;
  input [4:0] rd;
  input [31:0] imm;
  asm_u_type(7'b0010111, rd, imm);
endtask

//-----------------------------------------------------------------------------
// J-Type instructions (JAL)
//-----------------------------------------------------------------------------

task automatic asm_j_type;
  input [6:0] opcode;
  input [4:0] rd;
  input [31:0] imm;
  begin
    MEM[asm_pc[11:2]] = {imm[20], imm[10:1], imm[11], imm[19:12], rd, opcode};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic JAL;
  input [4:0] rd;
  input [31:0] imm;
  asm_j_type(7'b1101111, rd, imm);
endtask

task automatic JALR;
  input [4:0] rd;
  input [4:0] rs1;
  input [31:0] imm;
  asm_i_type(7'b1100111, rd, rs1, imm, 3'b000);
endtask

//-----------------------------------------------------------------------------
// System instructions
//-----------------------------------------------------------------------------

task automatic FENCE;
  input [3:0] pred;
  input [3:0] succ;
  begin
    MEM[asm_pc[11:2]] = {
      4'b0000, pred, succ, 5'b00000, 3'b000, 5'b00000, 7'b0001111
    };
    asm_pc = asm_pc + 4;
  end
endtask

task automatic FENCE_I;
  begin
    MEM[asm_pc[11:2]] = 32'b0000_0000_0000_00000_001_00000_0001111;
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic ECALL;
  begin
    MEM[asm_pc[11:2]] = 32'b000000000000_00000_000_00000_1110011;
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic EBREAK;
  begin
    MEM[asm_pc[11:2]] = 32'b000000000001_00000_000_00000_1110011;
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic CSRRW;
  input [4:0] rd;
  input [11:0] csr;
  input [4:0] rs1;
  begin
    MEM[asm_pc[11:2]] = {csr, rs1, 3'b001, rd, 7'b1110011};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic CSRRS;
  input [4:0] rd;
  input [11:0] csr;
  input [4:0] rs1;
  begin
    MEM[asm_pc[11:2]] = {csr, rs1, 3'b010, rd, 7'b1110011};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic CSRRC;
  input [4:0] rd;
  input [11:0] csr;
  input [4:0] rs1;
  begin
    MEM[asm_pc[11:2]] = {csr, rs1, 3'b011, rd, 7'b1110011};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic CSRRWI;
  input [4:0] rd;
  input [11:0] csr;
  input [31:0] imm;
  begin
    MEM[asm_pc[11:2]] = {csr, imm[4:0], 3'b101, rd, 7'b1110011};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic CSRRSI;
  input [4:0] rd;
  input [11:0] csr;
  input [31:0] imm;
  begin
    MEM[asm_pc[11:2]] = {csr, imm[4:0], 3'b110, rd, 7'b1110011};
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic CSRRCI;
  input [4:0] rd;
  input [11:0] csr;
  input [31:0] imm;
  begin
    MEM[asm_pc[11:2]] = {csr, imm[4:0], 3'b111, rd, 7'b1110011};
    asm_pc            = asm_pc + 4;
  end
endtask

//-----------------------------------------------------------------------------
// Pseudo-instructions
//-----------------------------------------------------------------------------

task automatic NOP;
  ADD(x0, x0, x0);
endtask

//
// Zicntr pseudoinstructions (read-only performance counters)
//
task automatic RDCYCLE;
  input [4:0] rd;
  CSRRS(rd, 12'hC00, x0);
endtask

task automatic RDCYCLEH;
  input [4:0] rd;
  CSRRS(rd, 12'hC80, x0);
endtask

task automatic RDINSTRET;
  input [4:0] rd;
  CSRRS(rd, 12'hC02, x0);
endtask

task automatic RDINSTRETH;
  input [4:0] rd;
  CSRRS(rd, 12'hC82, x0);
endtask

task automatic LI;
  input [4:0] rd;
  input [31:0] imm;
  begin
    if (imm == 0) begin
      ADD(rd, zero, zero);
    end else if ($signed(imm) >= -2048 && $signed(imm) < 2048) begin
      ADDI(rd, zero, imm);
    end else begin
      LUI(rd, imm + ({20'b0, imm[11], 11'b0}));
      if (imm[11:0] != 0) begin
        ADDI(rd, rd, {{20{imm[11]}}, imm[11:0]});
      end
    end
  end
endtask

task automatic MV;
  input [4:0] rd;
  input [4:0] rs1;
  ADD(rd, rs1, zero);
endtask

task automatic NOT;
  input [4:0] rd;
  input [4:0] rs1;
  XORI(rd, rs1, -1);
endtask

task automatic NEG;
  input [4:0] rd;
  input [4:0] rs1;
  SUB(rd, zero, rs1);
endtask

task automatic SEQZ;
  input [4:0] rd;
  input [4:0] rs1;
  SLTIU(rd, rs1, 1);
endtask

task automatic SNEZ;
  input [4:0] rd;
  input [4:0] rs1;
  SLTU(rd, zero, rs1);
endtask

task automatic SLTZ;
  input [4:0] rd;
  input [4:0] rs1;
  SLT(rd, rs1, zero);
endtask

task automatic SGTZ;
  input [4:0] rd;
  input [4:0] rs1;
  SLT(rd, zero, rs1);
endtask

task automatic BEQZ;
  input [4:0] rs1;
  input [31:0] imm;
  BEQ(rs1, x0, imm);
endtask

task automatic BNEZ;
  input [4:0] rs1;
  input [31:0] imm;
  BNE(rs1, x0, imm);
endtask

task automatic BLEZ;
  input [4:0] rs1;
  input [31:0] imm;
  BGE(x0, rs1, imm);
endtask

task automatic BGEZ;
  input [4:0] rs1;
  input [31:0] imm;
  BGE(rs1, x0, imm);
endtask

task automatic BLTZ;
  input [4:0] rs1;
  input [31:0] imm;
  BLT(rs1, x0, imm);
endtask

task automatic BGTZ;
  input [4:0] rs1;
  input [31:0] imm;
  BLT(x0, rs1, imm);
endtask

task automatic BGT;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  BLT(rs2, rs1, imm);
endtask

task automatic BLE;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  BGE(rs2, rs1, imm);
endtask

task automatic BGTU;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  BLTU(rs2, rs1, imm);
endtask

task automatic BLEU;
  input [4:0] rs1;
  input [4:0] rs2;
  input [31:0] imm;
  BGEU(rs2, rs1, imm);
endtask

task automatic J;
  input [31:0] imm;
  JAL(zero, imm);
endtask

task automatic JR;
  input [4:0] rs1;
  JALR(zero, rs1, 0);
endtask

task automatic RET;
  JALR(x0, ra, 0);
endtask

task automatic CALL;
  input [31:0] offset;
  begin
    AUIPC(t1, offset);
    JALR(ra, t1, {{20{offset[11]}}, offset[11:0]});
  end
endtask

//-----------------------------------------------------------------------------
// Labels
//-----------------------------------------------------------------------------

bit asm_error = 0;

task automatic Label;
  inout integer L;
  begin
    if (L[0] === 1'bx) begin
      $display("ERROR: Missing label initialization");
      asm_error = 1;
    end else if (L != asm_pc) begin
      $display("ERROR: Incorrect label initialization");
      $display("  Expected: %0d Got: %0d", asm_pc, L);
      asm_error = 1;
    end
  end
endtask

function automatic [31:0] LabelRef;
  input integer L;
  begin
    if (L[0] === 1'bx) begin
      $display("ERROR: Reference to uninitialized label");
      asm_error = 1;
      LabelRef  = 0;
    end else begin
      LabelRef = L - asm_pc;
    end
  end
endfunction

task automatic endASM;
  begin
    if (asm_error) begin
      $display("FATAL: Assembly errors detected");
      $finish();
    end
  end
endtask

//-----------------------------------------------------------------------------
// Data directives
//-----------------------------------------------------------------------------

task automatic DATAW;
  input [31:0] w;
  begin
    MEM[asm_pc[11:2]] = w;
    asm_pc            = asm_pc + 4;
  end
endtask

task automatic DATAB;
  input [7:0] b1;
  input [7:0] b2;
  input [7:0] b3;
  input [7:0] b4;
  begin
    MEM[asm_pc[11:2]] = {b4, b3, b2, b1};
    asm_pc            = asm_pc + 4;
  end
endtask

// verilator lint_on UNUSEDSIGNAL

//-----------------------------------------------------------------------------
// RV32F Floating-Point Extension
//-----------------------------------------------------------------------------

// FP register names
localparam bit [4:0] f0 = 0;
localparam bit [4:0] f1 = 1;
localparam bit [4:0] f2 = 2;
localparam bit [4:0] f3 = 3;
localparam bit [4:0] f4 = 4;
localparam bit [4:0] f5 = 5;
localparam bit [4:0] f6 = 6;
localparam bit [4:0] f7 = 7;
localparam bit [4:0] f8 = 8;
localparam bit [4:0] f9 = 9;
localparam bit [4:0] f10 = 10;
localparam bit [4:0] f11 = 11;
localparam bit [4:0] f12 = 12;
localparam bit [4:0] f13 = 13;
localparam bit [4:0] f14 = 14;
localparam bit [4:0] f15 = 15;
localparam bit [4:0] f16 = 16;
localparam bit [4:0] f17 = 17;
localparam bit [4:0] f18 = 18;
localparam bit [4:0] f19 = 19;
localparam bit [4:0] f20 = 20;
localparam bit [4:0] f21 = 21;
localparam bit [4:0] f22 = 22;
localparam bit [4:0] f23 = 23;
localparam bit [4:0] f24 = 24;
localparam bit [4:0] f25 = 25;
localparam bit [4:0] f26 = 26;
localparam bit [4:0] f27 = 27;
localparam bit [4:0] f28 = 28;
localparam bit [4:0] f29 = 29;
localparam bit [4:0] f30 = 30;
localparam bit [4:0] f31 = 31;

// FP ABI names
// verilator lint_off UNUSEDPARAM
localparam bit [4:0] ft0 = f0;
localparam bit [4:0] ft1 = f1;
localparam bit [4:0] ft2 = f2;
localparam bit [4:0] ft3 = f3;
localparam bit [4:0] ft4 = f4;
localparam bit [4:0] ft5 = f5;
localparam bit [4:0] ft6 = f6;
localparam bit [4:0] ft7 = f7;
localparam bit [4:0] fs0 = f8;
localparam bit [4:0] fs1 = f9;
localparam bit [4:0] fa0 = f10;
localparam bit [4:0] fa1 = f11;
localparam bit [4:0] fa2 = f12;
localparam bit [4:0] fa3 = f13;
localparam bit [4:0] fa4 = f14;
localparam bit [4:0] fa5 = f15;
localparam bit [4:0] fa6 = f16;
localparam bit [4:0] fa7 = f17;
localparam bit [4:0] fs2 = f18;
localparam bit [4:0] fs3 = f19;
localparam bit [4:0] fs4 = f20;
localparam bit [4:0] fs5 = f21;
localparam bit [4:0] fs6 = f22;
localparam bit [4:0] fs7 = f23;
localparam bit [4:0] fs8 = f24;
localparam bit [4:0] fs9 = f25;
localparam bit [4:0] fs10 = f26;
localparam bit [4:0] fs11 = f27;
localparam bit [4:0] ft8 = f28;
localparam bit [4:0] ft9 = f29;
localparam bit [4:0] ft10 = f30;
localparam bit [4:0] ft11 = f31;

// Rounding modes
localparam bit [2:0] RNE = 3'b000;  // Round to Nearest, ties to Even
localparam bit [2:0] RTZ = 3'b001;  // Round towards Zero
localparam bit [2:0] RDN = 3'b010;  // Round Down (-inf)
localparam bit [2:0] RUP = 3'b011;  // Round Up (+inf)
localparam bit [2:0] RMM = 3'b100;  // Round to Nearest, ties to Max Magnitude
localparam bit [2:0] DYN = 3'b111;  // Dynamic (use frm CSR)
// verilator lint_on UNUSEDPARAM

// FLW - Load word to FP register
task automatic FLW;
  input [4:0] fd;
  input [4:0] rs1;
  input signed [11:0] imm;
  begin
    MEM[asm_pc[11:2]] = {imm, rs1, 3'b010, fd, 7'b0000111};
    asm_pc            = asm_pc + 4;
  end
endtask

// FSW - Store word from FP register
task automatic FSW;
  input [4:0] frs2;
  input [4:0] rs1;
  input signed [11:0] imm;
  begin
    MEM[asm_pc[11:2]] = {imm[11:5], frs2, rs1, 3'b010, imm[4:0], 7'b0100111};
    asm_pc            = asm_pc + 4;
  end
endtask

// R4-type (FMA) helper
task automatic asm_r4_type;
  input [6:0] opcode;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [4:0] frs3;
  input [2:0] rm;
  begin
    MEM[asm_pc[11:2]] = {frs3, 2'b00, frs2, frs1, rm, fd, opcode};
    asm_pc            = asm_pc + 4;
  end
endtask

// FP R-type helper
task automatic asm_fp_r_type;
  input [6:0] funct7;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [2:0] rm;
  begin
    MEM[asm_pc[11:2]] = {funct7, frs2, frs1, rm, fd, 7'b1010011};
    asm_pc            = asm_pc + 4;
  end
endtask

// FADD.S
task automatic FADD_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [2:0] rm;
  asm_fp_r_type(7'b0000000, fd, frs1, frs2, rm);
endtask

// FSUB.S
task automatic FSUB_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [2:0] rm;
  asm_fp_r_type(7'b0000100, fd, frs1, frs2, rm);
endtask

// FMUL.S
task automatic FMUL_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [2:0] rm;
  asm_fp_r_type(7'b0001000, fd, frs1, frs2, rm);
endtask

// FDIV.S
task automatic FDIV_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [2:0] rm;
  asm_fp_r_type(7'b0001100, fd, frs1, frs2, rm);
endtask

// FSQRT.S
task automatic FSQRT_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [2:0] rm;
  asm_fp_r_type(7'b0101100, fd, frs1, 5'b00000, rm);
endtask

// FMADD.S
task automatic FMADD_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [4:0] frs3;
  input [2:0] rm;
  asm_r4_type(7'b1000011, fd, frs1, frs2, frs3, rm);
endtask

// FMSUB.S
task automatic FMSUB_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [4:0] frs3;
  input [2:0] rm;
  asm_r4_type(7'b1000111, fd, frs1, frs2, frs3, rm);
endtask

// FNMSUB.S
task automatic FNMSUB_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [4:0] frs3;
  input [2:0] rm;
  asm_r4_type(7'b1001011, fd, frs1, frs2, frs3, rm);
endtask

// FNMADD.S
task automatic FNMADD_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  input [4:0] frs3;
  input [2:0] rm;
  asm_r4_type(7'b1001111, fd, frs1, frs2, frs3, rm);
endtask

// FMIN.S
task automatic FMIN_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b0010100, fd, frs1, frs2, 3'b000);
endtask

// FMAX.S
task automatic FMAX_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b0010100, fd, frs1, frs2, 3'b001);
endtask

// FSGNJ.S (copy sign)
task automatic FSGNJ_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b0010000, fd, frs1, frs2, 3'b000);
endtask

// FSGNJN.S (copy negated sign)
task automatic FSGNJN_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b0010000, fd, frs1, frs2, 3'b001);
endtask

// FSGNJX.S (XOR signs)
task automatic FSGNJX_S;
  input [4:0] fd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b0010000, fd, frs1, frs2, 3'b010);
endtask

// FMV.X.W - Move FP bits to integer register
task automatic FMV_X_W;
  input [4:0] rd;
  input [4:0] frs1;
  asm_fp_r_type(7'b1110000, rd, frs1, 5'b00000, 3'b000);
endtask

// FMV.W.X - Move integer bits to FP register
task automatic FMV_W_X;
  input [4:0] fd;
  input [4:0] rs1;
  asm_fp_r_type(7'b1111000, fd, rs1, 5'b00000, 3'b000);
endtask

// FCVT.W.S - Convert FP to signed integer
task automatic FCVT_W_S;
  input [4:0] rd;
  input [4:0] frs1;
  input [2:0] rm;
  asm_fp_r_type(7'b1100000, rd, frs1, 5'b00000, rm);
endtask

// FCVT.WU.S - Convert FP to unsigned integer
task automatic FCVT_WU_S;
  input [4:0] rd;
  input [4:0] frs1;
  input [2:0] rm;
  asm_fp_r_type(7'b1100000, rd, frs1, 5'b00001, rm);
endtask

// FCVT.S.W - Convert signed integer to FP
task automatic FCVT_S_W;
  input [4:0] fd;
  input [4:0] rs1;
  input [2:0] rm;
  asm_fp_r_type(7'b1101000, fd, rs1, 5'b00000, rm);
endtask

// FCVT.S.WU - Convert unsigned integer to FP
task automatic FCVT_S_WU;
  input [4:0] fd;
  input [4:0] rs1;
  input [2:0] rm;
  asm_fp_r_type(7'b1101000, fd, rs1, 5'b00001, rm);
endtask

// FEQ.S - FP equal comparison
task automatic FEQ_S;
  input [4:0] rd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b1010000, rd, frs1, frs2, 3'b010);
endtask

// FLT.S - FP less-than comparison
task automatic FLT_S;
  input [4:0] rd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b1010000, rd, frs1, frs2, 3'b001);
endtask

// FLE.S - FP less-equal comparison
task automatic FLE_S;
  input [4:0] rd;
  input [4:0] frs1;
  input [4:0] frs2;
  asm_fp_r_type(7'b1010000, rd, frs1, frs2, 3'b000);
endtask

// FCLASS.S - Classify FP value
task automatic FCLASS_S;
  input [4:0] rd;
  input [4:0] frs1;
  asm_fp_r_type(7'b1110000, rd, frs1, 5'b00000, 3'b001);
endtask

// Pseudo-instructions

// FMV.S fd, frs (copy register) = FSGNJ.S fd, frs, frs
task automatic FMV_S;
  input [4:0] fd;
  input [4:0] frs;
  FSGNJ_S(fd, frs, frs);
endtask

// FNEG.S fd, frs (negate) = FSGNJN.S fd, frs, frs
task automatic FNEG_S;
  input [4:0] fd;
  input [4:0] frs;
  FSGNJN_S(fd, frs, frs);
endtask

// FABS.S fd, frs (absolute value) = FSGNJX.S fd, frs, frs
task automatic FABS_S;
  input [4:0] fd;
  input [4:0] frs;
  FSGNJX_S(fd, frs, frs);
endtask

`endif
