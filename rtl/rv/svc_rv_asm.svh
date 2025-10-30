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

`endif
