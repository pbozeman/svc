`include "svc_unit.sv"
`include "svc_rv_idec.sv"

// Example testbench demonstrating RISC-V assembly helper usage
//
// This testbench shows how to use svc_rv_asm.svh to generate
// RISC-V machine code instructions for testing.

// verilator lint_off UNUSEDSIGNAL
module svc_rv_asm_tb;
  `include "svc_rv_defs.svh"

  localparam int XLEN = 32;

  // Instruction memory
  logic [31:0] MEM[1024];

  // Include assembly helper AFTER declaring MEM
  `include "svc_rv_asm.svh"

  // Decoder signals
  logic [31:0] instr;
  logic        reg_write;
  logic        mem_read;
  logic        mem_write;
  logic [ 1:0] alu_a_src;
  logic        alu_b_src;
  logic [ 1:0] alu_instr;
  logic [ 2:0] res_src;
  logic [ 2:0] imm_type;
  logic        is_branch;
  logic        is_jmp;
  logic        jb_target_src;
  logic        is_m;
  logic        is_csr;
  logic        is_ebreak;
  logic        is_jal;
  logic        is_jalr;
  logic [ 4:0] rd;
  logic [ 4:0] rs1;
  logic [ 4:0] rs2;
  logic [ 2:0] funct3;
  logic [ 6:0] funct7;
  logic        rs1_used;
  logic        rs2_used;
  logic [31:0] imm_i;
  logic [31:0] imm_s;
  logic [31:0] imm_b;
  logic [31:0] imm_u;
  logic [31:0] imm_j;

  svc_rv_idec #(
      .XLEN (XLEN),
      .EXT_M(0)
  ) decoder (
      .instr        (instr),
      .reg_write    (reg_write),
      .mem_read     (mem_read),
      .mem_write    (mem_write),
      .alu_a_src    (alu_a_src),
      .alu_b_src    (alu_b_src),
      .alu_instr    (alu_instr),
      .res_src      (res_src),
      .imm_type     (imm_type),
      .is_branch    (is_branch),
      .is_jmp       (is_jmp),
      .jb_target_src(jb_target_src),
      .is_m         (is_m),
      .is_csr       (is_csr),
      .is_ebreak    (is_ebreak),
      .is_jal       (is_jal),
      .is_jalr      (is_jalr),
      .rd           (rd),
      .rs1          (rs1),
      .rs2          (rs2),
      .funct3       (funct3),
      .funct7       (funct7),
      .rs1_used     (rs1_used),
      .rs2_used     (rs2_used),
      .instr_invalid(),
      .imm_i        (imm_i),
      .imm_s        (imm_s),
      .imm_b        (imm_b),
      .imm_u        (imm_u),
      .imm_j        (imm_j)
  );

  // Test R-type instruction encoding
  task automatic test_r_type_encoding;
    integer addr;
    asm_pc = 0;

    // Generate R-type instructions
    ADD(x1, x2, x3);
    SUB(x4, x5, x6);
    XOR(x7, x8, x9);
    OR(x10, x11, x12);
    AND(x13, x14, x15);
    SLL(x16, x17, x18);
    SRL(x19, x20, x21);
    SRA(x22, x23, x24);
    SLT(x25, x26, x27);
    SLTU(x28, x29, x30);

    // Verify ADD instruction
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 2);
    `CHECK_EQ(rs2, 3);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(funct7, 7'b0000000);

    // Verify SUB instruction (funct7[5] = 1)
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 4);
    `CHECK_EQ(rs1, 5);
    `CHECK_EQ(rs2, 6);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(funct7, 7'b0100000);

    // Verify SRA instruction (funct7[5] = 1)
    addr  = 7;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 22);
    `CHECK_EQ(rs1, 23);
    `CHECK_EQ(rs2, 24);
    `CHECK_EQ(funct3, 3'b101);
    `CHECK_EQ(funct7, 7'b0100000);
  endtask

  // Test M-extension multiply instruction encoding
  task automatic test_m_ext_encoding;
    integer addr;
    asm_pc = 0;

    // Generate M-extension multiply instructions
    MUL(x1, x2, x3);
    MULH(x4, x5, x6);
    MULHSU(x7, x8, x9);
    MULHU(x10, x11, x12);

    // Verify MUL instruction (funct3=000)
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 2);
    `CHECK_EQ(rs2, 3);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(funct7, 7'b0000001);

    // Verify MULH instruction (funct3=001)
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 4);
    `CHECK_EQ(rs1, 5);
    `CHECK_EQ(rs2, 6);
    `CHECK_EQ(funct3, 3'b001);
    `CHECK_EQ(funct7, 7'b0000001);

    // Verify MULHSU instruction (funct3=010)
    addr  = 2;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 7);
    `CHECK_EQ(rs1, 8);
    `CHECK_EQ(rs2, 9);
    `CHECK_EQ(funct3, 3'b010);
    `CHECK_EQ(funct7, 7'b0000001);

    // Verify MULHU instruction (funct3=011)
    addr  = 3;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 10);
    `CHECK_EQ(rs1, 11);
    `CHECK_EQ(rs2, 12);
    `CHECK_EQ(funct3, 3'b011);
    `CHECK_EQ(funct7, 7'b0000001);
  endtask

  // Test M-extension division/remainder instruction encoding
  task automatic test_m_ext_div_encoding;
    integer addr;
    asm_pc = 0;

    // Generate M-extension division/remainder instructions
    DIV(x1, x2, x3);
    DIVU(x4, x5, x6);
    REM(x7, x8, x9);
    REMU(x10, x11, x12);

    // Verify DIV instruction (funct3=100)
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 2);
    `CHECK_EQ(rs2, 3);
    `CHECK_EQ(funct3, 3'b100);
    `CHECK_EQ(funct7, 7'b0000001);

    // Verify DIVU instruction (funct3=101)
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 4);
    `CHECK_EQ(rs1, 5);
    `CHECK_EQ(rs2, 6);
    `CHECK_EQ(funct3, 3'b101);
    `CHECK_EQ(funct7, 7'b0000001);

    // Verify REM instruction (funct3=110)
    addr  = 2;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 7);
    `CHECK_EQ(rs1, 8);
    `CHECK_EQ(rs2, 9);
    `CHECK_EQ(funct3, 3'b110);
    `CHECK_EQ(funct7, 7'b0000001);

    // Verify REMU instruction (funct3=111)
    addr  = 3;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 10);
    `CHECK_EQ(rs1, 11);
    `CHECK_EQ(rs2, 12);
    `CHECK_EQ(funct3, 3'b111);
    `CHECK_EQ(funct7, 7'b0000001);
  endtask

  // Test I-type instruction encoding
  task automatic test_i_type_encoding;
    integer addr;
    asm_pc = 0;

    // Generate I-type ALU instructions
    ADDI(x1, x2, 42);
    XORI(x3, x4, -1);
    ORI(x5, x6, 32'h0FF);
    ANDI(x7, x8, 32'hF00);
    SLTI(x9, x10, -10);
    SLTIU(x11, x12, 100);

    // Verify ADDI instruction
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_ITYPE);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 2);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(imm_i, 42);

    // Verify XORI with -1 (sign-extended to all bits set)
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_ITYPE);
    `CHECK_EQ(rd, 3);
    `CHECK_EQ(rs1, 4);
    `CHECK_EQ(funct3, 3'b100);
    `CHECK_EQ(imm_i, 32'hFFFFFFFF);
  endtask

  // Test shift immediate instruction encoding
  task automatic test_shift_imm_encoding;
    integer addr;
    asm_pc = 0;

    // Generate shift immediate instructions
    SLLI(x1, x2, 5);
    SRLI(x3, x4, 10);
    SRAI(x5, x6, 15);

    // Verify SLLI instruction
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_ITYPE);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 2);
    // rs2 not checked - contains instruction bits when not used
    `CHECK_EQ(instr[24:20], 5);  // shift amount in immediate field
    `CHECK_EQ(funct3, 3'b001);
    `CHECK_EQ(funct7, 7'b0000000);

    // Verify SRAI instruction (funct7[5] = 1)
    addr  = 2;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_ITYPE);
    `CHECK_EQ(rd, 5);
    `CHECK_EQ(rs1, 6);
    // rs2 not checked - contains instruction bits when not used
    `CHECK_EQ(instr[24:20], 15);  // shift amount in immediate field
    `CHECK_EQ(funct3, 3'b101);
    `CHECK_EQ(funct7, 7'b0100000);
  endtask

  // Test load instruction encoding
  task automatic test_load_encoding;
    integer addr;
    asm_pc = 0;

    // Generate load instructions
    LW(x1, x2, 100);
    LH(x3, x4, 50);
    LB(x5, x6, 25);
    LHU(x7, x8, 12);
    LBU(x9, x10, 8);

    // Verify LW instruction
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_LOAD);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 2);
    `CHECK_EQ(funct3, 3'b010);
    `CHECK_EQ(imm_i, 100);

    // Verify LBU instruction
    addr  = 4;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_LOAD);
    `CHECK_EQ(rd, 9);
    `CHECK_EQ(rs1, 10);
    `CHECK_EQ(funct3, 3'b100);
    `CHECK_EQ(imm_i, 8);
  endtask

  // Test store instruction encoding
  task automatic test_store_encoding;
    integer addr;
    asm_pc = 0;

    // Generate store instructions
    SW(x1, x2, 100);
    SH(x3, x4, 50);
    SB(x5, x6, 25);

    // Verify SW instruction
    // SW task signature: SW(rs1_data, rs2_base, imm)
    // Encoding: MEM[rs2_base + imm] = rs1_data
    // In instruction: rs1=base, rs2=data
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_STORE);
    `CHECK_EQ(rs1, 2);
    `CHECK_EQ(rs2, 1);
    `CHECK_EQ(funct3, 3'b010);
    `CHECK_EQ(imm_s, 100);
  endtask

  // Test branch instruction encoding
  task automatic test_branch_encoding;
    integer addr;
    asm_pc = 0;

    // Generate branch instructions
    BEQ(x1, x2, 16);
    BNE(x3, x4, 32);
    BLT(x5, x6, -8);
    BGE(x7, x8, -16);
    BLTU(x9, x10, 64);
    BGEU(x11, x12, 128);

    // Verify BEQ instruction
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_BRANCH);
    `CHECK_EQ(rs1, 1);
    `CHECK_EQ(rs2, 2);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(imm_b, 16);
    `CHECK_TRUE(is_branch);

    // Verify BLT with negative offset (sign-extended -8)
    addr  = 2;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_BRANCH);
    `CHECK_EQ(rs1, 5);
    `CHECK_EQ(rs2, 6);
    `CHECK_EQ(funct3, 3'b100);
    `CHECK_EQ(imm_b, 32'hFFFFFFF8);
  endtask

  // Test U-type instruction encoding
  task automatic test_u_type_encoding;
    integer addr;
    asm_pc = 0;

    // Generate U-type instructions
    LUI(x1, 32'h12345000);
    AUIPC(x2, 32'h00010000);

    // Verify LUI instruction
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_LUI);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(imm_u, 32'h12345000);

    // Verify AUIPC instruction
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_AUIPC);
    `CHECK_EQ(rd, 2);
    `CHECK_EQ(imm_u, 32'h00010000);
  endtask

  // Test J-type instruction encoding
  task automatic test_j_type_encoding;
    integer addr;
    asm_pc = 0;

    // Generate J-type instructions
    JAL(ra, 100);
    JALR(x5, x6, 200);

    // Verify JAL instruction
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_JAL);
    `CHECK_EQ(rd, ra);
    `CHECK_EQ(imm_j, 100);
    `CHECK_TRUE(is_jmp);

    // Verify JALR instruction (encoded as I-type)
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_JALR);
    `CHECK_EQ(rd, 5);
    `CHECK_EQ(rs1, 6);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(imm_i, 200);
    `CHECK_TRUE(is_jmp);
  endtask

  // Test pseudo-instructions
  task automatic test_pseudo_instructions;
    integer addr;
    asm_pc = 0;

    // Test NOP
    NOP();
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr, 32'b0000000_00000_00000_000_00000_0110011);

    // Test MV (move)
    asm_pc = 0;
    MV(x1, x2);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_RTYPE);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 2);
    `CHECK_EQ(rs2, 0);

    // Test LI with small immediate
    asm_pc = 0;
    LI(x1, 42);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_ITYPE);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 0);
    `CHECK_EQ(imm_i, 42);

    // Test LI with large immediate (generates LUI + ADDI)
    asm_pc = 0;
    LI(x1, 32'h12345678);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_LUI);
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_ITYPE);

    // Test BEQZ (branch if equal to zero)
    asm_pc = 0;
    BEQZ(x1, 16);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_BRANCH);
    `CHECK_EQ(rs1, 1);
    `CHECK_EQ(rs2, 0);
    `CHECK_EQ(funct3, 3'b000);
  endtask

  // Test ABI register names
  task automatic test_abi_names;
    asm_pc = 0;

    // Use ABI names
    ADDI(sp, sp, -16);
    SW(ra, sp, 12);
    LW(a0, sp, 0);
    ADD(t0, t1, t2);
    SUB(s0, s1, s2);

    // Verify we're using the correct register numbers
    instr = MEM[0];
    `CHECK_EQ(rd, 2);
    `CHECK_EQ(rs1, 2);
  endtask

  // Test EBREAK instruction encoding
  task automatic test_ebreak_encoding;
    integer addr;
    asm_pc = 0;

    // Generate EBREAK instruction
    EBREAK();

    // Verify EBREAK instruction encoding
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr, I_EBREAK);
    `CHECK_EQ(instr[6:0], OP_SYSTEM);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(imm_i, 32'd1);
  endtask

  //
  // Test CSR instruction encoding (Zicntr pseudoinstructions)
  //
  task automatic test_csr_encoding;
    integer addr;
    asm_pc = 0;

    //
    // RDCYCLE should expand to: CSRRS rd, 0xC00, x0
    // CSR addresses are in bits [31:20], sign-extended in imm_i
    //
    RDCYCLE(x1);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_SYSTEM);
    `CHECK_EQ(rd, 1);
    `CHECK_EQ(rs1, 0);
    `CHECK_EQ(funct3, FUNCT3_CSRRS);
    `CHECK_EQ(instr[31:20], CSR_CYCLE);

    //
    // RDCYCLEH should expand to: CSRRS rd, 0xC80, x0
    //
    asm_pc = 0;
    RDCYCLEH(x2);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_SYSTEM);
    `CHECK_EQ(rd, 2);
    `CHECK_EQ(rs1, 0);
    `CHECK_EQ(funct3, FUNCT3_CSRRS);
    `CHECK_EQ(instr[31:20], CSR_CYCLEH);

    //
    // RDINSTRET should expand to: CSRRS rd, 0xC02, x0
    //
    asm_pc = 0;
    RDINSTRET(x3);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_SYSTEM);
    `CHECK_EQ(rd, 3);
    `CHECK_EQ(rs1, 0);
    `CHECK_EQ(funct3, FUNCT3_CSRRS);
    `CHECK_EQ(instr[31:20], CSR_INSTRET);

    //
    // RDINSTRETH should expand to: CSRRS rd, 0xC82, x0
    //
    asm_pc = 0;
    RDINSTRETH(x4);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_SYSTEM);
    `CHECK_EQ(rd, 4);
    `CHECK_EQ(rs1, 0);
    `CHECK_EQ(funct3, FUNCT3_CSRRS);
    `CHECK_EQ(instr[31:20], CSR_INSTRETH);

    //
    // Test CSRRS base instruction
    //
    asm_pc = 0;
    CSRRS(x10, CSR_CYCLE, x0);
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_SYSTEM);
    `CHECK_EQ(rd, 10);
    `CHECK_EQ(rs1, 0);
    `CHECK_EQ(funct3, FUNCT3_CSRRS);
    `CHECK_EQ(instr[31:20], CSR_CYCLE);
  endtask

  // Test label support
  task automatic test_labels;
    integer loop_start;
    integer loop_end;
    integer addr;

    // Simple loop using labels
    asm_pc     = 0;
    loop_start = asm_pc;
    Label(loop_start);
    ADDI(x1, x1, 1);
    BLT(x1, x2, LabelRef(loop_start));

    // Verify the branch instruction
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_BRANCH);
    `CHECK_EQ(imm_b, 32'hFFFFFFFC);

    // Forward branch
    asm_pc   = 0;
    loop_end = 16;
    BEQ(x1, x2, LabelRef(loop_end));
    ADDI(x3, x3, 1);
    ADDI(x4, x4, 1);
    ADDI(x5, x5, 1);
    Label(loop_end);

    // Verify forward branch offset
    addr  = 0;
    instr = MEM[addr];
    `CHECK_EQ(imm_b, 16);

    // Jump with label
    asm_pc     = 0;
    loop_start = 0;
    Label(loop_start);
    ADDI(x10, x10, 1);
    JAL(x0, LabelRef(loop_start));

    // Verify JAL instruction
    addr  = 1;
    instr = MEM[addr];
    `CHECK_EQ(instr[6:0], OP_JAL);
    `CHECK_EQ(imm_j, 32'hFFFFFFFC);

    endASM();
  endtask

  `TEST_SUITE_BEGIN(svc_rv_asm_tb);
  `TEST_CASE(test_r_type_encoding);
  `TEST_CASE(test_m_ext_encoding);
  `TEST_CASE(test_m_ext_div_encoding);
  `TEST_CASE(test_i_type_encoding);
  `TEST_CASE(test_shift_imm_encoding);
  `TEST_CASE(test_load_encoding);
  `TEST_CASE(test_store_encoding);
  `TEST_CASE(test_branch_encoding);
  `TEST_CASE(test_u_type_encoding);
  `TEST_CASE(test_j_type_encoding);
  `TEST_CASE(test_pseudo_instructions);
  `TEST_CASE(test_abi_names);
  `TEST_CASE(test_ebreak_encoding);
  `TEST_CASE(test_csr_encoding);
  `TEST_CASE(test_labels);
  `TEST_SUITE_END();

endmodule
// verilator lint_on UNUSEDSIGNAL

