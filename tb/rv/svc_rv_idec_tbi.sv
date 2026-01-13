`include "svc_unit.sv"

`include "svc_rv_idec.sv"

module svc_rv_idec_tbi;
  `TEST_CLK_NS(clk, 10);

  `include "svc_rv_defs.svh"

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
  logic        jb_tgt_src;

  logic [ 4:0] rd;
  logic [ 4:0] rs1;
  logic [ 4:0] rs2;
  logic [ 2:0] funct3;
  logic [ 6:0] funct7;
  logic        is_m;
  logic        is_csr;
  logic        is_ebreak;
  logic        is_jal;
  logic        is_jalr;
  logic        rs1_used;
  logic        rs2_used;

  logic [31:0] imm_i;
  logic [31:0] imm_s;
  logic [31:0] imm_b;
  logic [31:0] imm_u;
  logic [31:0] imm_j;

  svc_rv_idec #(
      .XLEN (32),
      .EXT_M(1)
  ) uut (
      .instr(instr),

      .reg_write (reg_write),
      .mem_read  (mem_read),
      .mem_write (mem_write),
      .alu_a_src (alu_a_src),
      .alu_b_src (alu_b_src),
      .alu_instr (alu_instr),
      .res_src   (res_src),
      .imm_type  (imm_type),
      .is_branch (is_branch),
      .is_jmp    (is_jmp),
      .jb_tgt_src(jb_tgt_src),
      .is_m      (is_m),
      .is_csr    (is_csr),
      .is_ebreak (is_ebreak),
      .is_jal    (is_jal),
      .is_jalr   (is_jalr),

      .rd           (rd),
      .rs1          (rs1),
      .rs2          (rs2),
      .funct3       (funct3),
      .funct7       (funct7),
      .rs1_used     (rs1_used),
      .rs2_used     (rs2_used),
      .instr_invalid(),

      .imm_i(imm_i),
      .imm_s(imm_s),
      .imm_b(imm_b),
      .imm_u(imm_u),
      .imm_j(imm_j)
  );

  task automatic test_reset;
    instr = 32'h00000000;
    `CHECK_FALSE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_ebreak);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_FALSE(rs1_used);
    `CHECK_FALSE(rs2_used);
  endtask

  //
  // Test: CSR instruction decode (RDCYCLE)
  //
  task automatic test_csr_decode;
    //
    // CSRRS x1, 0xC00, x0 (RDCYCLE pseudoinstruction)
    //
    instr = {12'hC00, 5'h00, 3'b010, 5'd1, 7'b1110011};
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(res_src, RES_CSR);
    `CHECK_EQ(imm_type, IMM_I);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_TRUE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_FALSE(rs2_used);
    `CHECK_EQ(rd, 5'd1);
    `CHECK_EQ(rs1, 5'd0);
    `CHECK_EQ(funct3, FUNCT3_CSRRS);
    `CHECK_EQ(imm_i[11:0], CSR_CYCLE);
  endtask

  task automatic test_lw_decode;
    instr = 32'b000000000100_00001_010_00010_0000011;
    `CHECK_TRUE(reg_write);
    `CHECK_TRUE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(alu_a_src, ALU_A_RS1);
    `CHECK_EQ(alu_b_src, ALU_B_IMM);
    `CHECK_EQ(alu_instr, ALU_INSTR_ADD);
    `CHECK_EQ(res_src, RES_MEM);
    `CHECK_EQ(imm_type, IMM_I);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_FALSE(rs2_used);

    `CHECK_EQ(rd, 5'd2);
    `CHECK_EQ(rs1, 5'd1);
    `CHECK_EQ(funct3, 3'b010);

    `CHECK_EQ(imm_i, 32'd4);
  endtask

  task automatic test_sw_decode;
    instr = 32'b0000000_00011_00010_010_01000_0100011;
    `CHECK_FALSE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_TRUE(mem_write);
    `CHECK_EQ(alu_a_src, ALU_A_RS1);
    `CHECK_EQ(alu_b_src, ALU_B_IMM);
    `CHECK_EQ(alu_instr, ALU_INSTR_ADD);
    `CHECK_EQ(imm_type, IMM_S);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_TRUE(rs2_used);

    `CHECK_EQ(rd, 5'd8);
    `CHECK_EQ(rs1, 5'd2);
    `CHECK_EQ(rs2, 5'd3);
    `CHECK_EQ(funct3, 3'b010);

    `CHECK_EQ(imm_s, 32'd8);
  endtask

  task automatic test_add_decode;
    instr = 32'b0000000_00011_00010_000_00100_0110011;
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(alu_a_src, ALU_A_RS1);
    `CHECK_EQ(alu_b_src, ALU_B_RS2);
    `CHECK_EQ(alu_instr, ALU_INSTR_FN3);
    `CHECK_EQ(res_src, RES_ALU);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_TRUE(rs2_used);

    `CHECK_EQ(rd, 5'd4);
    `CHECK_EQ(rs1, 5'd2);
    `CHECK_EQ(rs2, 5'd3);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(funct7, 7'b0000000);
  endtask

  task automatic test_beq_decode;
    instr = 32'b0_000001_00011_00010_000_0000_0_1100011;
    `CHECK_FALSE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    //
    // ALU control signals are don't-care for branches (use bcmp instead)
    //
    `CHECK_EQ(imm_type, IMM_B);
    `CHECK_TRUE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_TRUE(rs2_used);

    `CHECK_EQ(rs1, 5'd2);
    `CHECK_EQ(rs2, 5'd3);
    `CHECK_EQ(funct3, 3'b000);

    `CHECK_EQ(imm_b, 32'd32);
  endtask

  task automatic test_addi_decode;
    instr = 32'b000000001000_00001_000_00010_0010011;
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(alu_a_src, ALU_A_RS1);
    `CHECK_EQ(alu_b_src, ALU_B_IMM);
    `CHECK_EQ(alu_instr, ALU_INSTR_FN3);
    `CHECK_EQ(res_src, RES_ALU);
    `CHECK_EQ(imm_type, IMM_I);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_FALSE(rs2_used);

    `CHECK_EQ(rd, 5'd2);
    `CHECK_EQ(rs1, 5'd1);
    `CHECK_EQ(funct3, 3'b000);

    `CHECK_EQ(imm_i, 32'd8);
  endtask

  task automatic test_jal_decode;
    instr = 32'b0_0000000001_0_00000000_00001_1101111;
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(res_src, RES_PC4);
    `CHECK_EQ(imm_type, IMM_J);
    `CHECK_FALSE(is_branch);
    `CHECK_TRUE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_TRUE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_FALSE(rs1_used);
    `CHECK_FALSE(rs2_used);

    `CHECK_EQ(rd, 5'd1);

    `CHECK_EQ(imm_j, 32'd2);
  endtask

  task automatic test_auipc_decode;
    instr = 32'b00000000000000000001_00001_0010111;
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(res_src, RES_TGT);
    `CHECK_EQ(imm_type, IMM_U);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_FALSE(rs1_used);
    `CHECK_FALSE(rs2_used);

    `CHECK_EQ(rd, 5'd1);

    `CHECK_EQ(imm_u, 32'h00001000);
  endtask

  task automatic test_lui_decode;
    instr = 32'b00000000000000000001_00001_0110111;
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(alu_a_src, ALU_A_ZERO);
    `CHECK_EQ(alu_b_src, ALU_B_IMM);
    `CHECK_EQ(res_src, RES_ALU);
    `CHECK_EQ(imm_type, IMM_U);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_FALSE(rs1_used);
    `CHECK_FALSE(rs2_used);

    `CHECK_EQ(rd, 5'd1);

    `CHECK_EQ(imm_u, 32'h00001000);
  endtask

  task automatic test_jalr_decode;
    instr = 32'b000000000100_00001_000_00010_1100111;
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(alu_a_src, ALU_A_RS1);
    `CHECK_EQ(alu_b_src, ALU_B_IMM);
    `CHECK_EQ(alu_instr, ALU_INSTR_ADD);
    `CHECK_EQ(res_src, RES_PC4);
    `CHECK_EQ(imm_type, IMM_I);
    `CHECK_FALSE(is_branch);
    `CHECK_TRUE(is_jmp);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_TRUE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_FALSE(rs2_used);
    `CHECK_EQ(jb_tgt_src, JB_TARGET_ALU);

    `CHECK_EQ(rd, 5'd2);
    `CHECK_EQ(rs1, 5'd1);

    `CHECK_EQ(imm_i, 32'd4);
  endtask

  task automatic test_negative_immediate;
    instr = 32'b111111111111_00001_010_00010_0000011;
    `CHECK_EQ(imm_i, 32'hFFFFFFFF);
    // rs2 not used for this instruction (but contains instruction bits)
  endtask

  //
  // Test: M extension instruction decode (MUL)
  //
  task automatic test_mul_decode;
    //
    // MUL x4, x2, x3
    //
    instr = 32'b0000001_00011_00010_000_00100_0110011;
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_EQ(alu_a_src, ALU_A_RS1);
    `CHECK_EQ(alu_b_src, ALU_B_RS2);
    `CHECK_EQ(res_src, RES_M);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_TRUE(is_m);
    `CHECK_FALSE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
    `CHECK_TRUE(rs1_used);
    `CHECK_TRUE(rs2_used);

    `CHECK_EQ(rd, 5'd4);
    `CHECK_EQ(rs1, 5'd2);
    `CHECK_EQ(rs2, 5'd3);
    `CHECK_EQ(funct3, 3'b000);
    `CHECK_EQ(funct7, 7'b0000001);
  endtask

  //
  // Test: EBREAK instruction decode
  //
  task automatic test_ebreak_decode;
    //
    // EBREAK: 32'h00100073
    //
    instr = I_EBREAK;
    `CHECK_TRUE(is_ebreak);
    `CHECK_TRUE(reg_write);
    `CHECK_FALSE(mem_read);
    `CHECK_FALSE(mem_write);
    `CHECK_FALSE(is_branch);
    `CHECK_FALSE(is_jmp);
    `CHECK_TRUE(is_csr);
    `CHECK_FALSE(is_jal);
    `CHECK_FALSE(is_jalr);
  endtask

  //
  // Test: ECALL instruction does NOT set is_ebreak
  //
  task automatic test_ecall_not_ebreak;
    //
    // ECALL: 32'h00000073
    //
    instr = I_ECALL;
    `CHECK_FALSE(is_ebreak);
    `CHECK_TRUE(is_csr);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_idec_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_ebreak_decode);
  `TEST_CASE(test_ecall_not_ebreak);
  `TEST_CASE(test_csr_decode);
  `TEST_CASE(test_lw_decode);
  `TEST_CASE(test_sw_decode);
  `TEST_CASE(test_add_decode);
  `TEST_CASE(test_beq_decode);
  `TEST_CASE(test_addi_decode);
  `TEST_CASE(test_jal_decode);
  `TEST_CASE(test_auipc_decode);
  `TEST_CASE(test_lui_decode);
  `TEST_CASE(test_jalr_decode);
  `TEST_CASE(test_negative_immediate);
  `TEST_CASE(test_mul_decode);
  `TEST_SUITE_END();

endmodule
