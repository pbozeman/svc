`include "svc_unit.sv"
`include "svc_rv_fp_idec.sv"

module svc_rv_fp_idec_tbi;
  `TEST_CLK_NS(clk, 10);

  // Include constants
  `include "svc_rv_defs.svh"

  logic [31:0] instr;

  logic        is_fp;
  logic        is_fp_load;
  logic        is_fp_store;
  logic        is_fp_compute;
  logic        is_fp_mc;
  logic        fp_reg_write;
  logic        int_reg_write;
  logic [ 4:0] fp_rs1;
  logic [ 4:0] fp_rs2;
  logic [ 4:0] fp_rs3;
  logic [ 4:0] fp_rd;
  logic        fp_rs1_used;
  logic        fp_rs2_used;
  logic        fp_rs3_used;
  logic        int_rs1_used;
  logic [ 2:0] fp_rm;
  logic        fp_rm_dyn;
  logic        fp_instr_invalid;

  //
  // DUT instantiation
  //
  svc_rv_fp_idec #(
      .XLEN(32)
  ) uut (
      .instr           (instr),
      .is_fp           (is_fp),
      .is_fp_load      (is_fp_load),
      .is_fp_store     (is_fp_store),
      .is_fp_compute   (is_fp_compute),
      .is_fp_mc        (is_fp_mc),
      .fp_reg_write    (fp_reg_write),
      .int_reg_write   (int_reg_write),
      .fp_rs1          (fp_rs1),
      .fp_rs2          (fp_rs2),
      .fp_rs3          (fp_rs3),
      .fp_rd           (fp_rd),
      .fp_rs1_used     (fp_rs1_used),
      .fp_rs2_used     (fp_rs2_used),
      .fp_rs3_used     (fp_rs3_used),
      .int_rs1_used    (int_rs1_used),
      .fp_rm           (fp_rm),
      .fp_rm_dyn       (fp_rm_dyn),
      .fp_instr_invalid(fp_instr_invalid)
  );

  //
  // Helper to build FP instruction encodings
  //
  // R4-type (FMA): funct5 | fmt | rs3 | rs2 | rs1 | rm | rd | opcode
  // R-type (FP):   funct7 | rs2 | rs1 | rm | rd | opcode
  // I-type (FLW):  imm[11:0] | rs1 | funct3 | rd | opcode
  // S-type (FSW):  imm[11:5] | rs2 | rs1 | funct3 | imm[4:0] | opcode
  //

  function automatic logic [31:0] make_fp_r(
      input logic [6:0] funct7, input logic [4:0] rs2_i,
      input logic [4:0] rs1_i, input logic [2:0] rm, input logic [4:0] rd_i);
    return {funct7, rs2_i, rs1_i, rm, rd_i, OP_FP};
  endfunction

  function automatic logic [31:0] make_fma(
      input logic [6:0] opcode_in, input logic [4:0] rs3_i,
      input logic [4:0] rs2_i, input logic [4:0] rs1_i, input logic [2:0] rm,
      input logic [4:0] rd_i);
    return {rs3_i, 2'b00, rs2_i, rs1_i, rm, rd_i, opcode_in};
  endfunction

  function automatic logic [31:0] make_flw(
      input logic [11:0] imm, input logic [4:0] rs1_i, input logic [4:0] rd_i);
    return {imm, rs1_i, 3'b010, rd_i, OP_LOAD_FP};
  endfunction

  function automatic logic [31:0] make_fsw(
      input logic [11:0] imm, input logic [4:0] rs2_i, input logic [4:0] rs1_i);
    return {imm[11:5], rs2_i, rs1_i, 3'b010, imm[4:0], OP_STORE_FP};
  endfunction

  //
  // Test: FLW instruction
  //
  task automatic test_flw();
    instr = make_flw(12'h100, 5'd10, 5'd5);  // FLW f5, 256(x10)
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_load, 1'b1);
    `CHECK_EQ(is_fp_store, 1'b0);
    `CHECK_EQ(is_fp_compute, 1'b0);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(int_reg_write, 1'b0);
    `CHECK_EQ(fp_rd, 5'd5);
    `CHECK_EQ(int_rs1_used, 1'b1);
    `CHECK_EQ(fp_rs1_used, 1'b0);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FSW instruction
  //
  task automatic test_fsw();
    instr = make_fsw(12'h200, 5'd7, 5'd15);  // FSW f7, 512(x15)
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_load, 1'b0);
    `CHECK_EQ(is_fp_store, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b0);
    `CHECK_EQ(fp_reg_write, 1'b0);
    `CHECK_EQ(int_reg_write, 1'b0);
    `CHECK_EQ(fp_rs2, 5'd7);
    `CHECK_EQ(int_rs1_used, 1'b1);
    `CHECK_EQ(fp_rs2_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FADD.S instruction
  //
  task automatic test_fadd();
    instr =
        make_fp_r(FP7_FADD, 5'd2, 5'd1, FRM_RNE, 5'd3);  // FADD.S f3, f1, f2
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(is_fp_mc, 1'b0);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(int_reg_write, 1'b0);
    `CHECK_EQ(fp_rs1, 5'd1);
    `CHECK_EQ(fp_rs2, 5'd2);
    `CHECK_EQ(fp_rd, 5'd3);
    `CHECK_EQ(fp_rs1_used, 1'b1);
    `CHECK_EQ(fp_rs2_used, 1'b1);
    `CHECK_EQ(fp_rs3_used, 1'b0);
    `CHECK_EQ(fp_rm, FRM_RNE);
    `CHECK_EQ(fp_rm_dyn, 1'b0);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FSUB.S instruction
  //
  task automatic test_fsub();
    instr =
        make_fp_r(FP7_FSUB, 5'd5, 5'd4, FRM_RTZ, 5'd6);  // FSUB.S f6, f4, f5
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_rm, FRM_RTZ);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FMUL.S instruction
  //
  task automatic test_fmul();
    instr =
        make_fp_r(FP7_FMUL, 5'd8, 5'd7, FRM_DYN, 5'd9);  // FMUL.S f9, f7, f8
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(is_fp_mc, 1'b0);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_rm_dyn, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FDIV.S instruction (multi-cycle)
  //
  task automatic test_fdiv();
    instr = make_fp_r(FP7_FDIV, 5'd11, 5'd10, FRM_RNE,
                      5'd12);  // FDIV.S f12, f10, f11
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(is_fp_mc, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FSQRT.S instruction (multi-cycle)
  //
  task automatic test_fsqrt();
    instr =
        make_fp_r(FP7_FSQRT, 5'd0, 5'd13, FRM_RNE, 5'd14);  // FSQRT.S f14, f13
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(is_fp_mc, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_rs1_used, 1'b1);
    `CHECK_EQ(fp_rs2_used, 1'b0);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FMADD.S instruction
  //
  task automatic test_fmadd();
    instr = make_fma(OP_FMADD, 5'd3, 5'd2, 5'd1, FRM_RNE,
                     5'd4);  // FMADD f4, f1, f2, f3
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_rs1, 5'd1);
    `CHECK_EQ(fp_rs2, 5'd2);
    `CHECK_EQ(fp_rs3, 5'd3);
    `CHECK_EQ(fp_rd, 5'd4);
    `CHECK_EQ(fp_rs1_used, 1'b1);
    `CHECK_EQ(fp_rs2_used, 1'b1);
    `CHECK_EQ(fp_rs3_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FMSUB.S, FNMSUB.S, FNMADD.S
  //
  task automatic test_fma_variants();
    // FMSUB.S
    instr = make_fma(OP_FMSUB, 5'd6, 5'd5, 5'd4, FRM_RNE, 5'd7);
    `TICK(clk);
    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_rs3_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FNMSUB.S
    instr = make_fma(OP_FNMSUB, 5'd9, 5'd8, 5'd7, FRM_RNE, 5'd10);
    `TICK(clk);
    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_rs3_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FNMADD.S
    instr = make_fma(OP_FNMADD, 5'd12, 5'd11, 5'd10, FRM_RNE, 5'd13);
    `TICK(clk);
    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_rs3_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FCVT.W.S (FP to int, writes to integer reg)
  //
  task automatic test_fcvt_ws();
    // FCVT.W.S x5, f3 (signed)
    instr = make_fp_r(FP7_FCVTWS, 5'd0, 5'd3, FRM_RTZ, 5'd5);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b0);
    `CHECK_EQ(int_reg_write, 1'b1);
    `CHECK_EQ(fp_rs1_used, 1'b1);
    `CHECK_EQ(int_rs1_used, 1'b0);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FCVT.WU.S x6, f4 (unsigned, rs2=1)
    instr = make_fp_r(FP7_FCVTWS, 5'd1, 5'd4, FRM_RTZ, 5'd6);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(int_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FCVT.S.W (int to FP, writes to FP reg)
  //
  task automatic test_fcvt_sw();
    // FCVT.S.W f5, x3 (signed)
    instr = make_fp_r(FP7_FCVTSW, 5'd0, 5'd3, FRM_RNE, 5'd5);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(is_fp_compute, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(int_reg_write, 1'b0);
    `CHECK_EQ(fp_rs1_used, 1'b0);
    `CHECK_EQ(int_rs1_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FCVT.S.WU f6, x4 (unsigned, rs2=1)
    instr = make_fp_r(FP7_FCVTSW, 5'd1, 5'd4, FRM_RNE, 5'd6);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(int_rs1_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FMV.X.W (FP bits to int reg)
  //
  task automatic test_fmv_xw();
    // FMV.X.W x5, f3
    instr = make_fp_r(FP7_FMVXW, 5'd0, 5'd3, FP3_FMV, 5'd5);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b0);
    `CHECK_EQ(int_reg_write, 1'b1);
    `CHECK_EQ(fp_rs1_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FMV.W.X (int bits to FP reg)
  //
  task automatic test_fmv_wx();
    // FMV.W.X f5, x3
    instr = make_fp_r(FP7_FMVWX, 5'd0, 5'd3, FP3_FMV, 5'd5);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(int_reg_write, 1'b0);
    `CHECK_EQ(fp_rs1_used, 1'b0);
    `CHECK_EQ(int_rs1_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FCLASS.S
  //
  task automatic test_fclass();
    // FCLASS.S x5, f3
    instr = make_fp_r(FP7_FMVXW, 5'd0, 5'd3, FP3_FCLASS, 5'd5);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b0);
    `CHECK_EQ(int_reg_write, 1'b1);
    `CHECK_EQ(fp_rs1_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FEQ.S, FLT.S, FLE.S (comparisons, write to int reg)
  //
  task automatic test_fcmp();
    // FEQ.S x5, f1, f2
    instr = make_fp_r(FP7_FCMP, 5'd2, 5'd1, FP3_FEQ, 5'd5);
    `TICK(clk);

    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b0);
    `CHECK_EQ(int_reg_write, 1'b1);
    `CHECK_EQ(fp_rs1_used, 1'b1);
    `CHECK_EQ(fp_rs2_used, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FLT.S
    instr = make_fp_r(FP7_FCMP, 5'd2, 5'd1, FP3_FLT, 5'd6);
    `TICK(clk);
    `CHECK_EQ(int_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FLE.S
    instr = make_fp_r(FP7_FCMP, 5'd2, 5'd1, FP3_FLE, 5'd7);
    `TICK(clk);
    `CHECK_EQ(int_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FSGNJ variants
  //
  task automatic test_fsgnj();
    // FSGNJ.S
    instr = make_fp_r(FP7_FSGNJ, 5'd2, 5'd1, FP3_FSGNJ, 5'd3);
    `TICK(clk);
    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FSGNJN.S
    instr = make_fp_r(FP7_FSGNJ, 5'd2, 5'd1, FP3_FSGNJN, 5'd4);
    `TICK(clk);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FSGNJX.S
    instr = make_fp_r(FP7_FSGNJ, 5'd2, 5'd1, FP3_FSGNJX, 5'd5);
    `TICK(clk);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: FMIN.S, FMAX.S
  //
  task automatic test_fminmax();
    // FMIN.S
    instr = make_fp_r(FP7_FMINMAX, 5'd2, 5'd1, FP3_FMIN, 5'd3);
    `TICK(clk);
    `CHECK_EQ(is_fp, 1'b1);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);

    // FMAX.S
    instr = make_fp_r(FP7_FMINMAX, 5'd2, 5'd1, FP3_FMAX, 5'd4);
    `TICK(clk);
    `CHECK_EQ(fp_reg_write, 1'b1);
    `CHECK_EQ(fp_instr_invalid, 1'b0);
  endtask

  //
  // Test: Invalid - wrong format (not single-precision)
  //
  task automatic test_invalid_fmt();
    // FADD with fmt=01 (double) - should be invalid
    instr = {FP7_FADD[6:2], 2'b01, 5'd2, 5'd1, FRM_RNE, 5'd3, OP_FP};
    `TICK(clk);
    `CHECK_EQ(fp_instr_invalid, 1'b1);
  endtask

  //
  // Test: Invalid - wrong funct3 for FLW
  //
  task automatic test_invalid_flw_funct3();
    // FLW with funct3 = 011 (invalid, should be 010)
    instr = {12'h100, 5'd10, 3'b011, 5'd5, OP_LOAD_FP};
    `TICK(clk);
    `CHECK_EQ(fp_instr_invalid, 1'b1);
  endtask

  //
  // Test: Invalid - FSQRT with rs2 != 0
  //
  task automatic test_invalid_fsqrt_rs2();
    // FSQRT with rs2 = 5 (invalid, should be 0)
    instr = make_fp_r(FP7_FSQRT, 5'd5, 5'd1, FRM_RNE, 5'd3);
    `TICK(clk);
    `CHECK_EQ(fp_instr_invalid, 1'b1);
  endtask

  //
  // Test: Non-FP instruction
  //
  task automatic test_non_fp();
    // ADD x3, x1, x2 (integer instruction)
    instr = {7'b0000000, 5'd2, 5'd1, 3'b000, 5'd3, OP_RTYPE};
    `TICK(clk);
    `CHECK_EQ(is_fp, 1'b0);
    `CHECK_EQ(is_fp_load, 1'b0);
    `CHECK_EQ(is_fp_store, 1'b0);
    `CHECK_EQ(is_fp_compute, 1'b0);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_fp_idec_tbi);
  `TEST_CASE(test_flw);
  `TEST_CASE(test_fsw);
  `TEST_CASE(test_fadd);
  `TEST_CASE(test_fsub);
  `TEST_CASE(test_fmul);
  `TEST_CASE(test_fdiv);
  `TEST_CASE(test_fsqrt);
  `TEST_CASE(test_fmadd);
  `TEST_CASE(test_fma_variants);
  `TEST_CASE(test_fcvt_ws);
  `TEST_CASE(test_fcvt_sw);
  `TEST_CASE(test_fmv_xw);
  `TEST_CASE(test_fmv_wx);
  `TEST_CASE(test_fclass);
  `TEST_CASE(test_fcmp);
  `TEST_CASE(test_fsgnj);
  `TEST_CASE(test_fminmax);
  `TEST_CASE(test_invalid_fmt);
  `TEST_CASE(test_invalid_flw_funct3);
  `TEST_CASE(test_invalid_fsqrt_rs2);
  `TEST_CASE(test_non_fp);
  `TEST_SUITE_END();

endmodule
