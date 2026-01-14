`include "svc_unit.sv"
`include "svc_rv_ext_fp_ex.sv"

module svc_rv_ext_fp_ex_tbv;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  `include "svc_rv_defs.svh"

  //
  // DUT signals
  //
  logic        op_valid;
  logic [31:0] instr;
  logic [ 2:0] fp_rm;
  logic        fp_rm_dyn;
  logic [ 2:0] frm_csr;
  logic [31:0] fp_rs1;
  logic [31:0] fp_rs2;
  logic [31:0] fp_rs3;
  logic [31:0] rs1;
  logic        result_valid;
  logic [31:0] result;
  logic [ 4:0] fflags;
  logic        busy;

  //
  // DUT instantiation
  //
  svc_rv_ext_fp_ex uut (
      .clk         (clk),
      .rst_n       (rst_n),
      .op_valid    (op_valid),
      .instr       (instr),
      .fp_rm       (fp_rm),
      .fp_rm_dyn   (fp_rm_dyn),
      .frm_csr     (frm_csr),
      .fp_rs1      (fp_rs1),
      .fp_rs2      (fp_rs2),
      .fp_rs3      (fp_rs3),
      .rs1         (rs1),
      .result_valid(result_valid),
      .result      (result),
      .fflags      (fflags),
      .busy        (busy)
  );

  //
  // IEEE 754 single-precision constants
  //
  localparam logic [31:0] FP_ZERO = 32'h00000000;  // 0.0
  localparam logic [31:0] FP_ONE = 32'h3F800000;  // 1.0
  localparam logic [31:0] FP_TWO = 32'h40000000;  // 2.0
  localparam logic [31:0] FP_THREE = 32'h40400000;  // 3.0
  localparam logic [31:0] FP_FOUR = 32'h40800000;  // 4.0
  localparam logic [31:0] FP_FIVE = 32'h40A00000;  // 5.0
  localparam logic [31:0] FP_SIX = 32'h40C00000;  // 6.0
  localparam logic [31:0] FP_SEVEN = 32'h40E00000;  // 7.0
  localparam logic [31:0] FP_NEG_ONE = 32'hBF800000;  // -1.0
  localparam logic [31:0] FP_NEG_THREE = 32'hC0400000;  // -3.0
  localparam logic [31:0] FP_PI = 32'h40490FDB;  // ~3.14159
  localparam logic [31:0] FP_INF = 32'h7F800000;  // +infinity

  //
  // Exception flag masks
  //
  localparam logic [4:0] FLAG_NV = 5'b10000;  // Invalid operation
  localparam logic [4:0] FLAG_DZ = 5'b01000;  // Divide by zero
  localparam logic [4:0] FLAG_NX = 5'b00001;  // Inexact

  //
  // Instruction builders
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

  // Captured result (since result_valid goes low when op_valid goes low)
  logic [31:0] captured_result;
  logic [ 4:0] captured_fflags;

  //
  // Helper to run operation and wait for result
  //
  localparam int TIMEOUT_CYCLES = 1000;

  task automatic run_op();
    int cycle_count;
    // Extract rounding mode from instruction (like ID stage)
    fp_rm       = instr[14:12];
    fp_rm_dyn   = (instr[14:12] == FRM_DYN);
    op_valid    = 1'b1;
    cycle_count = 0;
    // Keep op_valid high until result is ready
    while (!result_valid && cycle_count < TIMEOUT_CYCLES) begin
      `TICK(clk);
      cycle_count++;
    end
    if (cycle_count >= TIMEOUT_CYCLES) begin
      $error("run_op timed out waiting for result_valid");
    end
    `CHECK_TRUE(result_valid);
    // Capture results while still valid
    captured_result = result;
    captured_fflags = fflags;
    op_valid        = 1'b0;
  endtask

  // Alias for multi-cycle operations (same logic)
  task automatic run_mc_op();
    run_op();
  endtask

  //
  // Setup
  //
  task automatic setup();
    op_valid  = 1'b0;
    instr     = 32'h0;
    fp_rm     = FRM_RNE;
    fp_rm_dyn = 1'b0;
    frm_csr   = FRM_RNE;
    fp_rs1    = FP_ZERO;
    fp_rs2    = FP_ZERO;
    fp_rs3    = FP_ZERO;
    rs1       = 32'h0;
  endtask

  //
  // Test: FADD.S - 1.0 + 2.0 = 3.0
  //
  task automatic test_fadd_basic();
    instr  = make_fp_r(FP7_FADD, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_ONE;
    fp_rs2 = FP_TWO;

    run_op();

    `CHECK_EQ(captured_result, FP_THREE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FSUB.S - 5.0 - 2.0 = 3.0
  //
  task automatic test_fsub_basic();
    instr  = make_fp_r(FP7_FSUB, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_FIVE;
    fp_rs2 = FP_TWO;

    run_op();


    `CHECK_EQ(captured_result, FP_THREE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FMUL.S - 2.0 * 3.0 = 6.0
  //
  task automatic test_fmul_basic();
    instr  = make_fp_r(FP7_FMUL, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_TWO;
    fp_rs2 = FP_THREE;

    run_op();


    `CHECK_EQ(captured_result, FP_SIX);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FDIV.S - 6.0 / 2.0 = 3.0 (multi-cycle)
  //
  task automatic test_fdiv_basic();
    instr  = make_fp_r(FP7_FDIV, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_SIX;
    fp_rs2 = FP_TWO;

    run_mc_op();


    `CHECK_EQ(captured_result, FP_THREE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FSQRT.S - sqrt(4.0) = 2.0 (multi-cycle)
  //
  task automatic test_fsqrt_basic();
    instr  = make_fp_r(FP7_FSQRT, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_FOUR;
    fp_rs2 = FP_ZERO;

    run_mc_op();


    `CHECK_EQ(captured_result, FP_TWO);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FMIN.S - min(3.0, 5.0) = 3.0
  //
  task automatic test_fmin_basic();
    instr  = make_fp_r(FP7_FMINMAX, 5'd0, 5'd0, FP3_FMIN, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_FIVE;

    run_op();


    `CHECK_EQ(captured_result, FP_THREE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FMAX.S - max(3.0, 5.0) = 5.0
  //
  task automatic test_fmax_basic();
    instr  = make_fp_r(FP7_FMINMAX, 5'd0, 5'd0, FP3_FMAX, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_FIVE;

    run_op();


    `CHECK_EQ(captured_result, FP_FIVE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FMV.X.W - move float bits to integer (bypass FPU)
  //
  task automatic test_fmv_x_w();
    instr  = make_fp_r(FP7_FMVXW, 5'd0, 5'd0, FP3_FMV, 5'd0);
    fp_rs1 = FP_PI;

    run_op();


    `CHECK_EQ(captured_result, FP_PI);
    `CHECK_EQ(captured_fflags, 5'b0);
    `CHECK_FALSE(busy);
  endtask

  //
  // Test: FMV.W.X - move integer bits to float (bypass FPU)
  //
  task automatic test_fmv_w_x();
    instr = make_fp_r(FP7_FMVWX, 5'd0, 5'd0, 3'b000, 5'd0);
    rs1   = FP_TWO;

    run_op();


    `CHECK_EQ(captured_result, FP_TWO);
    `CHECK_EQ(captured_fflags, 5'b0);
    `CHECK_FALSE(busy);
  endtask

  //
  // Test: FCVT.W.S - convert 3.0 to signed int = 3
  //
  task automatic test_fcvt_w_s();
    // rs2[0] = 0 for signed
    instr  = make_fp_r(FP7_FCVTWS, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_THREE;

    run_op();


    `CHECK_EQ(captured_result, 32'd3);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FCVT.S.W - convert signed int 5 to 5.0
  //
  task automatic test_fcvt_s_w();
    // rs2[0] = 0 for signed
    instr = make_fp_r(FP7_FCVTSW, 5'd0, 5'd0, FRM_RNE, 5'd0);
    rs1   = 32'd5;

    run_op();


    `CHECK_EQ(captured_result, FP_FIVE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FMADD.S - (2.0 * 3.0) + 1.0 = 7.0
  //
  task automatic test_fmadd_basic();
    instr  = make_fma(OP_FMADD, 5'd0, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_TWO;
    fp_rs2 = FP_THREE;
    fp_rs3 = FP_ONE;

    run_op();


    `CHECK_EQ(captured_result, FP_SEVEN);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FMSUB.S - (2.0 * 3.0) - 1.0 = 5.0
  //
  task automatic test_fmsub_basic();
    instr  = make_fma(OP_FMSUB, 5'd0, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_TWO;
    fp_rs2 = FP_THREE;
    fp_rs3 = FP_ONE;

    run_op();


    `CHECK_EQ(captured_result, FP_FIVE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FSGNJ.S - copy sign from fp_rs2
  //
  task automatic test_fsgnj_basic();
    instr  = make_fp_r(FP7_FSGNJ, 5'd0, 5'd0, FP3_FSGNJ, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_NEG_ONE;

    run_op();


    // Result should be -3.0 (magnitude of fp_rs1, sign of fp_rs2)
    `CHECK_EQ(captured_result, FP_NEG_THREE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FSGNJN.S - copy negated sign from fp_rs2
  //
  task automatic test_fsgnjn_basic();
    instr  = make_fp_r(FP7_FSGNJ, 5'd0, 5'd0, FP3_FSGNJN, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_NEG_ONE;

    run_op();


    // Result should be +3.0 (magnitude of fp_rs1, negated sign of fp_rs2)
    `CHECK_EQ(captured_result, FP_THREE);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FEQ.S - 3.0 == 3.0 -> 1
  //
  task automatic test_feq_equal();
    instr  = make_fp_r(FP7_FCMP, 5'd0, 5'd0, FP3_FEQ, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_THREE;

    run_op();


    `CHECK_EQ(captured_result, 32'd1);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FEQ.S - 3.0 == 5.0 -> 0
  //
  task automatic test_feq_not_equal();
    instr  = make_fp_r(FP7_FCMP, 5'd0, 5'd0, FP3_FEQ, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_FIVE;

    run_op();


    `CHECK_EQ(captured_result, 32'd0);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FLT.S - 3.0 < 5.0 -> 1
  //
  task automatic test_flt_true();
    instr  = make_fp_r(FP7_FCMP, 5'd0, 5'd0, FP3_FLT, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_FIVE;

    run_op();


    `CHECK_EQ(captured_result, 32'd1);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FLE.S - 3.0 <= 3.0 -> 1
  //
  task automatic test_fle_equal();
    instr  = make_fp_r(FP7_FCMP, 5'd0, 5'd0, FP3_FLE, 5'd0);
    fp_rs1 = FP_THREE;
    fp_rs2 = FP_THREE;

    run_op();


    `CHECK_EQ(captured_result, 32'd1);
    `CHECK_EQ(captured_fflags, 5'b0);
  endtask

  //
  // Test: FDIV.S by zero raises DZ flag
  //
  task automatic test_fdiv_zero();
    instr  = make_fp_r(FP7_FDIV, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_ONE;
    fp_rs2 = FP_ZERO;

    run_mc_op();


    `CHECK_EQ(captured_result, FP_INF);
    `CHECK_EQ(captured_fflags & FLAG_DZ, FLAG_DZ);
  endtask

  //
  // Test: FSQRT.S of negative raises NV flag
  //
  task automatic test_fsqrt_neg();
    instr  = make_fp_r(FP7_FSQRT, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_NEG_ONE;

    run_mc_op();


    // Result should be NaN
    `CHECK_EQ(captured_result[30:23], 8'hFF);  // Exponent all 1s
    `CHECK_TRUE(captured_result[22:0] != 0);  // Non-zero mantissa (NaN)
    `CHECK_EQ(captured_fflags & FLAG_NV, FLAG_NV);
  endtask

  //
  // Test: FADD.S with inexact result (1.0 + PI)
  //
  task automatic test_fadd_inexact();
    instr  = make_fp_r(FP7_FADD, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_ONE;
    fp_rs2 = FP_PI;

    run_op();


    // 1.0 + PI is inexact
    `CHECK_EQ(captured_fflags & FLAG_NX, FLAG_NX);
  endtask

  //
  // Test: Dynamic rounding mode (use frm_csr)
  //
  task automatic test_dynamic_rm();
    // Use dynamic rounding (rm = 111)
    instr   = make_fp_r(FP7_FADD, 5'd0, 5'd0, FRM_DYN, 5'd0);
    frm_csr = FRM_RTZ;  // Round towards zero
    fp_rs1  = FP_ONE;
    fp_rs2  = FP_PI;

    run_op();


    // With RTZ, the inexact flag should still be set
    `CHECK_EQ(captured_fflags & FLAG_NX, FLAG_NX);
  endtask

  //
  // Test: Single-cycle op after multi-cycle op uses correct result
  //
  // Regression test: mc_result_valid_reg could stay high after a multi-cycle
  // op completed, causing subsequent single-cycle ops to incorrectly use the
  // stale mc_result_reg instead of fpu_result.
  //
  task automatic test_single_cycle_after_multicycle();
    // First: run a multi-cycle FSQRT: sqrt(9.0) = 3.0
    instr  = make_fp_r(FP7_FSQRT, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = 32'h41100000;  // 9.0
    fp_rs2 = FP_ZERO;

    run_mc_op();
    `CHECK_EQ(captured_result, FP_THREE);

    // Wait one more cycle for mc_result_valid_reg to be set (as it would be
    // in the real pipeline when the next instruction arrives)
    `TICK(clk);

    // Now run a single-cycle FADD: 1.0 + 1.0 = 2.0
    // Bug: without the is_multicycle check, this would return 3.0 (the stale
    // mc_result_reg from FSQRT) instead of 2.0
    instr  = make_fp_r(FP7_FADD, 5'd0, 5'd0, FRM_RNE, 5'd0);
    fp_rs1 = FP_ONE;
    fp_rs2 = FP_ONE;

    run_op();

    `CHECK_EQ(captured_result, FP_TWO);
  endtask

  // =========================================================================
  // Test Suite
  // =========================================================================
  `TEST_SUITE_BEGIN(svc_rv_ext_fp_ex_tbv);
  `TEST_SETUP(setup);

  `TEST_CASE(test_fadd_basic);
  `TEST_CASE(test_fsub_basic);
  `TEST_CASE(test_fmul_basic);
  `TEST_CASE(test_fdiv_basic);
  `TEST_CASE(test_fsqrt_basic);
  `TEST_CASE(test_fmin_basic);
  `TEST_CASE(test_fmax_basic);
  `TEST_CASE(test_fmv_x_w);
  `TEST_CASE(test_fmv_w_x);
  `TEST_CASE(test_fcvt_w_s);
  `TEST_CASE(test_fcvt_s_w);
  `TEST_CASE(test_fmadd_basic);
  `TEST_CASE(test_fmsub_basic);
  `TEST_CASE(test_fsgnj_basic);
  `TEST_CASE(test_fsgnjn_basic);
  `TEST_CASE(test_feq_equal);
  `TEST_CASE(test_feq_not_equal);
  `TEST_CASE(test_flt_true);
  `TEST_CASE(test_fle_equal);
  `TEST_CASE(test_fdiv_zero);
  `TEST_CASE(test_fsqrt_neg);
  `TEST_CASE(test_fadd_inexact);
  `TEST_CASE(test_dynamic_rm);
  `TEST_CASE(test_single_cycle_after_multicycle);

  `TEST_SUITE_END();

endmodule
