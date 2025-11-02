`include "svc_unit.sv"

`include "svc_rv_bcmp.sv"

module svc_rv_bcmp_tb;
  `TEST_CLK_NS(clk, 10);

  localparam int XLEN = 32;

  logic [XLEN-1:0] a;
  logic [XLEN-1:0] b;
  logic [     2:0] funct3;
  logic            branch_taken_ex;
  logic            rs_eq_lo;
  logic            rs_lt_u_lo;
  logic            rs_lt_s_lo;

  svc_rv_bcmp #(
      .XLEN(XLEN)
  ) uut (
      // ID stage partial comparisons
      .a_id         (a),
      .b_id         (b),
      .rs_eq_lo_id  (rs_eq_lo),
      .rs_lt_u_lo_id(rs_lt_u_lo),
      .rs_lt_s_lo_id(rs_lt_s_lo),

      // EX stage final comparison (using same values as ID for testbench)
      .a_ex           (a),
      .b_ex           (b),
      .funct3         (funct3),
      .rs_eq_lo_ex    (rs_eq_lo),
      .rs_lt_u_lo_ex  (rs_lt_u_lo),
      .rs_lt_s_lo_ex  (rs_lt_s_lo),
      .branch_taken_ex(branch_taken_ex)
  );

  `include "svc_rv_defs.svh"

  //
  // Test: BEQ - Branch if equal
  //
  task automatic test_beq;
    //
    // Equal values
    //
    a      = 32'd42;
    b      = 32'd42;
    funct3 = FUNCT3_BEQ;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Not equal values
    //
    a      = 32'd42;
    b      = 32'd43;
    funct3 = FUNCT3_BEQ;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);

    //
    // Zero values
    //
    a      = 32'd0;
    b      = 32'd0;
    funct3 = FUNCT3_BEQ;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);
  endtask

  //
  // Test: BNE - Branch if not equal
  //
  task automatic test_bne;
    //
    // Not equal values
    //
    a      = 32'd42;
    b      = 32'd43;
    funct3 = FUNCT3_BNE;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Equal values
    //
    a      = 32'd42;
    b      = 32'd42;
    funct3 = FUNCT3_BNE;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);

    //
    // Large values
    //
    a      = 32'hFFFFFFFF;
    b      = 32'hFFFFFFFE;
    funct3 = FUNCT3_BNE;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);
  endtask

  //
  // Test: BLT - Branch if less than (signed)
  //
  task automatic test_blt;
    //
    // Negative < Positive
    //
    a      = 32'hFFFFFFF6;
    b      = 32'd10;
    funct3 = FUNCT3_BLT;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Positive < Positive
    //
    a      = 32'd5;
    b      = 32'd10;
    funct3 = FUNCT3_BLT;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Positive >= Negative
    //
    a      = 32'd10;
    b      = 32'hFFFFFFF6;
    funct3 = FUNCT3_BLT;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);

    //
    // Equal values
    //
    a      = 32'd42;
    b      = 32'd42;
    funct3 = FUNCT3_BLT;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);
  endtask

  //
  // Test: BGE - Branch if greater than or equal (signed)
  //
  task automatic test_bge;
    //
    // Positive >= Negative
    //
    a      = 32'd10;
    b      = 32'hFFFFFFF6;
    funct3 = FUNCT3_BGE;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Equal values
    //
    a      = 32'd42;
    b      = 32'd42;
    funct3 = FUNCT3_BGE;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Negative < Positive
    //
    a      = 32'hFFFFFFF6;
    b      = 32'd10;
    funct3 = FUNCT3_BGE;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);

    //
    // Positive < Positive
    //
    a      = 32'd5;
    b      = 32'd10;
    funct3 = FUNCT3_BGE;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);
  endtask

  //
  // Test: BLTU - Branch if less than (unsigned)
  //
  task automatic test_bltu;
    //
    // Small < Large unsigned
    //
    a      = 32'd10;
    b      = 32'hFFFFFFF6;
    funct3 = FUNCT3_BLTU;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Small < Small unsigned
    //
    a      = 32'd5;
    b      = 32'd10;
    funct3 = FUNCT3_BLTU;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Large >= Small unsigned
    //
    a      = 32'hFFFFFFF6;
    b      = 32'd10;
    funct3 = FUNCT3_BLTU;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);

    //
    // Equal values
    //
    a      = 32'd42;
    b      = 32'd42;
    funct3 = FUNCT3_BLTU;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);
  endtask

  //
  // Test: BGEU - Branch if greater than or equal (unsigned)
  //
  task automatic test_bgeu;
    //
    // Large >= Small unsigned
    //
    a      = 32'hFFFFFFF6;
    b      = 32'd10;
    funct3 = FUNCT3_BGEU;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Equal values
    //
    a      = 32'd42;
    b      = 32'd42;
    funct3 = FUNCT3_BGEU;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // Small < Large unsigned
    //
    a      = 32'd10;
    b      = 32'hFFFFFFF6;
    funct3 = FUNCT3_BGEU;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);

    //
    // Zero comparison
    //
    a      = 32'd0;
    b      = 32'd0;
    funct3 = FUNCT3_BGEU;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);
  endtask

  //
  // Test: Edge cases
  //
  task automatic test_edge_cases;
    //
    // Max signed vs min signed (BLT)
    //
    a      = 32'h7FFFFFFF;
    b      = 32'h80000000;
    funct3 = FUNCT3_BLT;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);

    //
    // Max signed vs min signed (BLTU)
    //
    a      = 32'h7FFFFFFF;
    b      = 32'h80000000;
    funct3 = FUNCT3_BLTU;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    //
    // All ones vs zero
    //
    a      = 32'hFFFFFFFF;
    b      = 32'd0;
    funct3 = FUNCT3_BLT;
    `TICK(clk);
    `CHECK_TRUE(branch_taken_ex);

    a      = 32'hFFFFFFFF;
    b      = 32'd0;
    funct3 = FUNCT3_BLTU;
    `TICK(clk);
    `CHECK_FALSE(branch_taken_ex);
  endtask

  //
  // Test setup
  //
  `TEST_SUITE_BEGIN(svc_rv_bcmp_tb);

  `TEST_CASE(test_beq);
  `TEST_CASE(test_bne);
  `TEST_CASE(test_blt);
  `TEST_CASE(test_bge);
  `TEST_CASE(test_bltu);
  `TEST_CASE(test_bgeu);
  `TEST_CASE(test_edge_cases);

  `TEST_SUITE_END();

endmodule
