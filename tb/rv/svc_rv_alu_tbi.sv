`include "svc_unit.sv"
`include "svc_rv_alu.sv"

module svc_rv_alu_tbi;
  `TEST_CLK_NS(clk, 10);

  `include "svc_rv_defs.svh"

  localparam int XLEN = 32;

  logic [XLEN-1:0] a;
  logic [XLEN-1:0] b;
  logic [     3:0] alu_op;
  logic [XLEN-1:0] result;

  svc_rv_alu #(
      .XLEN(XLEN)
  ) uut (
      .a     (a),
      .b     (b),
      .alu_op(alu_op),
      .result(result)
  );

  //
  // Test: ADD operation
  //
  task automatic test_add;
    alu_op = ALU_ADD;
    a      = 32'h00000000;
    b      = 32'h00000000;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'h00000001;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000002);

    a = 32'h12345678;
    b = 32'h87654321;
    `TICK(clk);
    `CHECK_EQ(result, 32'h99999999);

    a = 32'hFFFFFFFF;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'h7FFFFFFF;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h80000000);
  endtask

  //
  // Test: SUB operation
  //
  task automatic test_sub;
    alu_op = ALU_SUB;
    a      = 32'h00000002;
    b      = 32'h00000001;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000000;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);

    a = 32'h12345678;
    b = 32'h12345678;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'h80000000;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h7FFFFFFF);

    a = 32'h00000005;
    b = 32'h00000003;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000002);
  endtask

  //
  // Test: AND operation
  //
  task automatic test_and;
    alu_op = ALU_AND;
    a      = 32'h00000000;
    b      = 32'hFFFFFFFF;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'hFFFFFFFF;
    b = 32'hFFFFFFFF;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);

    a = 32'hAAAAAAAA;
    b = 32'h55555555;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'h12345678;
    b = 32'hFF00FF00;
    `TICK(clk);
    `CHECK_EQ(result, 32'h12005600);

    a = 32'h12345678;
    b = 32'h0F0F0F0F;
    `TICK(clk);
    `CHECK_EQ(result, 32'h02040608);
  endtask

  //
  // Test: OR operation
  //
  task automatic test_or;
    alu_op = ALU_OR;
    a      = 32'h00000000;
    b      = 32'h00000000;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'hFFFFFFFF;
    b = 32'h00000000;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);

    a = 32'hAAAAAAAA;
    b = 32'h55555555;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);

    a = 32'h12340000;
    b = 32'h00005678;
    `TICK(clk);
    `CHECK_EQ(result, 32'h12345678);

    a = 32'h12340000;
    b = 32'h00005678;
    `TICK(clk);
    `CHECK_EQ(result, 32'h12345678);
  endtask

  //
  // Test: XOR operation
  //
  task automatic test_xor;
    alu_op = ALU_XOR;
    a      = 32'h00000000;
    b      = 32'h00000000;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'hFFFFFFFF;
    b = 32'hFFFFFFFF;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'hAAAAAAAA;
    b = 32'h55555555;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);

    a = 32'hFFFF0000;
    b = 32'h0000FFFF;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);

    a = 32'hAAAAAAAA;
    b = 32'h55555555;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);
  endtask

  //
  // Test: SLT operation
  //
  task automatic test_slt;
    alu_op = ALU_SLT;
    a      = 32'h00000000;
    b      = 32'h00000001;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000001;
    b = 32'h00000000;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'hFFFFFFFF;
    b = 32'h00000000;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000000;
    b = 32'hFFFFFFFF;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'h80000000;
    b = 32'h7FFFFFFF;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h12345678;
    b = 32'h12345678;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'hFFFFFFFF;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);
  endtask

  //
  // Test: SLTU operation
  //
  task automatic test_sltu;
    alu_op = ALU_SLTU;
    a      = 32'h00000000;
    b      = 32'h00000001;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000001;
    b = 32'h00000000;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'hFFFFFFFF;
    b = 32'h00000000;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'h00000000;
    b = 32'hFFFFFFFF;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h80000000;
    b = 32'h7FFFFFFF;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000000);

    a = 32'h7FFFFFFF;
    b = 32'h80000000;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);
  endtask

  //
  // Test: SLL operation
  //
  task automatic test_sll;
    alu_op = ALU_SLL;
    a      = 32'h00000001;
    b      = 32'h00000000;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000001;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000002);

    a = 32'h00000001;
    b = 32'h00000004;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000010);

    a = 32'h12345678;
    b = 32'h00000008;
    `TICK(clk);
    `CHECK_EQ(result, 32'h34567800);

    a = 32'hFFFFFFFF;
    b = 32'h0000001F;
    `TICK(clk);
    `CHECK_EQ(result, 32'h80000000);

    a = 32'h00000001;
    b = 32'h00000020;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);
  endtask

  //
  // Test: SRL operation
  //
  task automatic test_srl;
    alu_op = ALU_SRL;
    a      = 32'h00000001;
    b      = 32'h00000000;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000002;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000010;
    b = 32'h00000004;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h12345678;
    b = 32'h00000008;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00123456);

    a = 32'hFFFFFFFF;
    b = 32'h0000001F;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h80000000;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h40000000);
  endtask

  //
  // Test: SRA operation
  //
  task automatic test_sra;
    alu_op = ALU_SRA;
    a      = 32'h00000001;
    b      = 32'h00000000;

    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000002;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h00000010;
    b = 32'h00000004;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00000001);

    a = 32'h80000000;
    b = 32'h00000001;
    `TICK(clk);
    `CHECK_EQ(result, 32'hC0000000);

    a = 32'hFFFFFFFF;
    b = 32'h0000001F;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);

    a = 32'h12345678;
    b = 32'h00000008;
    `TICK(clk);
    `CHECK_EQ(result, 32'h00123456);

    a = 32'h80000000;
    b = 32'h0000001F;
    `TICK(clk);
    `CHECK_EQ(result, 32'hFFFFFFFF);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_alu_tbi);
  `TEST_CASE(test_add);
  `TEST_CASE(test_sub);
  `TEST_CASE(test_and);
  `TEST_CASE(test_or);
  `TEST_CASE(test_xor);
  `TEST_CASE(test_slt);
  `TEST_CASE(test_sltu);
  `TEST_CASE(test_sll);
  `TEST_CASE(test_srl);
  `TEST_CASE(test_sra);
  `TEST_SUITE_END();

endmodule
