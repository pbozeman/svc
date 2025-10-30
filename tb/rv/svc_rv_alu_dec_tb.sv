`include "svc_unit.sv"
`include "svc_rv_alu_dec.sv"

module svc_rv_alu_dec_tb;
  `TEST_CLK_NS(clk, 10);

  `include "svc_rv_defs.svh"

  logic [1:0] alu_instr;
  logic [2:0] funct3;
  logic       funct7_b5;
  logic       op_b5;

  logic [3:0] alu_op;

  svc_rv_alu_dec uut (
      .alu_instr(alu_instr),
      .funct3   (funct3),
      .funct7_b5(funct7_b5),
      .op_b5    (op_b5),
      .alu_op   (alu_op)
  );

  //
  // Test: ADD for loads/stores
  //
  task automatic test_add_load_store;
    alu_instr = 2'b00;
    funct3    = 3'b000;
    funct7_b5 = 1'b0;
    op_b5     = 1'b0;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_ADD);
  endtask

  //
  // Test: SUB for branches
  //
  task automatic test_sub_branch;
    alu_instr = 2'b01;
    funct3    = 3'b000;
    funct7_b5 = 1'b0;
    op_b5     = 1'b0;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SUB);
  endtask

  //
  // Test: R-type ADD
  //
  task automatic test_rtype_add;
    alu_instr = 2'b10;
    funct3    = 3'b000;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_ADD);
  endtask

  //
  // Test: R-type SUB
  //
  task automatic test_rtype_sub;
    alu_instr = 2'b10;
    funct3    = 3'b000;
    funct7_b5 = 1'b1;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SUB);
  endtask

  //
  // Test: I-type ADDI with funct7_b5 set
  //
  task automatic test_itype_addi;
    alu_instr = 2'b10;
    funct3    = 3'b000;
    funct7_b5 = 1'b1;
    op_b5     = 1'b0;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_ADD);
  endtask

  //
  // Test: SLT operation
  //
  task automatic test_slt;
    alu_instr = 2'b10;
    funct3    = 3'b010;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SLT);
  endtask

  //
  // Test: XOR operation
  //
  task automatic test_xor;
    alu_instr = 2'b10;
    funct3    = 3'b100;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_XOR);
  endtask

  //
  // Test: OR operation
  //
  task automatic test_or;
    alu_instr = 2'b10;
    funct3    = 3'b110;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_OR);
  endtask

  //
  // Test: AND operation
  //
  task automatic test_and;
    alu_instr = 2'b10;
    funct3    = 3'b111;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_AND);
  endtask

  //
  // Test: SLTU operation
  //
  task automatic test_sltu;
    alu_instr = 2'b10;
    funct3    = 3'b011;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SLTU);
  endtask

  //
  // Test: SLL operation
  //
  task automatic test_sll;
    alu_instr = 2'b10;
    funct3    = 3'b001;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SLL);
  endtask

  //
  // Test: SRL operation
  //
  task automatic test_srl;
    alu_instr = 2'b10;
    funct3    = 3'b101;
    funct7_b5 = 1'b0;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SRL);
  endtask

  //
  // Test: SRA operation
  //
  task automatic test_sra;
    alu_instr = 2'b10;
    funct3    = 3'b101;
    funct7_b5 = 1'b1;
    op_b5     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SRA);
  endtask

  //
  // Test: All funct3 combinations with I-type
  //
  task automatic test_all_itype;
    alu_instr = 2'b10;
    op_b5     = 1'b0;
    funct7_b5 = 1'b0;

    funct3    = 3'b000;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_ADD);

    funct3 = 3'b010;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_SLT);

    funct3 = 3'b100;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_XOR);

    funct3 = 3'b110;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_OR);

    funct3 = 3'b111;
    `TICK(clk);
    `CHECK_EQ(alu_op, ALU_AND);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_alu_dec_tb);
  `TEST_CASE(test_add_load_store);
  `TEST_CASE(test_sub_branch);
  `TEST_CASE(test_rtype_add);
  `TEST_CASE(test_rtype_sub);
  `TEST_CASE(test_itype_addi);
  `TEST_CASE(test_slt);
  `TEST_CASE(test_sltu);
  `TEST_CASE(test_sll);
  `TEST_CASE(test_srl);
  `TEST_CASE(test_sra);
  `TEST_CASE(test_xor);
  `TEST_CASE(test_or);
  `TEST_CASE(test_and);
  `TEST_CASE(test_all_itype);
  `TEST_SUITE_END();

endmodule
