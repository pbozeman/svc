//
// Division and remainder instruction test tasks
//
// These tests verify division and remainder instructions (DIV, DIVU, REM, REMU).
// Used by M extension (EXT_M=1) testbenches.
//

//
// Basic division tests (DIV - signed division)
//
task automatic test_div_basic;
  ADDI(x1, x0, 20);
  ADDI(x2, x0, 3);
  DIV(x3, x1, x2);
  ADDI(x4, x0, -20);
  DIV(x5, x4, x2);
  DIV(x6, x1, x4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 256);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd20);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd3);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd6);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'hFFFFFFEC);
  `CHECK_EQ($signed(uut.cpu.regfile.regs[5]), -32'sd6);
  `CHECK_EQ($signed(uut.cpu.regfile.regs[6]), -32'sd1);
endtask

//
// DIVU - unsigned division
//
task automatic test_divu_basic;
  ADDI(x1, x0, 20);
  ADDI(x2, x0, 3);
  DIVU(x3, x1, x2);
  ADDI(x4, x0, -1);
  ADDI(x5, x0, 2);
  DIVU(x6, x4, x5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd6);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'h7FFFFFFF);
endtask

//
// REM - signed remainder
//
task automatic test_rem_basic;
  ADDI(x1, x0, 20);
  ADDI(x2, x0, 3);
  REM(x3, x1, x2);
  ADDI(x4, x0, -20);
  REM(x5, x4, x2);
  REM(x6, x1, x4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd2);
  `CHECK_EQ($signed(uut.cpu.regfile.regs[5]), -32'sd2);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd0);
endtask

//
// REMU - unsigned remainder
//
task automatic test_remu_basic;
  ADDI(x1, x0, 20);
  ADDI(x2, x0, 3);
  REMU(x3, x1, x2);
  ADDI(x4, x0, -1);
  ADDI(x5, x0, 2);
  REMU(x6, x4, x5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd2);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd1);
endtask

//
// Division by zero
//
task automatic test_div_by_zero;
  ADDI(x1, x0, 10);
  DIV(x2, x1, x0);
  DIVU(x3, x1, x0);
  REM(x4, x1, x0);
  REMU(x5, x1, x0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hFFFFFFFF);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'hFFFFFFFF);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd10);
endtask

//
// Division overflow (most negative / -1)
//
task automatic test_div_overflow;
  LUI(x1, 32'h80000000);
  ADDI(x2, x0, -1);
  DIV(x3, x1, x2);
  REM(x4, x1, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'h80000000);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd0);
endtask

//
// Division with data hazards (tests forwarding/stalling with div results)
//
task automatic test_div_raw_dependency;
  ADDI(x1, x0, 20);
  ADDI(x2, x0, 4);
  DIV(x3, x1, x2);
  ADDI(x4, x3, 100);
  DIV(x5, x3, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd5);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd105);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd1);
endtask

//
// Chained division dependencies
//
task automatic test_div_chained_dependencies;
  ADDI(x1, x0, 100);
  ADDI(x2, x0, 2);
  DIV(x3, x1, x2);
  DIV(x4, x3, x2);
  DIV(x5, x4, x2);
  DIV(x6, x5, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 512);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd50);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd25);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd12);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd6);
endtask

//
// Mixed ALU and division operations
//
task automatic test_div_mixed_ops;
  ADDI(x1, x0, 20);
  ADDI(x2, x0, 3);
  ADD(x3, x1, x2);
  DIV(x4, x1, x2);
  SUB(x5, x4, x3);
  REM(x6, x1, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd23);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd6);
  `CHECK_EQ($signed(uut.cpu.regfile.regs[5]), -32'sd17);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd2);
endtask

//
// Mixed multiply and divide
//
task automatic test_mul_div_mixed;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, 5);
  MUL(x3, x1, x2);
  DIV(x4, x3, x2);
  DIV(x5, x3, x1);
  REM(x6, x3, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 512);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd50);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd5);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd0);
endtask
