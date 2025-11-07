//
// Zmmul extension test tasks
//
// These tests verify Zmmul multiply instructions in SoC context.
// Only included in testbenches with EXT_ZMMUL=1.
//

//
// Basic multiply tests
//
task automatic test_mul_basic;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, 20);
  MUL(x3, x1, x2);
  ADDI(x4, x0, -5);
  MUL(x5, x1, x4);
  MUL(x6, x4, x4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd20);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd200);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'hFFFFFFFB);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'hFFFFFFCE);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd25);
endtask

//
// MULH - signed × signed high bits
//
task automatic test_mulh_basic;
  ADDI(x1, x0, -1);
  ADDI(x2, x0, -1);
  MULH(x3, x1, x2);
  LUI(x4, 32'h80000000);
  LUI(x5, 32'h80000000);
  MULH(x6, x4, x5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'h40000000);
endtask

//
// MULHSU - signed × unsigned high bits
//
task automatic test_mulhsu_basic;
  ADDI(x1, x0, -1);
  ADDI(x2, x0, 1);
  MULHSU(x3, x1, x2);
  LUI(x4, 32'h80000000);
  ADDI(x5, x0, 2);
  MULHSU(x6, x4, x5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'hFFFFFFFF);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'hFFFFFFFF);
endtask

//
// MULHU - unsigned × unsigned high bits
//
task automatic test_mulhu_basic;
  ADDI(x1, x0, -1);
  ADDI(x2, x0, -1);
  MULHU(x3, x1, x2);
  LUI(x4, 32'hFFFFF000);
  ADDI(x4, x4, -1);
  ADDI(x5, x0, 2);
  MULHU(x6, x4, x5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'hFFFFFFFE);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd1);
endtask

//
// Multiply with data hazards (tests forwarding with multiply results)
//
task automatic test_mul_raw_dependency;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, 5);
  MUL(x3, x1, x2);
  ADDI(x4, x3, 100);
  MUL(x5, x3, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd50);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd150);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd250);
endtask

//
// Chained multiply dependencies (stress test for forwarding)
//
task automatic test_mul_chained_dependencies;
  ADDI(x1, x0, 2);
  MUL(x2, x1, x1);
  MUL(x3, x2, x1);
  MUL(x4, x3, x1);
  MUL(x5, x4, x1);
  MUL(x6, x5, x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd2);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd4);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd8);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd16);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd32);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd64);
endtask

//
// Mixed ALU and multiply operations
//
task automatic test_mul_mixed_ops;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, 5);
  ADD(x3, x1, x2);
  MUL(x4, x1, x2);
  SUB(x5, x4, x3);
  MUL(x6, x3, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd15);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd50);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd35);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd75);
endtask

//
// Multiply zero edge case
//
task automatic test_mul_zero;
  ADDI(x1, x0, 100);
  MUL(x2, x1, x0);
  MUL(x3, x0, x1);
  MUL(x4, x0, x0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd0);
endtask

//
// Large value multiplication
//
task automatic test_mul_large_values;
  LUI(x1, 32'h12345000);
  ADDI(x1, x1, 32'h678);
  LUI(x2, 32'h00010000);
  MUL(x3, x1, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'h56780000);
endtask
