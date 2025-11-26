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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd20);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd3);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd6);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'hFFFFFFEC);
  `CHECK_EQ($signed(uut.cpu.stage_id.regfile.regs[5]), -32'sd6);
  `CHECK_EQ($signed(uut.cpu.stage_id.regfile.regs[6]), -32'sd1);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd6);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'h7FFFFFFF);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd2);
  `CHECK_EQ($signed(uut.cpu.stage_id.regfile.regs[5]), -32'sd2);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd0);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd2);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd1);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hFFFFFFFF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'hFFFFFFFF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd10);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h80000000);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd0);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd105);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd1);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd50);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd25);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd12);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd6);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd23);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd6);
  `CHECK_EQ($signed(uut.cpu.stage_id.regfile.regs[5]), -32'sd17);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd2);
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
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd50);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd0);
endtask

//
// MMIO bug test: STORE followed by multi-cycle DIV
//
// This test triggers a bug where memory writes repeat during pipeline stalls.
// When a STORE is in MEM stage and a DIV starts in EX stage, the pipeline
// stalls but the MEM stage continues to assert dmem_we with the same address,
// causing repeated writes to MMIO addresses.
//
task automatic test_store_div_mmio_bug;
  ADDI(x3, x0, 100);
  ADDI(x4, x0, 3);
  LI(x1, 32'h80000000);
  LI(x2, 32'hDEADBEEF);
  NOP();
  NOP();
  SW(x2, x1, 0);
  DIV(x5, x3, x4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 256);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd33);
endtask

//
// Branch flush div test: taken branch followed by DIV
//
// This test verifies that the mc_state FSM properly resets when a branch
// mispredicts while a DIV instruction is in the EX stage. Without the fix,
// mc_state would stay in MC_STATE_EXEC, causing pipeline stalls and
// incorrect RVFI pc_wdata reporting.
//
// Sequence:
//   1. BEQ x0, x0 (always taken, forward branch)
//   2. DIV instruction (fetched but should be flushed)
//   3. Branch target: ADDI to set result register
//
task automatic test_branch_flush_div;
  //
  // x1 = 100, x2 = 3 (div operands that should never execute)
  //
  ADDI(x1, x0, 100);
  ADDI(x2, x0, 3);
  //
  // x3 = 42 (marker value, should not be overwritten by flushed div)
  //
  ADDI(x3, x0, 42);
  //
  // BEQ x0, x0 always taken, skip the DIV
  // Branch forward 8 bytes (skip DIV instruction)
  //
  BEQ(x0, x0, 8);
  //
  // This DIV should be flushed and never execute
  //
  DIV(x3, x1, x2);
  //
  // Branch target: set x4 = 123 to verify we got here
  //
  ADDI(x4, x0, 123);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 256);
  //
  // x3 should still be 42 (DIV was flushed, not executed)
  //
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd42);
  //
  // x4 should be 123 (branch target executed)
  //
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd123);
endtask

//
// Test: Misaligned load during DIV start
//
// This test triggers a bug where trap information is lost when a misaligned
// load is in MEM stage at the same time a DIV starts in EX stage. Without
// the fix, trap_wb wouldn't be updated because mem_wb_stall = 1.
//
// The test issues a misaligned LW followed immediately by a DIV to create
// the race condition. The trap signal should fire for the misaligned access.
//
task automatic test_misaligned_load_div_trap;
  //
  // Setup: x1 = address with offset 1 (misaligned for LW)
  //
  LI(x1, 32'h00000100);
  ADDI(x2, x0, 10);
  ADDI(x3, x0, 2);
  NOP();
  NOP();

  // Misaligned LW (address + 1 = odd address, misaligned for word access)
  // Followed immediately by DIV to trigger the race condition
  LW(x4, x1, 1);
  DIV(x5, x2, x3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.trap);
  `CHECK_FALSE(ebreak);
  `TICK(clk);

  // we currently just allow traps to pass
  `CHECK_FALSE(uut.trap);
  `CHECK_WAIT_FOR_EBREAK(clk, 256);
endtask

//
// Test: DIV instruction count verification
//
// Verifies that the instruction counter correctly counts 2 instructions
// (ADDI + DIV) during execution.
//
task automatic test_div_instret_count;
  // Setup: x1 = 2, x2 = 4
  ADDI(x1, x0, 2);
  ADDI(x2, x0, 4);

  // Start instruction count
  RDINSTRET(x10);

  // Execute 2 instructions: ADDI and DIV
  ADDI(x3, x0, 1);
  DIV(x4, x2, x1);

  // Stop instruction count
  RDINSTRET(x11);

  // Calculate instruction count delta
  SUB(x12, x11, x10);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 256);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd2);

  // Delta is 3: RDINSTRET x10 + ADDI + DIV
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[12], 32'd3);
endtask
