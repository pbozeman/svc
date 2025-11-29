//
// Common test setup for RISC-V SoC testbenches
//
// This file provides the common infrastructure needed by all SoC tests:
// - Memory array for program storage
// - Assembly support macros
// - EBREAK waiting macro
// - Reset handling for assembly state
// - load_program task
//

logic [31:0] MEM[1024];
`include "svc_rv_asm.svh"

`define CHECK_WAIT_FOR_EBREAK(clk, n = 128) `CHECK_WAIT_FOR(clk, ebreak, n)

// CHECK_XXX don't work on strings or reals, so we partially reimplement
// the checks here. String/Real detection in the core macros would be nice.
`define CHECK_CPI(name, max_cpi, cycles, instrs)                              \
  begin                                                                       \
    real cpi_real;                                                            \
    string msg;                                                               \
    cpi_real = real'(cycles) / real'(instrs);                                 \
    if (cpi_report_en) begin                                                  \
      $display("\nCPI: %-70s  %8d  %8d   %4.4f  %4.4f%s",                     \
               {svc_tb_module_name, ".", name}, cycles, instrs, cpi_real,     \
               max_cpi, (cpi_real < (max_cpi * 0.95)) ? "  WIN" : "");        \
    end                                                                       \
    if (cpi_real > max_cpi) begin                                             \
      $sformat(msg, "%s%s%s:%s%0d%s CHECK_LTE(%scpi_real%s=%f, max_cpi=%f)",  \
               `COLOR_YELLOW, `__FILE__, `COLOR_RESET,                        \
               `COLOR_RED, `__LINE__, `COLOR_RESET,                           \
               `COLOR_YELLOW, `COLOR_RESET, cpi_real, max_cpi);               \
      `FATAL_MSG(msg);                                                        \
    end                                                                       \
  end

//
// CPI reporting control
//
bit          cpi_report_en;

//
// MMIO duplicate write detection
//
logic [31:0] prev_pc_mem;
bit          mmio_dup_detected;

initial begin
  bit svc_tb_rpt;
  if ($value$plusargs("SVC_TB_RPT=%b", svc_tb_rpt) && svc_tb_rpt) begin
    cpi_report_en = 1;
  end
end

//
// Reset assembly state on reset
//
always_ff @(posedge clk) begin
  if (!rst_n) begin
    asm_pc <= 0;
    for (int i = 0; i < 1024; i++) begin
      MEM[i] <= 32'b0;
    end
  end
end

//
// Initialize regfile to 0 in simulation
//
// The regfile has no reset logic for timing/fanout reasons, but tests
// expect deterministic values. This test-only block zeroes all registers
// during reset.
//
always_ff @(posedge clk) begin
  if (!rst_n) begin
    for (int i = 0; i < 32; i++) begin
      uut.cpu.stage_id.regfile.regs[i] <= '0;
    end
  end
end

//
// MMIO duplicate write detector
//
always_ff @(posedge clk) begin
  if (!rst_n) begin
    prev_pc_mem       <= '0;
    mmio_dup_detected <= 1'b0;
  end else begin
    prev_pc_mem <= uut.cpu.pc_plus4_mem;

    if (io_wen && (uut.cpu.pc_plus4_mem == prev_pc_mem)) begin
      mmio_dup_detected <= 1'b1;
    end
  end
end

//
// Automatic failure on MMIO duplicate write
//
// (using negedge because of a subtle timing bug and expectations in other
// tests, this ensures we don't tiny_tick unexpectedly)
//
always @(negedge clk) begin
  `CHECK_FALSE(mmio_dup_detected);
end

task automatic load_program;
  int i;
  for (i = 0; i < 1024; i++) begin
    uut.imem.mem[i] = MEM[i];
  end
endtask

//
// Shared test cases for RISC-V SoC testbenches
//
// This file contains all test tasks and the test suite setup that can be
// included by different testbench configurations (passthrough, pipelined, etc.)
//

//
//--------------------------------------------------------------------
// Basic tests
//--------------------------------------------------------------------
//

//
// Test: EBREAK instruction
//
// Verifies the EBREAK instruction asserts the ebreak signal and halts.
//
task automatic test_ebreak;
  NOP();
  EBREAK();
  NOP();

  load_program();

  `CHECK_FALSE(ebreak);

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_TRUE(ebreak);

  `TICK(clk);
  `CHECK_TRUE(ebreak);
endtask

//
//--------------------------------------------------------------------
// Tests with no register dependencies (all read from x0)
//--------------------------------------------------------------------
//

//
// Test: ADDI from x0
//
// Tests ADDI with various immediate values (positive, negative, zero, and
// boundary values). All source from x0 to avoid register dependencies.
//
task automatic test_addi_from_x0;
  ADDI(x1, x0, 42);
  ADDI(x2, x0, -50);
  ADDI(x3, x0, 0);
  ADDI(x4, x0, 2047);
  ADDI(x5, x0, -2048);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hFFFFFFCE);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd2047);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'hFFFFF800);
endtask

//
// Test: Logical I-type from x0
//
// Tests XORI, ORI, and ANDI instructions. All source from x0 to verify
// basic logical operation correctness without dependencies.
//
task automatic test_logical_from_x0;
  XORI(x1, x0, 255);
  ORI(x2, x0, 240);
  ANDI(x3, x0, 15);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd255);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd240);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
endtask

//
// Test: Shift I-type from x0
//
// Tests SLLI, SRLI, and SRAI instructions with x0 as source. All results
// should be zero since shifting zero produces zero.
//
task automatic test_shift_from_x0;
  SLLI(x1, x0, 5);
  SRLI(x2, x0, 2);
  SRAI(x3, x0, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
endtask

//
// Test: Compare I-type from x0
//
// Tests SLTI and SLTIU instructions comparing zero against various
// immediates to verify signed and unsigned comparison logic.
//
task automatic test_compare_from_x0;
  SLTI(x1, x0, 10);
  SLTI(x2, x0, -10);
  SLTIU(x3, x0, 10);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd1);  // 0 < 10 (signed)
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);  // 0 >= -10 (signed)
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd1);  // 0 < 10 (unsigned)
endtask

//
// Test: R-type from x0
//
// Tests all R-type instructions with x0 as both operands. Verifies each
// instruction executes without errors and produces expected zero results.
//
task automatic test_r_type_from_x0;
  ADD(x1, x0, x0);
  SUB(x2, x0, x0);
  AND(x3, x0, x0);
  OR(x4, x0, x0);
  XOR(x5, x0, x0);
  SLL(x6, x0, x0);
  SRL(x7, x0, x0);
  SRA(x8, x0, x0);
  SLT(x9, x0, x0);
  SLTU(x10, x0, x0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[7], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[8], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[9], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[10], 32'd0);
endtask

//
// Test: x0 register is hardwired to zero
//
// Tests a fundamental RISC-V architectural requirement: register x0 must
// always read as zero and writes to x0 must be ignored. This test attempts
// to write 100 to x0 and verifies it remains zero.
//
task automatic test_x0_immutable;
  ADDI(x0, x0, 100);
  ADDI(x1, x0, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd0);
endtask

//
//--------------------------------------------------------------------
// I-type tests with register dependencies
//--------------------------------------------------------------------
//

//
// Test: ADDI with dependencies
//
// Tests ADDI with a register dependency (x7 uses x6). Verifies immediate
// values work correctly and results can be used by subsequent instructions.
//
task automatic test_addi;
  ADDI(x1, x0, 100);
  ADDI(x2, x0, -50);
  ADDI(x3, x0, 0);
  ADDI(x4, x0, 2047);
  ADDI(x5, x0, -2048);
  ADDI(x6, x0, 10);
  ADDI(x7, x6, 5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hFFFFFFCE);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd2047);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'hFFFFF800);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[7], 32'd15);
endtask

//
// Test: I-type logical with dependencies
//
// Tests XORI, ORI, and ANDI using register dependencies. All logical
// operations read from x1 which was set by the first instruction.
//
task automatic test_i_type_logical;
  ADDI(x1, x0, 255);
  XORI(x2, x1, 15);
  ORI(x3, x1, 240);
  ANDI(x4, x1, 15);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd255);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd240);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd255);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd15);
endtask

//
// Test: I-type compare with dependencies
//
// Tests SLTI and SLTIU with register dependencies. Verifies signed and
// unsigned comparisons work correctly with computed values.
//
task automatic test_i_type_compare;
  ADDI(x1, x0, 10);
  SLTI(x2, x1, 20);
  SLTI(x3, x1, 5);
  ADDI(x4, x0, -10);
  SLTIU(x5, x4, 5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd0);
endtask

//
// Test: I-type shifts with dependencies
//
// Tests SLLI, SRLI, and SRAI with register dependencies. Includes testing
// sign extension for arithmetic right shift with negative values.
//
task automatic test_i_type_shift;
  ADDI(x1, x0, 1);
  SLLI(x2, x1, 1);
  SLLI(x3, x1, 5);
  SLLI(x4, x1, 31);
  ADDI(x5, x0, 128);
  SRLI(x6, x5, 2);
  ADDI(x7, x0, -128);
  SRAI(x8, x7, 2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd2);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd32);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'h80000000);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd128);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd32);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[7], 32'hFFFFFF80);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[8], 32'hFFFFFFE0);
endtask

//
//--------------------------------------------------------------------
// R-type tests with register dependencies
//--------------------------------------------------------------------
//

//
// Test: R-type arithmetic
//
// Tests ADD and SUB instructions with register dependencies. Verifies
// two-operand arithmetic works correctly including with negative values.
//
task automatic test_r_type_arithmetic;
  ADDI(x1, x0, 100);
  ADDI(x2, x0, 50);
  ADD(x3, x1, x2);
  SUB(x4, x1, x2);
  ADDI(x5, x0, -10);
  ADD(x6, x5, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd50);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd150);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd50);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd40);
endtask

//
// Test: R-type logical
//
// Tests AND, OR, and XOR instructions with register dependencies. Verifies
// bitwise logical operations work correctly with two register operands.
//
task automatic test_r_type_logical;
  ADDI(x1, x0, 255);
  ADDI(x2, x0, 240);
  AND(x3, x1, x2);
  OR(x4, x1, x2);
  XOR(x5, x1, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd255);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd240);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd240);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd255);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd15);
endtask

//
// Test: R-type shifts
//
// Tests SLL, SRL, and SRA with register dependencies. The shift amount
// comes from a register (x2) rather than an immediate value.
//
task automatic test_r_type_shift;
  ADDI(x1, x0, 8);
  ADDI(x2, x0, 2);
  SLL(x3, x1, x2);
  SRL(x4, x1, x2);
  ADDI(x5, x0, -8);
  SRA(x6, x5, x2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd8);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd2);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd32);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd2);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'hFFFFFFF8);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'hFFFFFFFE);
endtask

//
// Test: R-type compare
//
// Tests SLT and SLTU with register dependencies. Compares values from
// registers to verify signed and unsigned comparison logic.
//
task automatic test_r_type_compare;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, 20);
  SLT(x3, x1, x2);
  SLT(x4, x2, x1);
  ADDI(x5, x0, -10);
  SLTU(x6, x5, x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd20);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd0);
endtask

//
//--------------------------------------------------------------------
// Read-after-write dependency tests
//--------------------------------------------------------------------
//

//
// Test: Simple read-after-write dependency
//
// Tests a basic RAW dependency where one instruction immediately uses the
// result of the previous instruction (x2 reads x1 right after x1 is written).
//
task automatic test_raw_dependency;
  ADDI(x1, x0, 10);
  ADDI(x2, x1, 5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd15);
endtask

//
// Test: Long chains of register dependencies
//
// Tests multiple dependency chains of varying lengths. The first chain
// (x1->x2->x3->x4->x5->x6->x7->x8) creates a deep dependency requiring
// each instruction to complete before the next can use its result. In a
// pipelined implementation, this stresses data forwarding or pipeline
// stalls across multiple stages.
//
task automatic test_chained_dependencies;
  ADDI(x1, x0, 100);
  ADD(x2, x1, x1);
  SUB(x3, x2, x1);
  XOR(x4, x3, x2);
  OR(x5, x4, x3);
  AND(x6, x5, x4);
  SLL(x7, x6, x1);
  SRL(x8, x7, x1);

  ADDI(x10, x0, 5);
  ADD(x11, x10, x10);

  ADDI(x20, x0, 1);
  ADDI(x21, x20, 1);
  ADDI(x22, x21, 1);
  ADDI(x23, x22, 1);
  ADDI(x24, x23, 1);

  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd200);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[10], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[11], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[20], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[21], 32'd2);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[22], 32'd3);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[23], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[24], 32'd5);
endtask

//
//--------------------------------------------------------------------
// Jump tests (JAL/JALR)
//--------------------------------------------------------------------
//

// NOTE: The NOP after JALR is a workaround for pipelined implementations
// without proper flush logic. This delay shouldn't be necessary in a correct
// implementation, but we allow it for basic functionality testing. Pipeline
// hazards are tested separately, and after the basic tests.

//
// Test: Simple JAL
//
// Tests basic JAL functionality: jumps forward over one instruction and
// saves the return address (PC+4) in the link register.
//
// See NOP note above.
task automatic test_jal_simple;
  JAL(x1, 12);
  NOP();
  ADDI(x2, x0, 99);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
endtask

//
// Test: Simple JALR
//
// Tests basic JALR functionality: computes target as base register (x0) plus
// offset, jumps to that address, and saves return address in link register.
//
// See NOP note above.
task automatic test_jalr_simple;
  JALR(x1, x0, 12);
  NOP();
  ADDI(x2, x0, 99);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
endtask

//
// Test: JALR LSB clearing
//
// Tests that JALR clears the least significant bit of the computed target
// address. Uses offset 9 (odd), which should become 8 after LSB clearing.
//
// See NOP note above.
task automatic test_jalr_lsb_clear;
  JALR(x1, x0, 9);
  NOP();
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
endtask

//
// Test: JALR with base register
//
// Tests JALR with a non-zero base register. Target is computed as x5 + (-8)
// = 16 - 8 = 8, jumping to the ADDI instruction which executes.
//
task automatic test_jalr_with_base_register;
  ADDI(x5, x0, 16);
  JALR(x1, x5, -8);
  ADDI(x2, x0, 99);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd8);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd99);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd16);
endtask

//
// Test: Function call and return pattern
//
// Tests the common RISC-V calling convention pattern: JAL to save return
// address in ra (x1), execute the "function", then JALR to return using the
// saved address. This validates both jump instructions work correctly
// together for implementing function calls.
//
// See NOP note above.
task automatic test_call_return_pattern;
  JAL(ra, 12);
  NOP();
  EBREAK();
  ADDI(x2, x0, 42);
  JALR(x0, ra, 0);
  NOP();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd42);
endtask

task automatic test_jal_short;
  JAL(x1, 4);
  ADDI(x2, x0, 9);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd9);
endtask

//
// Test: JAL to misaligned address
//
// Tests that JAL to a misaligned target address (not on a 2-byte boundary)
// triggers a trap. This should trap before updating any registers.
//
task automatic test_jal_misaligned;
  JAL(x1, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
endtask

//
// Test: JALR to misaligned address
//
// Tests that JALR to a misaligned target address triggers a trap.
// Sets x2 to 2 (misaligned after LSB clear), then attempts JALR using x2 as base.
// JALR clears LSB: (2 + 0) & ~1 = 2, which has bit[1] set (misaligned).
//
task automatic test_jalr_misaligned;
  ADDI(x2, x0, 2);
  JALR(x1, x2, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
endtask

//
// Test: JAL backward to misaligned address
//
// Tests that JAL jumping backward to a misaligned address triggers a trap.
// Uses a negative offset to jump backward to an odd address.
//
task automatic test_jal_misaligned_backward;
  NOP();
  NOP();
  JAL(x1, -2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
endtask

//
// Test: JAL forward jump with multiple skipped instructions
//
// Tests pipeline behavior by jumping over several instructions. The ADDIs
// with value 99 should be skipped and not execute (registers stay 0). In a
// pipelined implementation, these instructions may enter the pipeline but
// must be flushed when the jump is taken.
//
task automatic test_jal_forward_pipeline;
  JAL(x1, 20);
  ADDI(x2, x0, 99);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 99);
  ADDI(x5, x0, 99);
  ADDI(x6, x0, 5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd5);
endtask

//
// Test: JAL short forward jump skipping one instruction
//
// Tests pipeline behavior when jumping forward past a single instruction.
// The ADDI(x4) should be skipped (x4 stays 0). This test validates that the
// processor correctly handles the pipeline flush for a smaller jump offset.
//
task automatic test_jal_short_forward_pipeline;
  ADDI(x2, x0, 1);
  ADDI(x3, x0, 2);
  JAL(x1, 8);
  ADDI(x4, x0, 99);
  ADDI(x5, x0, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd12);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd2);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd3);
endtask

//
// Test: JALR forward jump with multiple skipped instructions
//
// Tests pipeline behavior for JALR by jumping over several instructions.
// The ADDIs with value 99 should be skipped and not execute (registers stay
// 0). This validates pipeline flushing for register-based jumps.
//
task automatic test_jalr_forward_pipeline;
  JALR(x1, x0, 20);
  ADDI(x2, x0, 99);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 99);
  ADDI(x5, x0, 99);
  ADDI(x6, x0, 5);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd5);
endtask

//
// Test: RAS prediction with pipeline flush
//
// Tests that when RAS predicts a return address for JALR, the speculatively
// fetched instruction from the sequential PC is properly flushed.
//
// Bug scenario: JALR x0, x1, 0 returns to saved address, but the instruction
// immediately following the JALR (which should be flushed) incorrectly executes
// when RAS prediction is active.
//
// Setup: Set x10=42, JAL to function, function returns. The instruction after
// JALR should NOT execute (x10 should stay 42, not become 0).
//
task automatic test_ras_jalr_return_flush;
  ADDI(x10, x0, 42);
  JAL(x1, 12);
  EBREAK();

  NOP();
  NOP();

  ADDI(x2, x0, 5);
  JALR(x0, x1, 0);
  ADDI(x10, x0, 0);

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd8);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[10], 32'd42);
endtask

//
// Test: JALR misprediction EX stage flush
//
// Tests that when JALR misprediction is detected in MEM stage, the
// wrong-path instruction in EX stage is properly flushed and does not
// write to the register file.
//
// With JALR misprediction detection moved to MEM stage for timing optimization,
// there is a one-cycle delay between when the wrong-path instruction enters EX
// and when the misprediction is detected. This test verifies that EX/MEM flush
// signal properly cancels the wrong-path instruction.
//
// Memory layout:
//   PC 0:  ADDI x10=42 (test value, should not be overwritten)
//   PC 4:  ADDI x15=2 (loop counter)
//   PC 8:  ADDI x2=44 (JALR target address)
//   PC 12: JAL to PC 20, pushes return address (PC 16) onto RAS
//   PC 16: ADDI x10=99 (WRONG PATH - RAS predicts JALR returns here)
//   PC 20: ADDI x3=1 (JAL lands here, work before JALR)
//   PC 24: ADDI x4=2
//   PC 28: ADDI x5=3
//   PC 32: ADDI x6=4
//   PC 36: ADDI x7=5 (several instructions to delay JALR)
//   PC 40: JALR to PC 44 (RAS predicts PC 16, actual is PC 44 - MISPREDICTION)
//   PC 44: ADDI x11=1 (correct path continues here)
//   PC 48: ADDI x12=2
//   PC 52: ADDI x13=3
//   PC 56: ADDI x14=4
//   PC 60: ADDI x15-- (decrement loop counter)
//   PC 64: BNE loop if x15!=0
//   PC 68: EBREAK
//
// First iteration (BTB/RAS training):
//   - JAL at PC 12 pushes PC 16 onto RAS
//   - BTB learns: JALR at PC 40 is a return instruction
//   - No misprediction yet (BTB/RAS not trained on first pass)
//
// Second iteration (triggers bug):
//   - JAL at PC 12 pushes PC 16 onto RAS (again)
//   - JALR at PC 40 reaches ID stage, BTB predicts as return
//   - RAS pops and predicts return to PC 16
//   - Pipeline speculatively fetches wrong-path ADDI at PC 16
//   - JALR advances to EX, computes actual target = PC 44
//   - Wrong-path ADDI advances from ID to EX
//   - JALR advances to MEM, misprediction detected (pred=16, actual=44)
//   - Pipeline redirects to PC 44, flushes IF/ID stages
//   - BUG: Wrong-path ADDI in EX stage not flushed (missing ex_mem_flush)
//   - Wrong-path ADDI completes and writes x10=99
//
// Expected (with bug): x10=99 (wrong-path instruction executed)
// Expected (fixed): x10=42 (wrong-path instruction flushed)
//
task automatic test_jalr_mispred_ex_flush;
  ADDI(x10, x0, 42);
  ADDI(x15, x0, 2);
  ADDI(x2, x0, 44);
  JAL(x1, 8);
  ADDI(x10, x0, 99);
  ADDI(x3, x0, 1);
  ADDI(x4, x0, 2);
  ADDI(x5, x0, 3);
  ADDI(x6, x0, 4);
  ADDI(x7, x0, 5);
  JALR(x0, x2, 0);
  ADDI(x11, x0, 1);
  ADDI(x12, x0, 2);
  ADDI(x13, x0, 3);
  ADDI(x14, x0, 4);
  ADDI(x15, x15, -1);
  BNE(x15, x0, -56);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[10], 32'd42);
endtask

//
// Test: JAL with immediate forwarding
//
// Tests JAL result (PC+4) being forwarded to the next instruction.
// This creates a RAW hazard where the following instruction immediately
// uses the JALR link register before it reaches WB stage.
//
task automatic test_jal_forwarding;
  JAL(x1, 4);
  ADDI(x2, x1, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd4);
endtask

//
// Test: JAL with BTB counter trained to "not taken"
//
// Reproduces bug where BTB predicts "not taken" for JAL (unconditional jump).
//
// Key insight: BTB counter update doesn't reset when tag changes. It reads
// the existing counter and increments/decrements. So:
// 1. Branch at PC X (index N) trains counter to 00 (strongly not taken)
// 2. JAL at PC Y (same index N, different tag) executes, counter = 00+1 = 01
// 3. JAL executes again, BTB hit with counter=01 → predicts NOT TAKEN → BUG!
//
// BTB index = PC[5:2]. PC 0x08 and 0x48 both have index 2.
//
task automatic test_jal_btb_not_taken;
  //
  // Phase 1: Train BTB[index=2] counter to 00
  // Use a branch that is ALWAYS not taken (compare x0 to non-zero)
  //
  ADDI(x10, x0, 3);  // 0x00: x10 = 3 (loop counter)
  ADDI(x11, x0, 99);  // 0x04: x11 = 99 (never equals x0)
  // train_loop:
  BEQ(x0, x11, 48);  // 0x08: if 0==99 goto 0x38 (NEVER taken)
  ADDI(x10, x10, -1);  // 0x0C: x10--
  BNE(x10, x0, -8);  // 0x10: if x10!=0 goto 0x08 (loop)
  // Loop trace (3 iterations):
  //   iter 1: BEQ NOT TAKEN (counter=01), x10→2, BNE TAKEN
  //   iter 2: BEQ NOT TAKEN (counter=00), x10→1, BNE TAKEN
  //   iter 3: BEQ NOT TAKEN (counter=00 saturated), x10→0, BNE NOT TAKEN
  // Result: BTB[2] counter = 00

  //
  // Phase 2: Pad to PC=0x48 (same BTB index=2, different tag)
  //
  NOP();  // 0x14
  NOP();  // 0x18
  NOP();  // 0x1C
  NOP();  // 0x20
  NOP();  // 0x24
  NOP();  // 0x28
  NOP();  // 0x2C
  NOP();  // 0x30
  NOP();  // 0x34
  NOP();  // 0x38
  NOP();  // 0x3C
  NOP();  // 0x40
  NOP();  // 0x44

  //
  // Phase 3: JAL at PC=0x48, executed twice to trigger bug
  //
  // first_jal:
  JAL(x1, 24);  // 0x48: JAL to 0x60. 1st exec: counter 00→01
  ADDI(x13, x0, 99);  // 0x4C: SHOULD BE SKIPPED
  NOP();  // 0x50
  NOP();  // 0x54
  NOP();  // 0x58
  NOP();  // 0x5C
  // jal_target:
  ADDI(x14, x0, 42);  // 0x60: x14 = 42
  BNE(x20, x0, 12);  // 0x64: if x20!=0 goto done (0x70)
  ADDI(x20, x0, 1);  // 0x68: x20 = 1 (flag)
  BEQ(x0, x0, -36);  // 0x6C: goto first_jal (0x48)
  // 2nd JAL exec: BTB hit, counter=01, predicted NOT TAKEN → BUG!
  // done:
  EBREAK();  // 0x70

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);

  // x13 = 0 (skipped by JAL)
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[13], 32'd0);

  // x14 = 42 (target reached)
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[14], 32'd42);
endtask

//
// Test: JALR with immediate forwarding
//
// Tests JALR result (PC+4) being forwarded to the next instruction.
// This creates a RAW hazard where the following instruction immediately
// uses the JALR link register before it reaches WB stage.
//
task automatic test_jalr_forwarding;
  JALR(x1, x0, 4);
  ADDI(x2, x1, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd4);
endtask

//
// Test: JALR with base register forwarding
//
// Tests forwarding a base register value to JALR.
// This creates a RAW hazard where JALR immediately uses a register
// that was just computed, requiring forwarding of the base address.
//
task automatic test_jalr_base_forwarding;
  ADDI(x5, x0, 8);
  JALR(x1, x5, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd8);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd8);
endtask

//
//--------------------------------------------------------------------
// Branch tests (BEQ, BNE, BLT, BGE, BLTU, BGEU)
//--------------------------------------------------------------------
//

//
// Test: BEQ taken forward
//
// Tests BEQ when condition is true (registers are equal). Branch should be
// taken and skip the intermediate instruction.
//
task automatic test_beq_taken_forward;
  ADDI(x1, x0, 42);
  ADDI(x2, x0, 42);
  BEQ(x1, x2, 8);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd42);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd100);
endtask

//
// Test: BEQ not taken
//
// Tests BEQ when condition is false (registers are not equal). Branch should
// not be taken and fall through to the next instruction.
//
task automatic test_beq_not_taken;
  ADDI(x1, x0, 42);
  ADDI(x2, x0, 43);
  BEQ(x1, x2, 8);
  ADDI(x3, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd43);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
endtask

//
// Test: BNE taken backward (loop)
//
// Tests BNE in a loop pattern. Increments x1 until it equals x2, using a
// backward branch to repeat the loop body.
//
task automatic test_bne_taken_backward;
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 5);
  ADDI(x1, x1, 1);
  BNE(x1, x2, -4);
  ADDI(x3, x0, 99);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 128);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd99);
endtask

//
// Test: BNE not taken
//
// Tests BNE when condition is false (registers are equal). Branch should not
// be taken and fall through to the next instruction.
//
task automatic test_bne_not_taken;
  ADDI(x1, x0, 42);
  ADDI(x2, x0, 42);
  BNE(x1, x2, 8);
  ADDI(x3, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd42);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
endtask

//
// Test: BLT taken (signed comparison)
//
// Tests BLT when condition is true (rs1 < rs2 signed). Uses a negative
// value to verify signed comparison.
//
task automatic test_blt_taken_signed;
  ADDI(x1, x0, -10);
  ADDI(x2, x0, 10);
  BLT(x1, x2, 8);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd100);
endtask

//
// Test: BLT not taken (signed comparison)
//
// Tests BLT when condition is false (rs1 >= rs2 signed).
//
task automatic test_blt_not_taken_signed;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, -10);
  BLT(x1, x2, 8);
  ADDI(x3, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
endtask

//
// Test: BGE taken (signed comparison)
//
// Tests BGE when condition is true (rs1 >= rs2 signed).
//
task automatic test_bge_taken_signed;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, -10);
  BGE(x1, x2, 8);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd100);
endtask

//
// Test: BGE not taken (signed comparison)
//
// Tests BGE when condition is false (rs1 < rs2 signed).
//
task automatic test_bge_not_taken_signed;
  ADDI(x1, x0, -10);
  ADDI(x2, x0, 10);
  BGE(x1, x2, 8);
  ADDI(x3, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
endtask

//
// Test: BGE with equal values
//
// Tests BGE when rs1 == rs2. Should be taken since equal satisfies >=.
//
task automatic test_bge_equal;
  ADDI(x1, x0, 42);
  ADDI(x2, x0, 42);
  BGE(x1, x2, 8);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd100);
endtask

//
// Test: BLTU taken (unsigned comparison)
//
// Tests BLTU when condition is true (rs1 < rs2 unsigned). Uses negative
// value (large unsigned) to verify unsigned comparison.
//
task automatic test_bltu_taken_unsigned;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, -10);
  BLTU(x1, x2, 8);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd100);
endtask

//
// Test: BLTU not taken (unsigned comparison)
//
// Tests BLTU when condition is false (rs1 >= rs2 unsigned).
//
task automatic test_bltu_not_taken_unsigned;
  ADDI(x1, x0, -10);
  ADDI(x2, x0, 10);
  BLTU(x1, x2, 8);
  ADDI(x3, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
endtask

//
// Test: BGEU taken (unsigned comparison)
//
// Tests BGEU when condition is true (rs1 >= rs2 unsigned).
//
task automatic test_bgeu_taken_unsigned;
  ADDI(x1, x0, -10);
  ADDI(x2, x0, 10);
  BGEU(x1, x2, 8);
  ADDI(x3, x0, 99);
  ADDI(x4, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd100);
endtask

//
// Test: BGEU not taken (unsigned comparison)
//
// Tests BGEU when condition is false (rs1 < rs2 unsigned).
//
task automatic test_bgeu_not_taken_unsigned;
  ADDI(x1, x0, 10);
  ADDI(x2, x0, -10);
  BGEU(x1, x2, 8);
  ADDI(x3, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
endtask

//
// Test: BGEU with zero
//
// Tests BGEU when both operands are zero. Should be taken since 0 >= 0.
//
task automatic test_bgeu_zero;
  ADDI(x1, x0, 0);
  BGEU(x1, x0, 8);
  ADDI(x2, x0, 99);
  ADDI(x3, x0, 100);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd100);
endtask

//
// Test: Branch loop pattern
//
// Tests a realistic loop using BLT to count from 0 to 5.
//
task automatic test_branch_loop;
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 5);
  ADDI(x1, x1, 1);
  BLT(x1, x2, -4);
  ADDI(x3, x0, 99);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 128);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd99);
endtask

//
// Test: BEQ to misaligned address
//
// Tests that BEQ branch to a misaligned target address triggers a trap.
// Sets up equal registers so branch is taken to a misaligned target.
// BEQ at PC=8, offset=6 -> target = 8 + 6 = 14 (bit[1]=1, misaligned).
//
task automatic test_beq_misaligned;
  ADDI(x1, x0, 42);
  ADDI(x2, x0, 42);
  BEQ(x1, x2, 6);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
endtask

//
// Test: BNE to misaligned address
//
// Tests that BNE branch to a misaligned target address triggers a trap.
// Sets up unequal registers so branch is taken to a misaligned target.
// BNE at PC=8, offset=6 -> target = 8 + 6 = 14 (bit[1]=1, misaligned).
//
task automatic test_bne_misaligned;
  ADDI(x1, x0, 42);
  ADDI(x2, x0, 43);
  BNE(x1, x2, 6);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
endtask

//
// Test: BLT backward to misaligned address
//
// Tests that BLT branch backward to a misaligned target triggers a trap.
// Creates a taken backward branch with misaligned target.
// BLT at PC=16, offset=-6 -> target = 16 - 6 = 10 (bit[1]=1, misaligned).
//
task automatic test_blt_misaligned_backward;
  NOP();
  NOP();
  ADDI(x1, x0, 5);
  ADDI(x2, x0, 10);
  BLT(x1, x2, -6);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
endtask

//
//--------------------------------------------------------------------
// LUI and AUIPC tests
//--------------------------------------------------------------------
//

//
// Test: LUI basic functionality
//
// Tests LUI (Load Upper Immediate) which loads a 20-bit immediate value
// into the upper 20 bits of a register, setting the lower 12 bits to zero.
//
task automatic test_lui_basic;
  LUI(x1, 32'h12345000);
  LUI(x2, 32'hABCDE000);
  LUI(x3, 32'h00001000);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h12345000);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hABCDE000);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h00001000);
endtask

//
// Test: LUI with zero immediate
//
// Tests LUI with a zero immediate value, which should produce zero.
//
task automatic test_lui_zero;
  LUI(x1, 32'h00000000);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h00000000);
endtask

//
// Test: LUI with negative value (sign bit set)
//
// Tests LUI with a value that has the sign bit set in the upper bits.
// The immediate still zero-extends into the register.
//
task automatic test_lui_negative;
  LUI(x1, 32'hFFFFF000);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'hFFFFF000);
endtask

//
// Test: AUIPC basic functionality
//
// Tests AUIPC (Add Upper Immediate to PC) which adds a 20-bit immediate
// (shifted left 12 bits) to the current PC and stores the result.
//
task automatic test_auipc_basic;
  AUIPC(x1, 32'h00001000);
  AUIPC(x2, 32'h00002000);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h00001000);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'h00002004);
endtask

//
// Test: AUIPC with zero immediate
//
// Tests AUIPC with zero immediate, which should produce the current PC.
//
task automatic test_auipc_zero;
  AUIPC(x1, 32'h00000000);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h00000000);
endtask

//
// Test: AUIPC with negative offset
//
// Tests AUIPC with a negative offset (sign bit set). The result is PC plus
// the sign-extended immediate value.
//
task automatic test_auipc_negative;
  NOP();
  NOP();
  NOP();
  AUIPC(x1, 32'hFFFFF000);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'hFFFFF00C);
endtask

//
// Test: AUIPC with immediate forwarding
//
// Tests AUIPC result being forwarded to the next instruction.
// This creates a RAW hazard where the following instruction immediately
// uses the AUIPC result before it reaches WB stage.
//
task automatic test_auipc_forwarding;
  AUIPC(x2, 32'h00001000);
  ADDI(x3, x2, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'h00001000);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h00001000);
endtask

//
// Test: LI pseudo-instruction with small values
//
// Tests the LI (Load Immediate) pseudo-instruction with values that fit in
// 12 bits. These expand to a single ADDI instruction.
//
task automatic test_li_pseudo_small;
  LI(x1, 32'd100);
  LI(x2, 32'd0);
  LI(x3, -32'd50);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'hFFFFFFCE);
endtask

//
// Test: LI pseudo-instruction with large values
//
// Tests the LI pseudo-instruction with full 32-bit values. These expand to
// LUI+ADDI sequence, which creates a read-after-write dependency that tests
// data forwarding.
//
task automatic test_li_pseudo_large;
  LI(x1, 32'h12345678);
  LI(x2, 32'hDEADBEEF);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h12345678);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hDEADBEEF);
endtask

//
// Test: LUI+ADDI combination
//
// Tests the common pattern of loading a full 32-bit constant using LUI
// followed by ADDI. Tests data forwarding since ADDI depends on LUI result.
//
task automatic test_lui_addi_combination;
  LUI(x1, 32'h12345000);
  ADDI(x1, x1, 32'h678);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h12345678);
endtask

//
//--------------------------------------------------------------------
// Load/Store tests
//--------------------------------------------------------------------
//

//
// Test: Basic load word and store word
//
// Tests basic LW and SW instructions with multiple memory locations.
//
task automatic test_lw_sw_basic;
  uut.dmem.mem[0] = 32'hDEADBEEF;
  uut.dmem.mem[1] = 32'h12345678;
  uut.dmem.mem[2] = 32'hCAFEBABE;

  ADDI(x1, x0, 0);
  LW(x2, x1, 0);
  LW(x3, x1, 4);
  LW(x4, x1, 8);
  LI(x5, 32'hABCD1234);
  SW(x5, x1, 12);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hDEADBEEF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h12345678);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'hCAFEBABE);
  `TICK(clk);
  `CHECK_EQ(uut.dmem.mem[3], 32'hABCD1234);
endtask

//
// Test: Load byte (signed)
//
// Tests LB instruction which loads a byte and sign-extends to 32 bits.
// Tests all four byte positions within a word.
//
task automatic test_lb_basic;
  uut.dmem.mem[0] = 32'h89ABCDEF;

  ADDI(x1, x0, 0);
  LB(x2, x1, 0);
  LB(x3, x1, 1);
  LB(x4, x1, 2);
  LB(x5, x1, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hFFFFFFEF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'hFFFFFFCD);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'hFFFFFFAB);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'hFFFFFF89);
endtask

//
// Test: Load byte unsigned
//
// Tests LBU instruction which loads a byte and zero-extends to 32 bits.
//
task automatic test_lbu_basic;
  uut.dmem.mem[0] = 32'h89ABCDEF;

  ADDI(x1, x0, 0);
  LBU(x2, x1, 0);
  LBU(x3, x1, 1);
  LBU(x4, x1, 2);
  LBU(x5, x1, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'h000000EF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h000000CD);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'h000000AB);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'h00000089);
endtask

//
// Test: Load halfword (signed)
//
// Tests LH instruction which loads a halfword and sign-extends to 32 bits.
//
task automatic test_lh_basic;
  uut.dmem.mem[0] = 32'h8765CDEF;

  ADDI(x1, x0, 0);
  LH(x2, x1, 0);
  LH(x3, x1, 2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hFFFFCDEF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'hFFFF8765);
endtask

//
// Test: Load halfword unsigned
//
// Tests LHU instruction which loads a halfword and zero-extends to 32 bits.
//
task automatic test_lhu_basic;
  uut.dmem.mem[0] = 32'h8765CDEF;

  ADDI(x1, x0, 0);
  LHU(x2, x1, 0);
  LHU(x3, x1, 2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'h0000CDEF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h00008765);
endtask

//
// Test: Store byte
//
// Tests SB instruction which stores the low byte to all byte positions.
//
task automatic test_sb_basic;
  uut.dmem.mem[0] = 32'h00000000;

  ADDI(x1, x0, 0);
  LI(x2, 32'h12345678);
  SB(x2, x1, 0);
  SB(x2, x1, 1);
  SB(x2, x1, 2);
  SB(x2, x1, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `TICK(clk);
  `CHECK_EQ(uut.dmem.mem[0], 32'h78787878);
endtask

//
// Test: Store halfword
//
// Tests SH instruction which stores the low halfword to both positions.
//
task automatic test_sh_basic;
  uut.dmem.mem[0] = 32'h00000000;

  ADDI(x1, x0, 0);
  LI(x2, 32'h12345678);
  SH(x2, x1, 0);
  SH(x2, x1, 2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `TICK(clk);
  `CHECK_EQ(uut.dmem.mem[0], 32'h56785678);
endtask

//
// Test: Store byte preserves other bytes
//
// Tests that SB only modifies the target byte without affecting others.
//
task automatic test_sb_partial_word;
  uut.dmem.mem[0] = 32'hDEADBEEF;

  ADDI(x1, x0, 0);
  LI(x2, 32'hFF);
  SB(x2, x1, 1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `TICK(clk);
  `CHECK_EQ(uut.dmem.mem[0], 32'hDEADFFEF);
endtask

//
// Test: Store halfword preserves other halfword
//
// Tests that SH only modifies the target halfword without affecting others.
//
task automatic test_sh_partial_word;
  uut.dmem.mem[0] = 32'hDEADBEEF;

  ADDI(x1, x0, 0);
  LI(x2, 32'h1234);
  SH(x2, x1, 2);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `TICK(clk);
  `CHECK_EQ(uut.dmem.mem[0], 32'h1234BEEF);
endtask

//
// Test: Store-load forwarding
//
// Tests store followed immediately by load from the same address.
// Verifies store-to-load forwarding or proper handling of the dependency.
//
task automatic test_sw_lw_forwarding;

  ADDI(x1, x0, 0);
  LI(x2, 32'h11223344);
  SW(x2, x1, 0);
  LW(x3, x1, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `TICK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h11223344);
  `CHECK_EQ(uut.dmem.mem[0], 32'h11223344);
endtask

//
// Test: Store-load with different address registers
//
// Tests memory hazard when storing through one register and loading
// through a different register to the same address. This verifies that
// memory operations complete in order even when register hazard detection
// doesn't catch the dependency.
//
task automatic test_sw_lw_different_regs;

  ADDI(x1, x0, 0);
  ADDI(x2, x0, 0);
  LI(x3, 32'hAABBCCDD);
  SW(x3, x1, 0);
  LW(x4, x2, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `TICK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'hAABBCCDD);
  `CHECK_EQ(uut.dmem.mem[0], 32'hAABBCCDD);
endtask

//
// Test: Load-use hazard
//
// Tests the load-use hazard where an instruction immediately uses the
// result of a load. This creates a pipeline stall since the load data
// isn't available until the MEM stage.
//
task automatic test_load_use_hazard;
  uut.dmem.mem[0] = 32'd42;
  uut.dmem.mem[1] = 32'd100;

  ADDI(x1, x0, 0);
  LW(x2, x1, 0);
  ADDI(x3, x2, 1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd0);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd42);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd43);
endtask

//
// Test: Multiple load/store operations
//
// Tests a sequence of loads, arithmetic, and stores to verify proper
// interaction between memory and ALU operations.
//
task automatic test_lw_sw_multiple;
  uut.dmem.mem[0] = 32'd10;
  uut.dmem.mem[1] = 32'd20;
  uut.dmem.mem[2] = 32'd30;

  ADDI(x1, x0, 0);
  LW(x2, x1, 0);
  LW(x3, x1, 4);
  ADD(x4, x2, x3);
  SW(x4, x1, 12);
  LW(x5, x1, 8);
  ADD(x6, x5, x5);
  SW(x6, x1, 16);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd10);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd20);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd30);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd30);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'd60);
  `CHECK_EQ(uut.dmem.mem[3], 32'd30);
  `TICK(clk);
  `CHECK_EQ(uut.dmem.mem[4], 32'd60);
endtask

//
// Test: Mixed byte/halfword/word operations
//
// Tests mixing SB, SH, SW, LB, LH, and LW on the same memory location.
//
task automatic test_mixed_byte_halfword_word;
  uut.dmem.mem[0] = 32'h00000000;

  ADDI(x1, x0, 0);
  LI(x2, 32'h12);
  SB(x2, x1, 0);
  LI(x3, 32'h34);
  SB(x3, x1, 1);
  LI(x4, 32'h5678);
  SH(x4, x1, 2);
  LW(x5, x1, 0);
  LH(x6, x1, 0);
  LBU(x7, x1, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'h56783412);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'h00003412);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[7], 32'h00000056);
endtask

//
// Test: Word-aligned memory addresses
//
// Verifies that memory addresses are word-aligned and byte strobes are
// correct for stores with unaligned offsets.
//
// Tests halfword store to address -6 (0xFFFFFFFA):
// - Expected memory address: 0xFFFFFFF8 (word-aligned)
// - Expected byte strobe: 4'b1100 (upper halfword)
//
task automatic test_word_aligned_mem_addr;
  uut.dmem.mem[0] = 32'h00000000;

  ADDI(x2, x0, -768);
  SH(x2, x0, -6);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.dmem_we, 128);
  `CHECK_EQ(uut.cpu.dmem_waddr, 32'hFFFFFFF8);
  `CHECK_EQ(uut.cpu.dmem_wstrb, 4'b1100);

  `CHECK_WAIT_FOR_EBREAK(clk);
endtask

//
//--------------------------------------------------------------------
// Trap tests
//--------------------------------------------------------------------
//

//
// Test: Misaligned halfword store trap
//
// Verifies that a halfword store to an odd address triggers a trap
// and does not write to memory.
// sh x0, 2047(x0) attempts to store to address 2047 (odd), which is
// misaligned for a 2-byte halfword access and must trap.
//
task automatic test_trap_misaligned_sh;
  uut.dmem.mem[511] = 32'hDEADBEEF;

  SH(x0, x0, 2047);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
  `CHECK_EQ(uut.dmem.mem[511], 32'hDEADBEEF);
endtask

//
// Test: Misaligned halfword load trap
//
// Verifies that a halfword load from an odd address triggers a trap
// and does not write to the destination register.
// lh x1, 2047(x0) attempts to load from address 2047 (odd), which is
// misaligned for a 2-byte halfword access and must trap.
//
task automatic test_trap_misaligned_lh;
  LH(x1, x0, 2047);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, uut.cpu.trap, 128);
  `CHECK_TRUE(uut.cpu.trap);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'd0);
endtask

//
//--------------------------------------------------------------------
// CSR tests (Zicntr - Performance Counters)
//--------------------------------------------------------------------
//

//
// Test: RDCYCLE reads cycle counter
//
task automatic test_rdcycle;
  NOP();
  NOP();
  NOP();
  RDCYCLE(x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_TRUE(uut.cpu.stage_id.regfile.regs[1] > 32'h0);
endtask

//
// Test: RDCYCLEH reads cycle counter high word
//
task automatic test_rdcycleh;
  RDCYCLEH(x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h0);
endtask

//
// Test: RDINSTRET reads instruction counter
//
task automatic test_rdinstret;
  NOP();
  NOP();
  NOP();
  RDINSTRET(x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_TRUE(uut.cpu.stage_id.regfile.regs[1] > 32'h0);
endtask

//
// Test: RDINSTRETH reads instruction counter high word
//
task automatic test_rdinstreth;
  RDINSTRETH(x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[1], 32'h0);
endtask

//
// Test: CYCLE counter increments
//
task automatic test_csr_cycle_increments;
  NOP();
  NOP();
  NOP();
  RDCYCLE(x1);
  NOP();
  NOP();
  NOP();
  RDCYCLE(x2);
  SUB(x3, x2, x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_TRUE(uut.cpu.stage_id.regfile.regs[1] > 32'h0);
  `CHECK_TRUE(
      uut.cpu.stage_id.regfile.regs[2] > uut.cpu.stage_id.regfile.regs[1]);
  `CHECK_TRUE(uut.cpu.stage_id.regfile.regs[3] > 32'h0);
endtask

//
// Test: INSTRET counter increments
//
task automatic test_csr_instret_increments;
  NOP();
  NOP();
  NOP();
  RDINSTRET(x1);
  NOP();
  NOP();
  NOP();
  RDINSTRET(x2);
  SUB(x3, x2, x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_TRUE(uut.cpu.stage_id.regfile.regs[1] > 32'h0);
  `CHECK_TRUE(
      uut.cpu.stage_id.regfile.regs[2] > uut.cpu.stage_id.regfile.regs[1]);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd4);
endtask

//
//--------------------------------------------------------------------
// CPI micro-benchmarks
//--------------------------------------------------------------------
//

//
// Test: CPI baseline - independent ALU operations
//
// Measures CPI for independent ALU operations with no dependencies.
// Expected CPI ~1.0 for a pipeline with full bypass and no stalls.
// This establishes the baseline best-case IPC for the pipeline.
//
task automatic test_cpi_alu_independent;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 256);
  ADDI(x3, x0, 1);
  ADDI(x4, x0, 2);
  ADDI(x5, x0, 3);
  ADDI(x6, x0, 4);
  ADDI(x1, x1, 1);
  ADD(x7, x3, x4);
  ADD(x8, x5, x6);
  XOR(x9, x3, x5);
  OR(x10, x4, x6);
  BNE(x1, x2, -20);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 4096);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("cpi_alu_indep", alu_indep_max_cpi, cycles, instrs);
endtask

//
// Test: CPI with ALU dependency chain
//
// Measures CPI for back-to-back ALU operations with RAW dependencies.
// With full EX->EX forwarding: CPI ~1.0
// Without forwarding: CPI ~2.0 (one bubble per dependency)
// This reveals the effectiveness of the bypass network.
//
task automatic test_cpi_alu_chain;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 256);
  ADDI(x5, x0, 1);
  ADDI(x5, x5, 1);
  ADDI(x5, x5, 1);
  ADDI(x5, x5, 1);
  ADDI(x5, x5, 1);
  ADDI(x5, x5, 1);
  ADDI(x1, x1, 1);
  BNE(x1, x2, -28);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 16384);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("cpi_alu_chain", alu_chain_max_cpi, cycles, instrs);
endtask

//
// Test: CPI for always-taken backward branch
//
// Measures the branch penalty for always-taken backward branches (loops).
// The penalty depends on pipeline flush behavior:
// - No flush or predict-taken: CPI ~1.0
// - Flush on branch: CPI = 1.0 + (flush_cycles / iterations)
// This reveals the control hazard cost for loops.
//
task automatic test_cpi_branch_taken;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 1024);
  ADDI(x1, x1, 1);
  BNE(x1, x2, -4);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 8192);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("cpi_br_taken", br_taken_max_cpi, cycles, instrs);
endtask

//
// Test: CPI for not-taken branches
//
// Measures CPI when branches are never taken (fall through).
// With static not-taken prediction: CPI ~1.0
// Without prediction or predict-taken: higher CPI
// This reveals branch prediction effectiveness.
//
task automatic test_cpi_branch_not_taken;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 1024);
  ADDI(x3, x0, 9999);
  BEQ(x1, x3, 8);
  ADDI(x1, x1, 1);
  BNE(x1, x2, -12);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 16384);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("cpi_br_not_taken", br_not_taken_max_cpi, cycles, instrs);
endtask

//
// Test: CPI for load-use hazard
//
// Measures CPI when loads are immediately followed by dependent instructions.
// With MEM->EX bypass and 1-cycle memory: CPI ~1.0-1.3
// Without bypass: CPI ~1.5-2.0 (one bubble per load-use)
// This reveals memory hazard handling effectiveness.
//
task automatic test_cpi_load_use;
  logic [31:0] cycles;
  logic [31:0] instrs;

  uut.dmem.mem[0] = 32'd42;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 256);
  ADDI(x3, x0, 0);
  LW(x4, x3, 0);
  ADDI(x5, x4, 1);
  ADDI(x1, x1, 1);
  BNE(x1, x2, -12);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 4096);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("cpi_load_use", load_use_max_cpi, cycles, instrs);
endtask

//
// Test: CPI for mixed instruction types
//
// Measures CPI for a realistic mix of ALU, shifts, and logical operations.
// This provides a more representative CPI than isolated benchmarks.
// Expected CPI ~1.0 for a well-balanced pipeline.
//
task automatic test_cpi_mixed_alu;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 256);
  ADDI(x3, x0, 5);
  ADDI(x4, x0, 10);
  ADD(x5, x3, x4);
  XOR(x6, x5, x3);
  SLLI(x7, x6, 2);
  OR(x8, x7, x4);
  SRLI(x9, x8, 1);
  ADDI(x1, x1, 1);
  BNE(x1, x2, -32);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 16384);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("cpi_mixed_alu", mixed_alu_max_cpi, cycles, instrs);
endtask

//
// Test: Function call/return CPI
//
// Measures CPI for function call patterns to demonstrate RAS benefit.
// Calls a simple function 64 times in a loop.
//
task automatic test_cpi_function_calls;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x10, x0, 64);
  ADDI(x11, x0, 0);
  JAL(ra, 16);
  ADDI(x11, x11, 1);
  BNE(x11, x10, -8);
  JAL(x0, 16);
  ADDI(x12, x12, 3);
  SLLI(x12, x12, 1);
  JALR(x0, ra, 0);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 4096);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("cpi_function_calls", function_calls_max_cpi, cycles, instrs);
endtask

//
//--------------------------------------------------------------------
// Memory-mapped I/O tests
//--------------------------------------------------------------------
//

//
// Test: Basic MMIO write
//
// Tests writing to memory-mapped I/O region (address 0x80000000+).
// Writes a value to MMIO and verifies it's stored in the I/O memory.
//
task automatic test_mmio_write_basic;
  LI(x1, 32'h80000000);
  LI(x2, 32'h12345678);
  SW(x2, x1, 0);
  LI(x3, 32'hABCDEF00);
  SW(x3, x1, 4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'h12345678);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'hABCDEF00);
  `TICK(clk);
  `CHECK_EQ(io_mem.mem[0], 32'h12345678);
  `CHECK_EQ(io_mem.mem[1], 32'hABCDEF00);
endtask

//
// Test: Basic MMIO read
//
// Tests reading from memory-mapped I/O region.
// Preloads MMIO memory and verifies the CPU can read the values.
//
task automatic test_mmio_read_basic;
  io_mem.mem[0] = 32'hDEADBEEF;
  io_mem.mem[1] = 32'hCAFEBABE;

  LI(x1, 32'h80000000);
  LW(x2, x1, 0);
  LW(x3, x1, 4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hDEADBEEF);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'hCAFEBABE);
endtask

//
// Test: MMIO read-write sequence
//
// Tests a sequence of writes followed by reads to verify MMIO operates
// correctly for both directions with the same address.
//
task automatic test_mmio_read_write_sequence;
  LI(x1, 32'h80000000);
  LI(x2, 32'h11111111);
  SW(x2, x1, 0);
  LI(x3, 32'h22222222);
  SW(x3, x1, 4);
  LW(x4, x1, 0);
  LW(x5, x1, 4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'h11111111);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'h22222222);
  `TICK(clk);
  `CHECK_EQ(io_mem.mem[0], 32'h11111111);
  `CHECK_EQ(io_mem.mem[1], 32'h22222222);
endtask

//
// Test: MMIO byte operations
//
// Tests byte-level MMIO operations (SB/LB/LBU) to verify byte strobes work
// correctly for memory-mapped I/O.
//
task automatic test_mmio_byte_ops;
  io_mem.mem[0] = 32'h00000000;

  LI(x1, 32'h80000000);
  LI(x2, 32'h12);
  SB(x2, x1, 0);
  LI(x3, 32'h34);
  SB(x3, x1, 1);
  LI(x4, 32'h56);
  SB(x4, x1, 2);
  LI(x5, 32'h78);
  SB(x5, x1, 3);
  LW(x6, x1, 0);
  LBU(x7, x1, 0);
  LBU(x8, x1, 3);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[6], 32'h78563412);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[7], 32'h00000012);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[8], 32'h00000078);
  `TICK(clk);
  `CHECK_EQ(io_mem.mem[0], 32'h78563412);
endtask

//
// Test: MMIO vs normal memory isolation
//
// Verifies that MMIO region (0x80000000+) and normal data memory (0x00000000+)
// are properly isolated and don't interfere with each other.
//
task automatic test_mmio_isolation;
  uut.dmem.mem[0] = 32'hAAAAAAAA;
  io_mem.mem[0]   = 32'hBBBBBBBB;

  LI(x1, 32'h00000000);
  LI(x2, 32'h80000000);
  LW(x3, x1, 0);
  LW(x4, x2, 0);
  LI(x5, 32'hCCCCCCCC);
  SW(x5, x1, 4);
  LI(x6, 32'hDDDDDDDD);
  SW(x6, x2, 4);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'hAAAAAAAA);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'hBBBBBBBB);
  `TICK(clk);
  `CHECK_EQ(uut.dmem.mem[1], 32'hCCCCCCCC);
  `CHECK_EQ(io_mem.mem[1], 32'hDDDDDDDD);
endtask

//
//--------------------------------------------------------------------
// Smoke tests
//--------------------------------------------------------------------
//

//
// Test: Fibonacci(12)
//
// Computes the 12th Fibonacci number (144) using an iterative loop.
// This smoke test validates:
// - Branch instructions in a loop
// - Jump instructions (JAL for looping)
// - Register dependencies
// - Arithmetic operations
// - Shift operations
//
task automatic test_fib12;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x10, x0, 12);
  ADDI(x11, x0, 0);
  ADDI(x12, x0, 1);
  ADDI(x13, x0, 0);
  BEQ(x13, x10, 24);
  ADD(x14, x11, x12);
  ADD(x11, x12, x0);
  ADD(x12, x14, x0);
  ADDI(x13, x13, 1);
  JAL(x0, -20);
  SLLI(x30, x11, 1);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 256);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[11], 32'd144);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[30], 32'd288);

  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("fib12", fib12_max_cpi, cycles, instrs);
endtask

//
// Test: Fibonacci with 100 iterations (performance benchmark)
//
task automatic test_fib100;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x20);
  RDINSTRET(x21);
  ADDI(x10, x0, 100);
  ADDI(x11, x0, 0);
  ADDI(x12, x0, 1);
  ADDI(x13, x0, 0);
  BEQ(x13, x10, 24);
  ADD(x14, x11, x12);
  ADD(x11, x12, x0);
  ADD(x12, x14, x0);
  ADDI(x13, x13, 1);
  JAL(x0, -20);
  SLLI(x30, x11, 1);
  RDCYCLE(x22);
  RDINSTRET(x23);
  SUB(x24, x22, x20);
  SUB(x25, x23, x21);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 2048);
  cycles = uut.cpu.stage_id.regfile.regs[24];
  instrs = uut.cpu.stage_id.regfile.regs[25];
  `CHECK_CPI("fib100", fib100_max_cpi, cycles, instrs);
endtask

//
// Test: Bubble sort
//
// Implements bubble sort algorithm on an array of 8 elements.
// This comprehensive smoke test validates:
// - Nested loops with branches
// - Load/store operations
// - Address calculation
// - Comparison and conditional branches
// - Complex control flow
//
task automatic test_bubble_sort;
  logic [31:0] cycles;
  logic [31:0] instrs;

  uut.dmem.mem[0] = 32'd64;
  uut.dmem.mem[1] = 32'd34;
  uut.dmem.mem[2] = 32'd25;
  uut.dmem.mem[3] = 32'd12;
  uut.dmem.mem[4] = 32'd22;
  uut.dmem.mem[5] = 32'd11;
  uut.dmem.mem[6] = 32'd90;
  uut.dmem.mem[7] = 32'd88;

  RDCYCLE(x28);
  RDINSTRET(x29);
  ADDI(x1, x0, 0);
  ADDI(x2, x0, 8);
  ADDI(x10, x0, 0);
  ADDI(x20, x2, -1);
  BGE(x10, x20, 76);
  ADDI(x11, x0, 0);
  SUB(x12, x2, x10);
  ADDI(x12, x12, -1);
  BGE(x11, x12, 52);
  SLLI(x15, x11, 2);
  ADD(x15, x1, x15);
  ADDI(x16, x11, 1);
  SLLI(x16, x16, 2);
  ADD(x16, x1, x16);
  LW(x13, x15, 0);
  LW(x14, x16, 0);
  BLEU(x13, x14, 12);
  SW(x14, x15, 0);
  SW(x13, x16, 0);
  ADDI(x11, x11, 1);
  JAL(x0, -48);
  ADDI(x10, x10, 1);
  JAL(x0, -76);
  RDCYCLE(x30);
  RDINSTRET(x31);
  SUB(x26, x30, x28);
  SUB(x27, x31, x29);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 5000);
  `CHECK_EQ(uut.dmem.mem[0], 32'd11);
  `CHECK_EQ(uut.dmem.mem[1], 32'd12);
  `CHECK_EQ(uut.dmem.mem[2], 32'd22);
  `CHECK_EQ(uut.dmem.mem[3], 32'd25);
  `CHECK_EQ(uut.dmem.mem[4], 32'd34);
  `CHECK_EQ(uut.dmem.mem[5], 32'd64);
  `CHECK_EQ(uut.dmem.mem[6], 32'd88);
  `CHECK_EQ(uut.dmem.mem[7], 32'd90);

  cycles = uut.cpu.stage_id.regfile.regs[26];
  instrs = uut.cpu.stage_id.regfile.regs[27];
  `CHECK_CPI("bubble", bubble_max_cpi, cycles, instrs);
endtask

//
// Test: Forward taken branch loop (anti-BTFNT)
//
// This test has a forward branch that is ALWAYS taken, which is the opposite
// of what BTFNT predicts (forward branches predicted not-taken).
//
// Without BTB: Every iteration mispredicts (forward branch predicted not-taken but is taken)
// With BTB: First iteration mispredicts, then BTB learns and predicts correctly
//
// Expected improvement with BTB: Significant CPI reduction after first iteration
//
task automatic test_forward_taken_loop;
  logic [31:0] cycles;
  logic [31:0] instrs;

  RDCYCLE(x28);
  RDINSTRET(x29);
  ADDI(x10, x0, 0);
  ADDI(x11, x0, 100);

  //
  // Main loop with forward taken branch
  // PC=16: loop:
  //
  BLT(x10, x11, 12);

  //
  // Should never reach here (branch always taken)
  // PC=20:
  //
  ADDI(x12, x0, 999);
  EBREAK();

  //
  // taken_target: (PC=28)
  //
  ADDI(x10, x10, 1);
  BLT(x10, x11, -16);

  //
  // Done - measure cycles
  //
  RDCYCLE(x30);
  RDINSTRET(x31);
  SUB(x26, x30, x28);
  SUB(x27, x31, x29);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR(clk, ebreak, 2000);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[10], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[11], 32'd100);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[12], 32'd0);

  cycles = uut.cpu.stage_id.regfile.regs[26];
  instrs = uut.cpu.stage_id.regfile.regs[27];
  `CHECK_CPI("forward_taken_loop", forward_taken_loop_max_cpi, cycles, instrs);
endtask
