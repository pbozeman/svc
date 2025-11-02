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

`define CHECK_WAIT_FOR_EBREAK(clk) `CHECK_WAIT_FOR(clk, ebreak, 128)

// CHECK_XXX don't work on strings or reals, so we partially reimplement
// the checks here. String/Real detection in the core macros would be nice.
`define CHECK_CPI(name, expected_cpi, cycles, instrs)                         \
  begin                                                                       \
    real cpi_real;                                                            \
    real cpi_min;                                                             \
    real cpi_max;                                                             \
    string msg;                                                               \
    cpi_real = calc_cpi(name, cycles, instrs);                                \
    cpi_min = expected_cpi * 0.95;                                            \
    cpi_max = expected_cpi * 1.05;                                            \
    if (cpi_real < cpi_min) begin                                             \
      $sformat(msg, "%s%s%s:%s%0d%s CHECK_GTE(%scpi_real%s=%f, cpi_min=%f)",  \
               `COLOR_YELLOW, `__FILE__, `COLOR_RESET,                        \
               `COLOR_RED, `__LINE__, `COLOR_RESET,                           \
               `COLOR_YELLOW, `COLOR_RESET, cpi_real, cpi_min);               \
      `FATAL_MSG(msg);                                                        \
    end                                                                       \
    if (cpi_real > cpi_max) begin                                             \
      $sformat(msg, "%s%s%s:%s%0d%s CHECK_LTE(%scpi_real%s=%f, cpi_max=%f)",  \
               `COLOR_YELLOW, `__FILE__, `COLOR_RESET,                        \
               `COLOR_RED, `__LINE__, `COLOR_RESET,                           \
               `COLOR_YELLOW, `COLOR_RESET, cpi_real, cpi_max);               \
      `FATAL_MSG(msg);                                                        \
    end                                                                       \
  end

//
// CPI reporting control
//
bit          cpi_report_en;
logic [31:0] fib12_cpi_cycles;
logic [31:0] fib12_cpi_instrs;
real         fib12_cpi_real;
bit          fib12_cpi_valid;

logic [31:0] bubble_cpi_cycles;
logic [31:0] bubble_cpi_instrs;
real         bubble_cpi_real;
bit          bubble_cpi_valid;

initial begin
  bit svc_tb_rpt;
  if ($value$plusargs("SVC_TB_RPT=%b", svc_tb_rpt) && svc_tb_rpt) begin
    cpi_report_en = 1;
  end
end

final begin
  if (cpi_report_en) begin
    $display("");
    if (fib12_cpi_valid) begin
      $display("  %s.Fib12:", svc_tb_module_name);
      $display("    Cycles:       %0d", fib12_cpi_cycles);
      $display("    Instructions: %0d", fib12_cpi_instrs);
      $display("    CPI:          %f\n", fib12_cpi_real);
    end
    if (bubble_cpi_valid) begin
      $display("  %s.BubbleSort:", svc_tb_module_name);
      $display("    Cycles:       %0d", bubble_cpi_cycles);
      $display("    Instructions: %0d", bubble_cpi_instrs);
      $display("    CPI:          %f\n", bubble_cpi_real);
    end
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

task automatic load_program;
  int i;
  for (i = 0; i < 1024; i++) begin
    uut.imem.mem[i] = MEM[i];
  end
endtask

//
// CPI calculation function
//
function automatic real calc_cpi;
  input string name;
  input logic [31:0] cycles;
  input logic [31:0] instrs;
  real cpi_real;

  cpi_real = real'(cycles) / real'(instrs);
  if (cpi_report_en) begin
    if (name == "fib12") begin
      fib12_cpi_cycles = cycles;
      fib12_cpi_instrs = instrs;
      fib12_cpi_real   = cpi_real;
      fib12_cpi_valid  = 1;
    end else if (name == "bubble") begin
      bubble_cpi_cycles = cycles;
      bubble_cpi_instrs = instrs;
      bubble_cpi_real   = cpi_real;
      bubble_cpi_valid  = 1;
    end
  end
  return cpi_real;
endfunction
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
// Test: Reset state
//
// Verifies the processor starts with PC at address 0 after reset.
//
task automatic test_reset;
  `CHECK_EQ(uut.cpu.pc, '0);
endtask

//
// Test: Linear program execution
//
// Verifies the PC increments by 4 each cycle for sequential instructions
// (NOPs). Tests basic fetch and PC update logic.
//
task automatic test_linear_program;
  NOP();
  NOP();
  NOP();
  NOP();

  load_program();

  `TICK(clk);
  `CHECK_EQ(uut.cpu.pc, 32'd4);

  `TICK(clk);
  `CHECK_EQ(uut.cpu.pc, 32'd8);

  `TICK(clk);
  `CHECK_EQ(uut.cpu.pc, 32'd12);

  `TICK(clk);
  `CHECK_EQ(uut.cpu.pc, 32'd16);
endtask

//
// Test: EBREAK instruction
//
// Verifies the EBREAK instruction asserts the ebreak signal for one cycle.
// The processor continues execution after EBREAK (doesn't halt). It should
// be calling a trap function, but this is not implemented yet.
//
task automatic test_ebreak_instruction;
  NOP();
  EBREAK();
  NOP();

  load_program();

  `CHECK_FALSE(ebreak);

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_TRUE(ebreak);

  `TICK(clk);
  `CHECK_FALSE(ebreak);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hFFFFFFCE);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd2047);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'hFFFFF800);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd255);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd240);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd1);  // 0 < 10 (signed)
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);  // 0 >= -10 (signed)
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd1);  // 0 < 10 (unsigned)
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[7], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[8], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[9], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[10], 32'd0);
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
  `CHECK_EQ(uut.cpu.regfile.regs[0], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd0);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hFFFFFFCE);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd2047);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'hFFFFF800);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[7], 32'd15);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd255);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd240);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd255);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd15);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd1);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd0);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd1);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd2);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd32);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'h80000000);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd128);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd32);
  `CHECK_EQ(uut.cpu.regfile.regs[7], 32'hFFFFFF80);
  `CHECK_EQ(uut.cpu.regfile.regs[8], 32'hFFFFFFE0);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd50);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd150);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd50);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd40);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd255);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd240);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd240);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd255);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd15);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd8);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd2);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd32);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd2);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'hFFFFFFF8);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'hFFFFFFFE);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd20);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd1);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd0);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd15);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd200);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
  `CHECK_EQ(uut.cpu.regfile.regs[10], 32'd5);
  `CHECK_EQ(uut.cpu.regfile.regs[11], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[20], 32'd1);
  `CHECK_EQ(uut.cpu.regfile.regs[21], 32'd2);
  `CHECK_EQ(uut.cpu.regfile.regs[22], 32'd3);
  `CHECK_EQ(uut.cpu.regfile.regs[23], 32'd4);
  `CHECK_EQ(uut.cpu.regfile.regs[24], 32'd5);
endtask

//
//--------------------------------------------------------------------
// Jump tests (JAL/JALR)
//--------------------------------------------------------------------
//

//
// Test: Simple JAL
//
// Tests basic JAL functionality: jumps forward over one instruction and
// saves the return address (PC+4) in the link register.
//
task automatic test_jal_simple;
  JAL(x1, 12);
  NOP();
  ADDI(x2, x0, 99);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
endtask

//
// Test: Simple JALR
//
// Tests basic JALR functionality: computes target as base register (x0) plus
// offset, jumps to that address, and saves return address in link register.
//
task automatic test_jalr_simple;
  JALR(x1, x0, 12);
  NOP();
  ADDI(x2, x0, 99);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
endtask

//
// Test: JALR LSB clearing
//
// Tests that JALR clears the least significant bit of the computed target
// address. Uses offset 9 (odd), which should become 8 after LSB clearing.
//
// NOTE: The NOP after JALR is a workaround for pipelined implementations
// without proper flush logic. This delay shouldn't be necessary in a correct
// implementation, but we allow it for basic functionality testing. Pipeline
// hazards are tested separately.
//
task automatic test_jalr_lsb_clear;
  JALR(x1, x0, 9);
  NOP();
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd4);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd8);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd99);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd16);
endtask

//
// Test: Function call and return pattern
//
// Tests the common RISC-V calling convention pattern: JAL to save return
// address in ra (x1), execute the "function", then JALR to return using the
// saved address. This validates both jump instructions work correctly
// together for implementing function calls.
//
// NOTE: The NOPs after JAL and JALR are workarounds for pipelined
// implementations without proper flush logic. These delays shouldn't be
// necessary in a correct implementation, but we allow them for basic
// functionality testing. Pipeline hazards are tested separately.
//
task automatic test_call_return_pattern;
  JAL(ra, 12);
  NOP();
  EBREAK();
  ADDI(x2, x0, 42);
  JALR(x0, ra, 0);
  NOP();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd42);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd5);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd12);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd1);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd2);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd3);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd4);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd5);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd42);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd43);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd5);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd5);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd99);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd42);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd42);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hFFFFFFF6);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd100);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd5);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd5);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd99);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h12345000);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hABCDE000);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'h00001000);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h00000000);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'hFFFFF000);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h00001000);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'h00002004);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h00000000);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'hFFFFF00C);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd100);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'hFFFFFFCE);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h12345678);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hDEADBEEF);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h12345678);
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
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hDEADBEEF);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'h12345678);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'hCAFEBABE);
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
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hFFFFFFEF);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'hFFFFFFCD);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'hFFFFFFAB);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'hFFFFFF89);
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
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'h000000EF);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'h000000CD);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'h000000AB);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'h00000089);
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
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'hFFFFCDEF);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'hFFFF8765);
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
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'h0000CDEF);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'h00008765);
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
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'h11223344);
  `CHECK_EQ(uut.dmem.mem[0], 32'h11223344);
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
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'd0);
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd42);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd43);
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
  `CHECK_EQ(uut.cpu.regfile.regs[2], 32'd10);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd20);
  `CHECK_EQ(uut.cpu.regfile.regs[4], 32'd30);
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'd30);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'd60);
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
  `CHECK_EQ(uut.cpu.regfile.regs[5], 32'h56783412);
  `CHECK_EQ(uut.cpu.regfile.regs[6], 32'h00003412);
  `CHECK_EQ(uut.cpu.regfile.regs[7], 32'h00000056);
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
  `CHECK_TRUE(uut.cpu.regfile.regs[1] > 32'h0);
endtask

//
// Test: RDCYCLEH reads cycle counter high word
//
task automatic test_rdcycleh;
  RDCYCLEH(x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h0);
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
  `CHECK_TRUE(uut.cpu.regfile.regs[1] > 32'h0);
endtask

//
// Test: RDINSTRETH reads instruction counter high word
//
task automatic test_rdinstreth;
  RDINSTRETH(x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.regfile.regs[1], 32'h0);
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
  `CHECK_TRUE(uut.cpu.regfile.regs[1] > 32'h0);
  `CHECK_TRUE(uut.cpu.regfile.regs[2] > uut.cpu.regfile.regs[1]);
  `CHECK_TRUE(uut.cpu.regfile.regs[3] > 32'h0);
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
  `CHECK_TRUE(uut.cpu.regfile.regs[1] > 32'h0);
  `CHECK_TRUE(uut.cpu.regfile.regs[2] > uut.cpu.regfile.regs[1]);
  `CHECK_EQ(uut.cpu.regfile.regs[3], 32'd4);
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
  `CHECK_EQ(uut.cpu.regfile.regs[11], 32'd144);
  `CHECK_EQ(uut.cpu.regfile.regs[30], 32'd288);

  cycles = uut.cpu.regfile.regs[24];
  instrs = uut.cpu.regfile.regs[25];
  `CHECK_CPI("fib12", fib12_expected_cpi, cycles, instrs);
endtask

//
// Test: Bubble sort (requires dmem - not yet implemented)
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

  cycles = uut.cpu.regfile.regs[26];
  instrs = uut.cpu.regfile.regs[27];
  `CHECK_CPI("bubble", bubble_expected_cpi, cycles, instrs);
endtask
