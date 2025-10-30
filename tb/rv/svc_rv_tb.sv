`include "svc_unit.sv"

`include "svc_rv.sv"

module svc_rv_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int IMEM_AW = 10;
  logic ebreak;

  svc_rv #(
      .IMEM_AW(IMEM_AW)
  ) uut (
      .clk   (clk),
      .rst_n (rst_n),
      .ebreak(ebreak)
  );

  logic [31:0] MEM[1024];
  `include "svc_rv_asm.svh"

  `define CHECK_WAIT_FOR_EBREAK(clk) `CHECK_WAIT_FOR(clk, ebreak, 128)

  // Reset assembly state on reset
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
    `CHECK_EQ(uut.pc, '0);
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
    `CHECK_EQ(uut.pc, 32'd4);

    `TICK(clk);
    `CHECK_EQ(uut.pc, 32'd8);

    `TICK(clk);
    `CHECK_EQ(uut.pc, 32'd12);

    `TICK(clk);
    `CHECK_EQ(uut.pc, 32'd16);
  endtask

  //
  // Test: EBREAK instruction
  //
  // Verifies the EBREAK instruction asserts the ebreak signal for one cycle.
  // The processor continues execution after EBREAK (doesn't halt). It should
  // be calling a trap function, but this is not implemented yet.
  //
  task automatic test_ebreak_instruction;
    EBREAK();
    NOP();

    load_program();

    // After reset, ebreak should be low
    `CHECK_FALSE(ebreak);

    `TICK(clk);
    `CHECK_TRUE(ebreak);

    // We don't currently stop on ebreak
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd42);
    `CHECK_EQ(uut.regfile.regs[2], 32'hFFFFFFCE);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
    `CHECK_EQ(uut.regfile.regs[4], 32'd2047);
    `CHECK_EQ(uut.regfile.regs[5], 32'hFFFFF800);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd255);
    `CHECK_EQ(uut.regfile.regs[2], 32'd240);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd0);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd1);  // 0 < 10 (signed)
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);  // 0 >= -10 (signed)
    `CHECK_EQ(uut.regfile.regs[3], 32'd1);  // 0 < 10 (unsigned)
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd0);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
    `CHECK_EQ(uut.regfile.regs[4], 32'd0);
    `CHECK_EQ(uut.regfile.regs[5], 32'd0);
    `CHECK_EQ(uut.regfile.regs[6], 32'd0);
    `CHECK_EQ(uut.regfile.regs[7], 32'd0);
    `CHECK_EQ(uut.regfile.regs[8], 32'd0);
    `CHECK_EQ(uut.regfile.regs[9], 32'd0);
    `CHECK_EQ(uut.regfile.regs[10], 32'd0);
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
    `CHECK_EQ(uut.regfile.regs[0], 32'd0);
    `CHECK_EQ(uut.regfile.regs[1], 32'd0);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd100);
    `CHECK_EQ(uut.regfile.regs[2], 32'hFFFFFFCE);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
    `CHECK_EQ(uut.regfile.regs[4], 32'd2047);
    `CHECK_EQ(uut.regfile.regs[5], 32'hFFFFF800);
    `CHECK_EQ(uut.regfile.regs[6], 32'd10);
    `CHECK_EQ(uut.regfile.regs[7], 32'd15);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd255);
    `CHECK_EQ(uut.regfile.regs[2], 32'd240);
    `CHECK_EQ(uut.regfile.regs[3], 32'd255);
    `CHECK_EQ(uut.regfile.regs[4], 32'd15);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd10);
    `CHECK_EQ(uut.regfile.regs[2], 32'd1);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
    `CHECK_EQ(uut.regfile.regs[4], 32'hFFFFFFF6);
    `CHECK_EQ(uut.regfile.regs[5], 32'd0);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd1);
    `CHECK_EQ(uut.regfile.regs[2], 32'd2);
    `CHECK_EQ(uut.regfile.regs[3], 32'd32);
    `CHECK_EQ(uut.regfile.regs[4], 32'h80000000);
    `CHECK_EQ(uut.regfile.regs[5], 32'd128);
    `CHECK_EQ(uut.regfile.regs[6], 32'd32);
    `CHECK_EQ(uut.regfile.regs[7], 32'hFFFFFF80);
    `CHECK_EQ(uut.regfile.regs[8], 32'hFFFFFFE0);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd100);
    `CHECK_EQ(uut.regfile.regs[2], 32'd50);
    `CHECK_EQ(uut.regfile.regs[3], 32'd150);
    `CHECK_EQ(uut.regfile.regs[4], 32'd50);
    `CHECK_EQ(uut.regfile.regs[5], 32'hFFFFFFF6);
    `CHECK_EQ(uut.regfile.regs[6], 32'd40);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd255);
    `CHECK_EQ(uut.regfile.regs[2], 32'd240);
    `CHECK_EQ(uut.regfile.regs[3], 32'd240);
    `CHECK_EQ(uut.regfile.regs[4], 32'd255);
    `CHECK_EQ(uut.regfile.regs[5], 32'd15);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd8);
    `CHECK_EQ(uut.regfile.regs[2], 32'd2);
    `CHECK_EQ(uut.regfile.regs[3], 32'd32);
    `CHECK_EQ(uut.regfile.regs[4], 32'd2);
    `CHECK_EQ(uut.regfile.regs[5], 32'hFFFFFFF8);
    `CHECK_EQ(uut.regfile.regs[6], 32'hFFFFFFFE);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd10);
    `CHECK_EQ(uut.regfile.regs[2], 32'd20);
    `CHECK_EQ(uut.regfile.regs[3], 32'd1);
    `CHECK_EQ(uut.regfile.regs[4], 32'd0);
    `CHECK_EQ(uut.regfile.regs[5], 32'hFFFFFFF6);
    `CHECK_EQ(uut.regfile.regs[6], 32'd0);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd10);
    `CHECK_EQ(uut.regfile.regs[2], 32'd15);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd100);
    `CHECK_EQ(uut.regfile.regs[2], 32'd200);
    `CHECK_EQ(uut.regfile.regs[3], 32'd100);
    `CHECK_EQ(uut.regfile.regs[10], 32'd5);
    `CHECK_EQ(uut.regfile.regs[11], 32'd10);
    `CHECK_EQ(uut.regfile.regs[20], 32'd1);
    `CHECK_EQ(uut.regfile.regs[21], 32'd2);
    `CHECK_EQ(uut.regfile.regs[22], 32'd3);
    `CHECK_EQ(uut.regfile.regs[23], 32'd4);
    `CHECK_EQ(uut.regfile.regs[24], 32'd5);
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
    JAL(x1, 8);
    ADDI(x2, x0, 99);
    EBREAK();

    load_program();

    `CHECK_WAIT_FOR_EBREAK(clk);
    `CHECK_EQ(uut.regfile.regs[1], 32'd4);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
  endtask

  //
  // Test: Simple JALR
  //
  // Tests basic JALR functionality: computes target as base register (x0) plus
  // offset, jumps to that address, and saves return address in link register.
  //
  task automatic test_jalr_simple;
    JALR(x1, x0, 8);
    ADDI(x2, x0, 99);
    EBREAK();

    load_program();

    `CHECK_WAIT_FOR_EBREAK(clk);
    `CHECK_EQ(uut.regfile.regs[1], 32'd4);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
  endtask

  //
  // Test: JALR LSB clearing
  //
  // Tests that JALR clears the least significant bit of the computed target
  // address. Uses offset 9 (odd), which should become 8 after LSB clearing.
  //
  task automatic test_jalr_lsb_clear;
    JALR(x1, x0, 9);
    ADDI(x2, x0, 99);
    EBREAK();

    load_program();

    `CHECK_WAIT_FOR_EBREAK(clk);
    `CHECK_EQ(uut.regfile.regs[1], 32'd4);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
  endtask

  //
  // Test: JALR with base register
  //
  // Tests JALR with a non-zero base register. Target is computed as x5 + (-8)
  // = 16 - 8 = 8, demonstrating register-based indirect jumps.
  //
  task automatic test_jalr_with_base_register;
    ADDI(x5, x0, 16);
    JALR(x1, x5, -8);
    ADDI(x2, x0, 99);
    EBREAK();

    load_program();

    `CHECK_WAIT_FOR_EBREAK(clk);
    `CHECK_EQ(uut.regfile.regs[1], 32'd8);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
    `CHECK_EQ(uut.regfile.regs[5], 32'd16);
  endtask

  //
  // Test: Function call and return pattern
  //
  // Tests the common RISC-V calling convention pattern: JAL to save return
  // address in ra (x1), execute the "function", then JALR to return using the
  // saved address. This validates both jump instructions work correctly
  // together for implementing function calls.
  //
  task automatic test_call_return_pattern;
    JAL(ra, 8);
    EBREAK();
    ADDI(x2, x0, 42);
    JALR(x0, ra, 0);

    load_program();

    `CHECK_WAIT_FOR_EBREAK(clk);
    `CHECK_EQ(uut.regfile.regs[1], 32'd4);
    `CHECK_EQ(uut.regfile.regs[2], 32'd42);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd4);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
    `CHECK_EQ(uut.regfile.regs[4], 32'd0);
    `CHECK_EQ(uut.regfile.regs[5], 32'd0);
    `CHECK_EQ(uut.regfile.regs[6], 32'd5);
  endtask

  //
  // Test: JAL forward jump skipping one instruction
  //
  // Tests pipeline behavior when jumping forward past a single instruction.
  // The ADDI(x4) should be skipped (x4 stays 0). This test validates that the
  // processor correctly handles the pipeline flush for a smaller jump offset.
  //
  task automatic test_jal_backward_pipeline;
    ADDI(x2, x0, 1);
    ADDI(x3, x0, 2);
    JAL(x1, 12);
    ADDI(x4, x0, 99);
    ADDI(x5, x0, 3);
    EBREAK();

    load_program();

    `CHECK_WAIT_FOR_EBREAK(clk);
    `CHECK_EQ(uut.regfile.regs[1], 32'd12);
    `CHECK_EQ(uut.regfile.regs[2], 32'd1);
    `CHECK_EQ(uut.regfile.regs[3], 32'd2);
    `CHECK_EQ(uut.regfile.regs[4], 32'd0);
    `CHECK_EQ(uut.regfile.regs[5], 32'd3);
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
    `CHECK_EQ(uut.regfile.regs[1], 32'd4);
    `CHECK_EQ(uut.regfile.regs[2], 32'd0);
    `CHECK_EQ(uut.regfile.regs[3], 32'd0);
    `CHECK_EQ(uut.regfile.regs[4], 32'd0);
    `CHECK_EQ(uut.regfile.regs[5], 32'd0);
    `CHECK_EQ(uut.regfile.regs[6], 32'd5);
  endtask

  //
  // Test setup
  //
  `TEST_SUITE_BEGIN(svc_rv_tb);

  // Basic tests
  `TEST_CASE(test_reset);
  `TEST_CASE(test_linear_program);
  `TEST_CASE(test_ebreak_instruction);

  // Tests with no register dependencies (all read from x0)
  `TEST_CASE(test_addi_from_x0);
  `TEST_CASE(test_logical_from_x0);
  `TEST_CASE(test_shift_from_x0);
  `TEST_CASE(test_compare_from_x0);
  `TEST_CASE(test_r_type_from_x0);
  `TEST_CASE(test_x0_immutable);

  // I-type tests with register dependencies
  `TEST_CASE(test_addi);
  `TEST_CASE(test_i_type_logical);
  `TEST_CASE(test_i_type_compare);
  `TEST_CASE(test_i_type_shift);

  // R-type tests with register dependencies
  `TEST_CASE(test_r_type_arithmetic);
  `TEST_CASE(test_r_type_logical);
  `TEST_CASE(test_r_type_shift);
  `TEST_CASE(test_r_type_compare);

  // Read-after-write dependency tests
  `TEST_CASE(test_raw_dependency);
  //
  // Dependency stress test - deep chains that stress forwarding/stalls
  `TEST_CASE(test_chained_dependencies);

  // Jump tests (JAL/JALR) - uncomment when JAL/JALR are implemented
  // `TEST_CASE(test_jal_simple);
  // `TEST_CASE(test_jalr_simple);
  // `TEST_CASE(test_jalr_lsb_clear);
  // `TEST_CASE(test_jalr_with_base_register);
  // `TEST_CASE(test_call_return_pattern);
  //
  // Pipeline stress tests - validate instruction flushing on control flow
  // `TEST_CASE(test_jal_forward_pipeline);
  // `TEST_CASE(test_jal_backward_pipeline);
  // `TEST_CASE(test_jalr_forward_pipeline);

  `TEST_SUITE_END();

endmodule
