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

  task automatic test_reset;
    `CHECK_EQ(uut.pc, '0);
  endtask

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

  // Math tests with no hazards - all operations read from x0 only
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
  // Test setup
  //
  `TEST_SUITE_BEGIN(svc_rv_tb);

  // Basic tests
  `TEST_CASE(test_reset);
  `TEST_CASE(test_linear_program);
  `TEST_CASE(test_ebreak_instruction);

  // I-type arithmetic tests (no hazards)
  `TEST_CASE(test_addi_from_x0);
  `TEST_CASE(test_logical_from_x0);
  `TEST_CASE(test_shift_from_x0);
  `TEST_CASE(test_compare_from_x0);

  // R-type tests (no hazards)
  `TEST_CASE(test_r_type_from_x0);
  `TEST_CASE(test_x0_immutable);

  `TEST_SUITE_END();

endmodule
