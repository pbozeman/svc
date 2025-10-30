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
      uut.imem_i.mem[i] = MEM[i];
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


  `TEST_SUITE_BEGIN(svc_rv_tb);

  // Basic tests
  `TEST_CASE(test_reset);
  `TEST_CASE(test_linear_program);
  `TEST_CASE(test_ebreak_instruction);

  `TEST_SUITE_END();

endmodule
