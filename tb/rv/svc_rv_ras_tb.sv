`include "svc_unit.sv"

`include "svc_rv_ras.sv"

module svc_rv_ras_tb;
  localparam XLEN = 32;
  localparam DEPTH = 8;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic            ras_valid;
  logic [XLEN-1:0] ras_tgt;
  logic            push_en;
  logic [XLEN-1:0] push_addr;
  logic            pop_en;

  svc_rv_ras #(
      .XLEN (XLEN),
      .DEPTH(DEPTH)
  ) uut (
      .clk      (clk),
      .rst_n    (rst_n),
      .ras_valid(ras_valid),
      .ras_tgt  (ras_tgt),
      .push_en  (push_en),
      .push_addr(push_addr),
      .pop_en   (pop_en)
  );

  //
  // Test: Reset state
  //
  task automatic test_reset;
    `CHECK_FALSE(ras_valid);
    `CHECK_EQ(ras_tgt, 0);
  endtask

  //
  // Test: Single push and pop
  //
  task automatic test_single_push_pop;
    push_en   = 1'b1;
    push_addr = 32'h1000;
    pop_en    = 1'b0;

    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h1000);

    push_en = 1'b0;
    pop_en  = 1'b1;

    `TICK(clk);
    `CHECK_FALSE(ras_valid);

    push_en = 1'b0;
    pop_en  = 1'b0;

    `TICK(clk);
  endtask

  //
  // Test: Multiple pushes
  //
  task automatic test_multiple_pushes;
    push_en   = 1'b1;
    pop_en    = 1'b0;

    push_addr = 32'h1000;
    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h1000);

    push_addr = 32'h2000;
    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h2000);

    push_addr = 32'h3000;
    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h3000);

    push_en = 1'b0;
    pop_en  = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h2000);

    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h1000);

    `TICK(clk);
    `CHECK_FALSE(ras_valid);

    push_en = 1'b0;
    pop_en  = 1'b0;

    `TICK(clk);
  endtask

  //
  // Test: Stack overflow
  //
  task automatic test_overflow;
    int i;

    push_en = 1'b1;
    pop_en  = 1'b0;

    for (i = 0; i < DEPTH + 2; i = i + 1) begin
      push_addr = 32'h1000 + (i << 2);
      `TICK(clk);
      `CHECK_TRUE(ras_valid);
    end

    push_en = 1'b0;
    pop_en  = 1'b1;

    for (i = 0; i < DEPTH; i = i + 1) begin
      `TICK(clk);
    end

    `CHECK_FALSE(ras_valid);

    push_en = 1'b0;
    pop_en  = 1'b0;

    `TICK(clk);
  endtask

  //
  // Test: Pop when empty
  //
  task automatic test_pop_empty;
    push_en = 1'b0;
    pop_en  = 1'b1;

    `TICK(clk);
    `CHECK_FALSE(ras_valid);

    `TICK(clk);
    `CHECK_FALSE(ras_valid);

    push_en = 1'b0;
    pop_en  = 1'b0;

    `TICK(clk);
  endtask

  //
  // Test: Simultaneous push and pop
  //
  task automatic test_push_pop_simultaneous;
    push_en   = 1'b1;
    push_addr = 32'h1000;
    pop_en    = 1'b0;

    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h1000);

    push_en   = 1'b1;
    push_addr = 32'h2000;
    pop_en    = 1'b1;

    `TICK(clk);
    `CHECK_TRUE(ras_valid);
    `CHECK_EQ(ras_tgt, 32'h2000);

    push_en = 1'b0;
    pop_en  = 1'b0;

    `TICK(clk);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_ras_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_single_push_pop);
  `TEST_CASE(test_multiple_pushes);
  `TEST_CASE(test_overflow);
  `TEST_CASE(test_pop_empty);
  `TEST_CASE(test_push_pop_simultaneous);
  `TEST_SUITE_END();

endmodule
