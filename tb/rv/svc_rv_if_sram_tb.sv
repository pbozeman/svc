`include "svc_unit.sv"

`include "svc_rv_if_sram.sv"

module svc_rv_if_sram_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int XLEN = 32;

  logic            if_id_stall;
  logic            if_id_flush;
  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_plus4;
  logic [    31:0] instr_sram;
  logic [XLEN-1:0] pc_to_if_id;
  logic [XLEN-1:0] pc_plus4_to_if_id;
  logic [    31:0] instr_id;

  `include "svc_rv_defs.svh"

svc_rv_if_sram #(
      .XLEN     (XLEN),
      .PIPELINED(1)
  ) uut (
      .clk              (clk),
      .rst_n            (rst_n),
      .if_id_stall      (if_id_stall),
      .if_id_flush      (if_id_flush),
      .pc               (pc),
      .pc_plus4         (pc_plus4),
      .instr_sram       (instr_sram),
      .pc_to_if_id      (pc_to_if_id),
      .pc_plus4_to_if_id(pc_plus4_to_if_id),
      .instr_id         (instr_id)
  );

  task automatic test_reset;
    if_id_stall = 1'b0;
    if_id_flush = 1'b0;
    pc          = 32'h0;
    pc_plus4    = 32'h4;
    instr_sram  = I_NOP;

    `TICK(clk);

    `CHECK_EQ(instr_id, I_NOP);
    `CHECK_EQ(pc_to_if_id, 32'h0);
    `CHECK_EQ(pc_plus4_to_if_id, 32'h4);
  endtask

  task automatic test_normal_flow;
    if_id_stall = 1'b0;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_sram  = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);
    `CHECK_EQ(pc_to_if_id, 32'h1000);
    `CHECK_EQ(pc_plus4_to_if_id, 32'h1004);

    pc         = 32'h1004;
    pc_plus4   = 32'h1008;
    instr_sram = 32'h9abcdef0;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h9abcdef0);
    `CHECK_EQ(pc_to_if_id, 32'h1004);
    `CHECK_EQ(pc_plus4_to_if_id, 32'h1008);
  endtask

  task automatic test_stall;
    if_id_stall = 1'b0;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_sram  = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);

    if_id_stall = 1'b1;
    pc          = 32'h1004;
    pc_plus4    = 32'h1008;
    instr_sram  = 32'h9abcdef0;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);
    `CHECK_EQ(pc_to_if_id, 32'h1004);
  endtask

  task automatic test_flush;
    if_id_stall = 1'b0;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_sram  = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);

    if_id_flush = 1'b1;
    pc          = 32'h2000;
    pc_plus4    = 32'h2004;
    instr_sram  = 32'h9abcdef0;

    `TICK(clk);

    `CHECK_EQ(instr_id, I_NOP);
    `CHECK_EQ(pc_to_if_id, 32'h2000);

    if_id_flush = 1'b0;
    pc          = 32'h2004;
    pc_plus4    = 32'h2008;
    instr_sram  = 32'hfedcba98;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'hfedcba98);
  endtask

  task automatic test_pc_passthrough;
    if_id_stall = 1'b0;
    if_id_flush = 1'b0;
    pc          = 32'h1234;
    pc_plus4    = 32'h1238;
    instr_sram  = 32'h00000000;

    `TICK(clk);

    `CHECK_EQ(pc_to_if_id, 32'h1234);
    `CHECK_EQ(pc_plus4_to_if_id, 32'h1238);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_if_sram_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_normal_flow);
  `TEST_CASE(test_stall);
  `TEST_CASE(test_flush);
  `TEST_CASE(test_pc_passthrough);
  `TEST_SUITE_END();

endmodule
