`include "svc_unit.sv"

`include "svc_rv_if_bram.sv"

module svc_rv_if_bram_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int XLEN = 32;

  logic            m_ready;
  logic            if_id_flush;
  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_plus4;
  logic [    31:0] instr_bram;
  logic [XLEN-1:0] pc_to_if_id;
  logic [XLEN-1:0] pc_plus4_to_if_id;
  logic [    31:0] instr_id;

  `include "svc_rv_defs.svh"

svc_rv_if_bram #(
      .XLEN(XLEN)
  ) uut (
      .clk              (clk),
      .rst_n            (rst_n),
      .m_ready          (m_ready),
      .if_id_flush      (if_id_flush),
      .pc               (pc),
      .pc_plus4         (pc_plus4),
      .instr_bram       (instr_bram),
      .pc_to_if_id      (pc_to_if_id),
      .pc_plus4_to_if_id(pc_plus4_to_if_id),
      .instr_id         (instr_id)
  );

  task automatic test_reset;
    m_ready     = 1'b1;
    if_id_flush = 1'b0;
    pc          = 32'h0;
    pc_plus4    = 32'h4;
    instr_bram  = I_NOP;

    `TICK(clk);

    `CHECK_EQ(instr_id, I_NOP);
    `CHECK_EQ(pc_to_if_id, 32'h0);
    `CHECK_EQ(pc_plus4_to_if_id, 32'h4);
  endtask

  task automatic test_pc_buffering;
    m_ready     = 1'b1;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_bram  = 32'h00000000;

    `TICK(clk);

    `CHECK_EQ(pc_to_if_id, 32'h1000);
    `CHECK_EQ(pc_plus4_to_if_id, 32'h1004);

    pc       = 32'h1004;
    pc_plus4 = 32'h1008;

    `TICK(clk);

    `CHECK_EQ(pc_to_if_id, 32'h1004);
    `CHECK_EQ(pc_plus4_to_if_id, 32'h1008);
  endtask

  task automatic test_normal_flow;
    m_ready     = 1'b1;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_bram  = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);

    pc         = 32'h1004;
    pc_plus4   = 32'h1008;
    instr_bram = 32'h9abcdef0;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h9abcdef0);
  endtask

  task automatic test_stall;
    m_ready     = 1'b1;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_bram  = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);
    `CHECK_EQ(pc_to_if_id, 32'h1000);

    m_ready    = 1'b0;
    pc         = 32'h1004;
    pc_plus4   = 32'h1008;
    instr_bram = 32'h9abcdef0;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);
    `CHECK_EQ(pc_to_if_id, 32'h1000);
  endtask

  task automatic test_flush;
    m_ready     = 1'b1;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_bram  = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);

    if_id_flush = 1'b1;
    pc          = 32'h2000;
    pc_plus4    = 32'h2004;
    instr_bram  = 32'h9abcdef0;

    `TICK(clk);

    `CHECK_EQ(instr_id, I_NOP);
  endtask

  task automatic test_extended_flush;
    m_ready     = 1'b1;
    if_id_flush = 1'b0;
    pc          = 32'h1000;
    pc_plus4    = 32'h1004;
    instr_bram  = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h12345678);

    if_id_flush = 1'b1;
    pc          = 32'h2000;
    pc_plus4    = 32'h2004;
    instr_bram  = 32'h9abcdef0;

    `TICK(clk);

    `CHECK_EQ(instr_id, I_NOP);

    if_id_flush = 1'b0;
    pc          = 32'h2004;
    pc_plus4    = 32'h2008;
    instr_bram  = 32'hfedcba98;

    `TICK(clk);

    `CHECK_EQ(instr_id, I_NOP);

    pc         = 32'h2008;
    pc_plus4   = 32'h200c;
    instr_bram = 32'h11223344;

    `TICK(clk);

    `CHECK_EQ(instr_id, 32'h11223344);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_if_bram_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_pc_buffering);
  `TEST_CASE(test_normal_flow);
  `TEST_CASE(test_stall);
  `TEST_CASE(test_flush);
  `TEST_CASE(test_extended_flush);
  `TEST_SUITE_END();

endmodule
