`include "svc_unit.sv"

`include "svc_rv_reg_pc_if.sv"

module svc_rv_reg_pc_if_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int XLEN = 32;

  logic            stall;
  logic [XLEN-1:0] pc_in;
  logic [XLEN-1:0] pc_plus4_in;
  logic [XLEN-1:0] pc_out_delay;
  logic [XLEN-1:0] pc_plus4_out_delay;
  logic [XLEN-1:0] pc_out_passthrough;
  logic [XLEN-1:0] pc_plus4_out_passthrough;

  //
  // Registered version (PC_DELAY=1)
  //
  svc_rv_reg_pc_if #(
      .XLEN    (XLEN),
      .PC_DELAY(1)
  ) uut_delay (
      .clk         (clk),
      .rst_n       (rst_n),
      .stall       (stall),
      .pc_in       (pc_in),
      .pc_plus4_in (pc_plus4_in),
      .pc_out      (pc_out_delay),
      .pc_plus4_out(pc_plus4_out_delay)
  );

  //
  // Passthrough version (PC_DELAY=0)
  //
  svc_rv_reg_pc_if #(
      .XLEN    (XLEN),
      .PC_DELAY(0)
  ) uut_passthrough (
      .clk         (clk),
      .rst_n       (rst_n),
      .stall       (stall),
      .pc_in       (pc_in),
      .pc_plus4_in (pc_plus4_in),
      .pc_out      (pc_out_passthrough),
      .pc_plus4_out(pc_plus4_out_passthrough)
  );

  //
  // Test: Reset values
  //
  task automatic test_reset;
    stall       = 0;
    pc_in       = 32'h0;
    pc_plus4_in = 32'h4;

    `CHECK_EQ(pc_out_delay, 32'h0);
    `CHECK_EQ(pc_plus4_out_delay, 32'h4);
    `CHECK_EQ(pc_out_passthrough, 32'h0);
    `CHECK_EQ(pc_plus4_out_passthrough, 32'h4);
  endtask

  //
  // Test: Passthrough mode
  //
  task automatic test_passthrough;
    stall       = 0;
    pc_in       = 32'h100;
    pc_plus4_in = 32'h104;

    `TICK(clk);

    `CHECK_EQ(pc_out_passthrough, 32'h100);
    `CHECK_EQ(pc_plus4_out_passthrough, 32'h104);

    pc_in       = 32'h200;
    pc_plus4_in = 32'h204;

    `TICK(clk);

    `CHECK_EQ(pc_out_passthrough, 32'h200);
    `CHECK_EQ(pc_plus4_out_passthrough, 32'h204);
  endtask

  //
  // Test: Registered delay
  //
  task automatic test_registered_delay;
    stall       = 0;
    pc_in       = 32'h100;
    pc_plus4_in = 32'h104;

    `TICK(clk);

    `CHECK_EQ(pc_out_delay, 32'h100);
    `CHECK_EQ(pc_plus4_out_delay, 32'h104);

    pc_in       = 32'h200;
    pc_plus4_in = 32'h204;

    `TICK(clk);

    `CHECK_EQ(pc_out_delay, 32'h200);
    `CHECK_EQ(pc_plus4_out_delay, 32'h204);
  endtask

  //
  // Test: Stall holds values
  //
  task automatic test_stall;
    stall       = 0;
    pc_in       = 32'h100;
    pc_plus4_in = 32'h104;

    `TICK(clk);

    `CHECK_EQ(pc_out_delay, 32'h100);
    `CHECK_EQ(pc_plus4_out_delay, 32'h104);

    stall       = 1;
    pc_in       = 32'h200;
    pc_plus4_in = 32'h204;

    `TICK(clk);

    `CHECK_EQ(pc_out_delay, 32'h100);
    `CHECK_EQ(pc_plus4_out_delay, 32'h104);

    stall = 0;

    `TICK(clk);

    `CHECK_EQ(pc_out_delay, 32'h200);
    `CHECK_EQ(pc_plus4_out_delay, 32'h204);
  endtask

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_reg_pc_if_tb, 100);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_passthrough);
  `TEST_CASE(test_registered_delay);
  `TEST_CASE(test_stall);
  `TEST_SUITE_END();

endmodule
