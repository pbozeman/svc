`include "svc_unit.sv"

`include "svc_rv_pc.sv"

module svc_rv_pc_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic        stall;
  logic        pc_sel;
  logic [31:0] jb_target;
  logic [31:0] pc;
  logic [31:0] pc_plus4;

  svc_rv_pc uut (
      .clk      (clk),
      .rst_n    (rst_n),
      .stall    (stall),
      .pc_sel   (pc_sel),
      .jb_target(jb_target),
      .pc       (pc),
      .pc_plus4 (pc_plus4)
  );

  initial begin
    stall     = 0;
    pc_sel    = 0;
    jb_target = 0;
  end

  task automatic test_reset;
    `CHECK_EQ(pc, 32'd0);
    `CHECK_EQ(pc_plus4, 32'd4);
  endtask

  task automatic test_pc_increment;
    `CHECK_EQ(pc, 32'd0);
    `CHECK_EQ(pc_plus4, 32'd4);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd4);
    `CHECK_EQ(pc_plus4, 32'd8);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd8);
    `CHECK_EQ(pc_plus4, 32'd12);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd12);
    `CHECK_EQ(pc_plus4, 32'd16);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd16);
    `CHECK_EQ(pc_plus4, 32'd20);
  endtask

  task automatic test_pc_increment_continuous;
    int i;
    for (i = 0; i < 16; i++) begin
      `CHECK_EQ(pc, i * 4);
      `CHECK_EQ(pc_plus4, (i + 1) * 4);
      `TICK(clk);
    end
  endtask

  task automatic test_reset_during_increment;
    `CHECK_EQ(pc, 32'd0);
    `CHECK_EQ(pc_plus4, 32'd4);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd4);
    `CHECK_EQ(pc_plus4, 32'd8);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd8);
    `CHECK_EQ(pc_plus4, 32'd12);

    rst_n = 0;
    `TICK(clk);
    `CHECK_EQ(pc, 32'd0);
    `CHECK_EQ(pc_plus4, 32'd4);

    rst_n = 1;
    `TICK(clk);
    `CHECK_EQ(pc, 32'd4);
    `CHECK_EQ(pc_plus4, 32'd8);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd8);
    `CHECK_EQ(pc_plus4, 32'd12);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_pc_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_pc_increment);
  `TEST_CASE(test_pc_increment_continuous);
  `TEST_CASE(test_reset_during_increment);
  `TEST_SUITE_END();

endmodule
