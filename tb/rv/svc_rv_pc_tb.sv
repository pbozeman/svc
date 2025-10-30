`include "svc_unit.sv"

`include "svc_rv_pc.sv"

module svc_rv_pc_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [31:0] pc;

  svc_rv_pc uut (
      .clk  (clk),
      .rst_n(rst_n),
      .pc   (pc)
  );

  task automatic test_reset;
    `CHECK_EQ(pc, 32'd0);
  endtask

  task automatic test_pc_increment;
    `CHECK_EQ(pc, 32'd0);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd4);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd8);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd12);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd16);
  endtask

  task automatic test_pc_increment_continuous;
    int i;
    for (i = 0; i < 16; i++) begin
      `CHECK_EQ(pc, i * 4);
      `TICK(clk);
    end
  endtask

  task automatic test_reset_during_increment;
    `CHECK_EQ(pc, 32'd0);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd4);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd8);

    rst_n = 0;
    `TICK(clk);
    `CHECK_EQ(pc, 32'd0);

    rst_n = 1;
    `TICK(clk);
    `CHECK_EQ(pc, 32'd4);

    `TICK(clk);
    `CHECK_EQ(pc, 32'd8);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_pc_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_pc_increment);
  `TEST_CASE(test_pc_increment_continuous);
  `TEST_CASE(test_reset_during_increment);
  `TEST_SUITE_END();

endmodule
