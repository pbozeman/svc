`include "svc_unit.sv"
`include "svc_sticky_bit.sv"

module svc_sticky_bit_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic clear;
  logic in;
  logic out;

  svc_sticky_bit uut (
      .clk  (clk),
      .rst_n(rst_n),
      .clear(clear),
      .in   (in),
      .out  (out)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      clear <= 1'b0;
      in    <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(out);
    `TICK(clk);
    `CHECK_FALSE(out);
  endtask

  task automatic test_basic_operation();
    in = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(out);

    in = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(out);

    clear = 1'b1;
    `TICK(clk);
    `CHECK_FALSE(out);

    clear = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(out);
  endtask

  task automatic test_input_changes();
    in = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(out);

    in = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(out);

    clear = 1'b1;
    `TICK(clk);
    `CHECK_FALSE(out);

    clear = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(out);

    in = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(out);

    in = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(out);
  endtask

  task automatic test_in_priority();
    in    = 1'b1;
    clear = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(out);

    clear = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(out);
  endtask

  task automatic test_multiple_cycles();
    in    = 1'b0;
    clear = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(out);

    in = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(out);

    in = 1'b0;
    repeat (5) begin
      `TICK(clk);
      `CHECK_TRUE(out);
    end

    clear = 1'b1;
    `TICK(clk);
    `CHECK_FALSE(out);

    clear = 1'b0;
    repeat (3) begin
      `TICK(clk);
      `CHECK_FALSE(out);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_sticky_bit_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_operation);
  `TEST_CASE(test_input_changes);
  `TEST_CASE(test_in_priority);
  `TEST_CASE(test_multiple_cycles);
  `TEST_SUITE_END();
endmodule
