`include "svc_unit.sv"
`include "svc_rv_detect.sv"

module svc_rv_detect_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic valid;
  logic ready;
  logic txn_started;
  logic txn_stalled;
  logic txn_accepted;

  svc_rv_detect uut (
      .clk         (clk),
      .rst_n       (rst_n),
      .valid       (valid),
      .ready       (ready),
      .txn_started (txn_started),
      .txn_stalled (txn_stalled),
      .txn_accepted(txn_accepted)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      valid <= 1'b0;
      ready <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_FALSE(txn_accepted);
  endtask

  task automatic test_basic_handshake();
    valid = 1'b0;
    ready = 1'b1;

    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_FALSE(txn_accepted);

    valid = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_TRUE(txn_accepted);

    valid = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_FALSE(txn_accepted);
  endtask

  task automatic test_backpressure();
    valid = 1'b0;
    ready = 1'b0;

    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_FALSE(txn_accepted);

    valid = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_FALSE(txn_accepted);

    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_TRUE(txn_stalled);
    `CHECK_FALSE(txn_accepted);

    ready = 1'b1;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_TRUE(txn_accepted);

    valid = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_accepted);
  endtask

  task automatic test_valid_ready_same_cycle();
    valid = 1'b0;
    ready = 1'b0;

    `TICK(clk);

    valid = 1'b1;
    ready = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(txn_started);
    `CHECK_TRUE(txn_accepted);

    valid = 1'b0;
    ready = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_accepted);
  endtask

  task automatic test_multiple_transactions();
    valid = 1'b0;
    ready = 1'b1;

    `TICK(clk);

    valid = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(txn_started);
    `CHECK_TRUE(txn_accepted);

    valid = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_accepted);

    valid = 1'b1;
    `TICK(clk);
    `CHECK_TRUE(txn_started);
    `CHECK_TRUE(txn_accepted);

    valid = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_accepted);
  endtask

  task automatic test_stalled_signal();
    valid = 1'b1;
    ready = 1'b0;

    `TICK(clk);
    `CHECK_TRUE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_FALSE(txn_accepted);

    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_TRUE(txn_stalled);
    `CHECK_FALSE(txn_accepted);

    // Multiple cycles of stall
    repeat (3) begin
      `TICK(clk);
      `CHECK_FALSE(txn_started);
      `CHECK_TRUE(txn_stalled);
      `CHECK_FALSE(txn_accepted);
    end

    ready = 1'b1;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_TRUE(txn_accepted);

    valid = 1'b0;
    ready = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(txn_started);
    `CHECK_FALSE(txn_stalled);
    `CHECK_FALSE(txn_accepted);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_detect_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_handshake);
  `TEST_CASE(test_backpressure);
  `TEST_CASE(test_valid_ready_same_cycle);
  `TEST_CASE(test_multiple_transactions);
  `TEST_CASE(test_stalled_signal);
  `TEST_SUITE_END();
endmodule
