`include "svc_unit.sv"

`include "svc_rv_pipe_data.sv"

module svc_rv_pipe_data_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int WIDTH = 8;

  //
  // Test signals for default configuration (*_REG=0)
  //
  logic             advance;
  logic             flush;
  logic             bubble;
  logic [WIDTH-1:0] data_i;
  logic [WIDTH-1:0] data_o;

  svc_rv_pipe_data #(
      .WIDTH     (WIDTH),
      .REG       (1),
      .RESET_REG (0),
      .RESET_VAL (8'hAA),
      .FLUSH_REG (0),
      .FLUSH_VAL (8'hBB),
      .BUBBLE_REG(0),
      .BUBBLE_VAL(8'hCC)
  ) uut (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (flush),
      .bubble (bubble),
      .data_i (data_i),
      .data_o (data_o)
  );

  //
  // Test signals for *_REG=1 configuration
  //
  logic [WIDTH-1:0] data_o_reg;

  svc_rv_pipe_data #(
      .WIDTH     (WIDTH),
      .REG       (1),
      .RESET_REG (1),
      .RESET_VAL (8'h00),
      .FLUSH_REG (1),
      .FLUSH_VAL (8'h00),
      .BUBBLE_REG(1),
      .BUBBLE_VAL(8'h00)
  ) uut_reg (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (flush),
      .bubble (bubble),
      .data_i (data_i),
      .data_o (data_o_reg)
  );

  //
  // Test signals for passthrough configuration (REG=0)
  //
  logic [WIDTH-1:0] data_o_pt;

  svc_rv_pipe_data #(
      .WIDTH(WIDTH),
      .REG  (0)
  ) uut_passthrough (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(advance),
      .flush  (flush),
      .bubble (bubble),
      .data_i (data_i),
      .data_o (data_o_pt)
  );

  //
  // Initialize signals in reset
  //
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      advance <= 1'b0;
      flush   <= 1'b0;
      bubble  <= 1'b0;
      data_i  <= '0;
    end
  end

  //
  // Test: Reset sets data to RESET_VAL (RESET_REG=0)
  //
  task automatic test_reset();
    `CHECK_EQ(data_o, 8'hAA);
  endtask

  //
  // Test: Reset with RESET_REG=1 loads data_i
  //
  task automatic test_reset_reg();
    //
    // Note: data_i is 0 after reset, so data_o_reg should be 0
    //
    `CHECK_EQ(data_o_reg, 8'h00);
  endtask

  //
  // Test: advance=1 loads data_i
  //
  task automatic test_advance();
    advance = 1'b1;
    flush   = 1'b0;
    bubble  = 1'b0;
    data_i  = 8'h42;
    `TICK(clk);

    `CHECK_EQ(data_o, 8'h42);

    //
    // Advance with different data
    //
    data_i = 8'h55;
    `TICK(clk);
    `CHECK_EQ(data_o, 8'h55);
  endtask

  //
  // Test: No control signals retains previous data (hold)
  //
  task automatic test_hold();
    //
    // First advance some data
    //
    advance = 1'b1;
    data_i  = 8'h77;
    `TICK(clk);
    `CHECK_EQ(data_o, 8'h77);

    //
    // Now hold (no control signals active)
    //
    advance = 1'b0;
    flush   = 1'b0;
    bubble  = 1'b0;
    data_i  = 8'hEE;
    `TICK(clk);

    //
    // Should retain previous value
    //
    `CHECK_EQ(data_o, 8'h77);

    //
    // Hold for multiple cycles
    //
    repeat (3) `TICK(clk);
    `CHECK_EQ(data_o, 8'h77);
  endtask

  //
  // Test: flush=1 sets data to FLUSH_VAL
  //
  task automatic test_flush();
    //
    // First advance some data
    //
    advance = 1'b1;
    flush   = 1'b0;
    data_i  = 8'h33;
    `TICK(clk);

    //
    // Flush
    //
    advance = 1'b0;
    flush   = 1'b1;
    data_i  = 8'hDD;
    `TICK(clk);

    `CHECK_EQ(data_o, 8'hBB);

    flush = 1'b0;
  endtask

  //
  // Test: flush=1 with FLUSH_REG=1 loads data_i
  //
  task automatic test_flush_reg();
    //
    // First advance some data
    //
    advance = 1'b1;
    flush   = 1'b0;
    data_i  = 8'h33;
    `TICK(clk);

    //
    // Flush with specific data_i
    //
    advance = 1'b0;
    flush   = 1'b1;
    data_i  = 8'hEE;
    `TICK(clk);

    `CHECK_EQ(data_o_reg, 8'hEE);

    flush = 1'b0;
  endtask

  //
  // Test: bubble=1 sets data to BUBBLE_VAL
  //
  task automatic test_bubble();
    //
    // First advance some data
    //
    advance = 1'b1;
    bubble  = 1'b0;
    data_i  = 8'h44;
    `TICK(clk);

    //
    // Bubble
    //
    advance = 1'b0;
    bubble  = 1'b1;
    data_i  = 8'hFF;
    `TICK(clk);

    `CHECK_EQ(data_o, 8'hCC);

    bubble = 1'b0;
  endtask

  //
  // Test: bubble=1 with BUBBLE_REG=1 loads data_i
  //
  task automatic test_bubble_reg();
    //
    // First advance some data
    //
    advance = 1'b1;
    bubble  = 1'b0;
    data_i  = 8'h44;
    `TICK(clk);

    //
    // Bubble with specific data_i
    //
    advance = 1'b0;
    bubble  = 1'b1;
    data_i  = 8'hAB;
    `TICK(clk);

    `CHECK_EQ(data_o_reg, 8'hAB);

    bubble = 1'b0;
  endtask

  //
  // Test: Passthrough directly connects data_i to data_o
  //
  task automatic test_passthrough();
    //
    // Passthrough should directly connect in to out
    //
    data_i = 8'h12;
    `TICK(clk);
    `CHECK_EQ(data_o_pt, 8'h12);

    //
    // Change input immediately affects output
    //
    data_i = 8'h34;
    `TICK(clk);
    `CHECK_EQ(data_o_pt, 8'h34);

    //
    // Control signals should have no effect
    //
    data_i = 8'h56;
    flush  = 1'b1;
    `TICK(clk);
    `CHECK_EQ(data_o_pt, 8'h56);

    flush = 1'b0;
  endtask

  //
  // Test: Back-to-back advances
  //
  task automatic test_back_to_back();
    advance = 1'b1;

    data_i  = 8'h01;
    `TICK(clk);
    `CHECK_EQ(data_o, 8'h01);

    data_i = 8'h02;
    `TICK(clk);
    `CHECK_EQ(data_o, 8'h02);

    data_i = 8'h03;
    `TICK(clk);
    `CHECK_EQ(data_o, 8'h03);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_pipe_data_tbi);

  `TEST_CASE(test_reset);
  `TEST_CASE(test_reset_reg);
  `TEST_CASE(test_advance);
  `TEST_CASE(test_hold);
  `TEST_CASE(test_flush);
  `TEST_CASE(test_flush_reg);
  `TEST_CASE(test_bubble);
  `TEST_CASE(test_bubble_reg);
  `TEST_CASE(test_passthrough);
  `TEST_CASE(test_back_to_back);

  `TEST_SUITE_END();

endmodule
