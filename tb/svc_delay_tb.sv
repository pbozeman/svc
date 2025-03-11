`include "svc_unit.sv"
`include "svc_delay.sv"

module svc_delay_tb;
  // Clock and reset generation
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // Test parameters
  parameter WIDTH = 8;
  parameter CYCLES = 3;

  // Testbench signals
  logic [WIDTH-1:0] in;
  logic [WIDTH-1:0] out;

  svc_delay #(
      .CYCLES(CYCLES),
      .WIDTH (WIDTH)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),
      .in   (in),
      .out  (out)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      in <= 8'h00;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(out, 8'h00);
  endtask

  task automatic test_basic_delay();
    // First input after reset
    in = 8'hA5;
    `TICK(clk);
    `CHECK_EQ(out, 8'h00);

    `TICK(clk);
    `CHECK_EQ(out, 8'h00);

    `TICK(clk);
    `CHECK_EQ(out, 8'h00);

    `TICK(clk);
    `CHECK_EQ(out, 8'hA5);

    // Change input and verify delay persists
    in = 8'h3C;
    `TICK(clk);
    `CHECK_EQ(out, 8'hA5);

    `TICK(clk);
    `CHECK_EQ(out, 8'hA5);

    `TICK(clk);
    `CHECK_EQ(out, 8'hA5);

    `TICK(clk);
    `CHECK_EQ(out, 8'h3C);
  endtask

  task automatic test_continuous_flow();
    logic [WIDTH-1:0] test_data[10];

    // Initialize test data
    test_data[0] = 8'h01;
    test_data[1] = 8'h02;
    test_data[2] = 8'h03;
    test_data[3] = 8'h04;
    test_data[4] = 8'h05;
    test_data[5] = 8'h06;
    test_data[6] = 8'h07;
    test_data[7] = 8'h08;
    test_data[8] = 8'h09;
    test_data[9] = 8'h0A;

    `CHECK_EQ(out, 8'h00);

    for (int i = 0; i < CYCLES + 1; i++) begin
      in = test_data[i];
      `TICK(clk);
    end

    for (int i = 0; i < 6; i++) begin
      `CHECK_EQ(out, test_data[i]);
      in = test_data[i+CYCLES+1];
      `TICK(clk);
    end
  endtask

  // Single cycle delay test signals
  logic [WIDTH-1:0] single_in;
  logic [WIDTH-1:0] single_out;

  // Instantiate a module with CYCLES=1
  svc_delay #(
      .CYCLES(1),
      .WIDTH (WIDTH)
  ) single_cycle_delay (
      .clk  (clk),
      .rst_n(rst_n),
      .in   (single_in),
      .out  (single_out)
  );

  task automatic test_single_cycle_delay();
    single_in = 8'h42;

    `TICK(clk);
    `CHECK_EQ(single_out, 8'h00);

    `TICK(clk);
    `CHECK_EQ(single_out, 8'h42);

    single_in = 8'h77;
    `TICK(clk);
    `CHECK_EQ(single_out, 8'h42);

    `TICK(clk);
    `CHECK_EQ(single_out, 8'h77);
  endtask

  `TEST_SUITE_BEGIN(svc_delay_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_delay);
  `TEST_CASE(test_continuous_flow);
  `TEST_CASE(test_single_cycle_delay);
  `TEST_SUITE_END();
endmodule
