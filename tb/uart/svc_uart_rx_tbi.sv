`include "svc_unit.sv"
`include "svc_uart_rx.sv"

module svc_uart_rx_tbi;
  localparam CLOCK_FREQ = 10_000_000;
  localparam BAUD_RATE = 1_000_000;
  localparam CLOCKS_PER_BIT = CLOCK_FREQ / BAUD_RATE;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic       urx_valid;
  logic [7:0] urx_data;
  logic       urx_ready;
  logic       urx_pin;
  logic [7:0] urx_valid_cnt;
  logic [7:0] urx_data_recv;

  svc_uart_rx #(
      .CLOCK_FREQ(CLOCK_FREQ),
      .BAUD_RATE (BAUD_RATE)
  ) uut (
      .clk      (clk),
      .rst_n    (rst_n),
      .urx_valid(urx_valid),
      .urx_data (urx_data),
      .urx_ready(urx_ready),
      .urx_pin  (urx_pin)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      urx_valid_cnt <= 0;
      urx_pin       <= 1'b1;
      urx_ready     <= 1'b1;
    end else begin
      if (urx_valid && urx_ready) begin
        urx_valid_cnt <= urx_valid_cnt + 1;
        urx_data_recv <= urx_data;
      end
    end
  end

  // Wait for a full bit period
  task automatic wait_bit();
    repeat (CLOCKS_PER_BIT) `TICK(clk);
  endtask

  task automatic wait_half_bit();
    repeat (CLOCKS_PER_BIT / 2) `TICK(clk);
  endtask

  task automatic send_uart_char(input logic [7:0] data);
    urx_pin = 1'b0;
    wait_bit();
    for (int i = 0; i < 8; i++) begin
      urx_pin = data[i];
      wait_bit();
    end
    urx_pin = 1'b1;
    wait_bit();
  endtask

  task automatic receive_and_verify_char(input logic [7:0] data);
    send_uart_char(data);
    `CHECK_EQ(urx_data_recv, data);
  endtask

  task automatic test_reset();
    `CHECK_FALSE(urx_valid);
  endtask

  task automatic test_basic_reception();
    receive_and_verify_char(8'h55);
    repeat (1000) `TICK(clk);
    `CHECK_EQ(urx_valid_cnt, 1);
  endtask

  task automatic test_consecutive_reception();
    receive_and_verify_char(8'hAA);
    receive_and_verify_char(8'h00);
    receive_and_verify_char(8'hFF);
    receive_and_verify_char(8'h01);
    repeat (1000) `TICK(clk);
    `CHECK_EQ(urx_valid_cnt, 4);
  endtask

  task automatic test_bit_patterns();
    // Single bits at different positions
    receive_and_verify_char(8'h01);
    receive_and_verify_char(8'h02);
    receive_and_verify_char(8'h04);
    receive_and_verify_char(8'h08);
    receive_and_verify_char(8'h10);
    receive_and_verify_char(8'h20);
    receive_and_verify_char(8'h40);
    receive_and_verify_char(8'h80);
    // Common ASCII characters
    // A, Z, a, z, space
    receive_and_verify_char(8'h41);
    receive_and_verify_char(8'h5A);
    receive_and_verify_char(8'h61);
    receive_and_verify_char(8'h7A);
    receive_and_verify_char(8'h20);
    repeat (1000) `TICK(clk);
    `CHECK_EQ(urx_valid_cnt, 13);
  endtask

  task automatic test_false_start_bit();
    // Create a false start bit (goes low then high before half bit time)
    urx_pin = 1'b0;
    repeat (CLOCKS_PER_BIT / 4) `TICK(clk);
    urx_pin = 1'b1;
    // Wait a full bit period to check no data is received
    wait_bit();
    wait_bit();
    // Verify no data was received
    `CHECK_EQ(urx_valid_cnt, 0);
    // Now send a valid character to ensure RX still works
    receive_and_verify_char(8'h42);
    `CHECK_EQ(urx_valid_cnt, 1);
  endtask

  task automatic test_bad_stop_bit();
    urx_pin = 1'b0;
    wait_bit();
    // Data bits (all 1's for testing)
    for (int i = 0; i < 8; i++) begin
      urx_pin = 1'b1;
      wait_bit();
    end
    // Bad stop bit (should be high but we send low)
    urx_pin = 1'b0;
    wait_bit();
    // Return to idle
    urx_pin = 1'b1;
    wait_bit();
    // Verify no data was received due to bad stop bit
    `CHECK_EQ(urx_valid_cnt, 0);
    // Now send a valid character to ensure RX still works
    receive_and_verify_char(8'h42);
    `CHECK_EQ(urx_valid_cnt, 1);
  endtask

  task automatic test_backpressure();
    // Set ready to 0 to apply backpressure
    urx_ready = 1'b0;

    // Send a character while backpressure is applied
    send_uart_char(8'h5A);

    // Wait some cycles to verify data is held
    repeat (100) `TICK(clk);

    // Verify no new data was accepted due to backpressure
    `CHECK_EQ(urx_valid_cnt, 0);
    `CHECK_TRUE(urx_valid);

    // Release backpressure
    urx_ready = 1'b1;
    `TICK(clk);

    // Verify data was received after backpressure release
    `CHECK_EQ(urx_valid_cnt, 1);
    `CHECK_EQ(urx_data_recv, 8'h5A);

    // Verify can receive new data after backpressure is released
    receive_and_verify_char(8'h3C);
    `CHECK_EQ(urx_valid_cnt, 2);
  endtask

  `TEST_SUITE_BEGIN(svc_uart_rx_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_reception);
  `TEST_CASE(test_consecutive_reception);
  `TEST_CASE(test_bit_patterns);
  `TEST_CASE(test_false_start_bit);
  `TEST_CASE(test_bad_stop_bit);
  `TEST_CASE(test_backpressure);
  `TEST_SUITE_END();
endmodule
