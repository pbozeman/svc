`include "svc_unit.sv"
`include "svc_uart_tx.sv"

module svc_uart_tx_tb;
  localparam CLOCK_FREQ = 10_000_000;
  localparam BAUD_RATE = 1_000_000;
  localparam CLOCKS_PER_BIT = CLOCK_FREQ / BAUD_RATE;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic       utx_en;
  logic [7:0] utx_data;
  logic       utx_busy;
  logic       utx_pin;

  svc_uart_tx #(
      .CLOCK_FREQ(CLOCK_FREQ),
      .BAUD_RATE (BAUD_RATE)
  ) uut (
      .clk     (clk),
      .rst_n   (rst_n),
      .utx_en  (utx_en),
      .utx_data(utx_data),
      .utx_busy(utx_busy),
      .utx_pin (utx_pin)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      utx_en   <= 1'b0;
      utx_data <= 8'h00;
    end
  end

  // Wait for a full bit period
  task automatic wait_bit();
    repeat (CLOCKS_PER_BIT) `TICK(clk);
  endtask

  task automatic send_and_verify_char(input logic [7:0] data);
    // Start the transmission
    utx_en   = 1'b1;
    utx_data = data;

    `TICK(clk);
    utx_en = 1'b0;

    // Check busy signal
    `CHECK_TRUE(utx_busy);

    // Check start bit
    `CHECK_EQ(utx_pin, 1'b0);
    wait_bit();

    // Check all data bits
    for (int i = 0; i < 8; i++) begin
      `CHECK_EQ(utx_pin, data[i]);
      wait_bit();
    end

    // Check stop bit
    `CHECK_EQ(utx_pin, 1'b1);
    ;
    wait_bit();

    // Check transmission complete
    `CHECK_FALSE(utx_busy);
    `CHECK_EQ(utx_pin, 1'b1);
    ;
  endtask

  task automatic test_reset();
    `CHECK_FALSE(utx_busy);
    `CHECK_EQ(utx_pin, 1'b1);
    ;
  endtask

  task automatic test_basic_transmission();
    send_and_verify_char(8'h55);
  endtask

  task automatic test_consecutive_transmission();
    send_and_verify_char(8'hAA);
    send_and_verify_char(8'h00);
    send_and_verify_char(8'hFF);
    send_and_verify_char(8'h01);
  endtask

  task automatic test_backpressure();
    utx_en   = 1'b1;
    utx_data = 8'h33;
    `TICK(clk);

    // Try to start another transmission while busy
    utx_en   = 1'b1;
    utx_data = 8'hCC;
    `TICK(clk);
    utx_en = 1'b0;

    // Verify the UART is still sending the first byte
    `CHECK_TRUE(utx_busy);

    // Wait for transmission to complete
    while (utx_busy) begin
      `TICK(clk);
    end

    // Verify idle state after completion
    `CHECK_FALSE(utx_busy);
    `CHECK_EQ(utx_pin, 1'b1);
    ;

    // Send another byte to ensure the UART still works after backpressure
    send_and_verify_char(8'h78);
  endtask

  // Test various bit patterns
  task automatic test_bit_patterns();
    // Single bits at different positions
    send_and_verify_char(8'h01);
    send_and_verify_char(8'h02);
    send_and_verify_char(8'h04);
    send_and_verify_char(8'h08);
    send_and_verify_char(8'h10);
    send_and_verify_char(8'h20);
    send_and_verify_char(8'h40);
    send_and_verify_char(8'h80);

    // Common ASCII characters
    // A, Z, a, z, space
    send_and_verify_char(8'h41);
    send_and_verify_char(8'h5A);
    send_and_verify_char(8'h61);
    send_and_verify_char(8'h7A);
    send_and_verify_char(8'h20);
  endtask

  `TEST_SUITE_BEGIN(svc_uart_tx_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_transmission);
  `TEST_CASE(test_consecutive_transmission);
  `TEST_CASE(test_backpressure);
  `TEST_CASE(test_bit_patterns);
  `TEST_SUITE_END();

endmodule
