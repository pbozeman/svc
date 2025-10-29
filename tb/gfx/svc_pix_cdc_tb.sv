`include "svc_unit.sv"

`include "svc_pix_cdc.sv"

// ✨🤖✨ basic smoke test vibe coded with claude

module svc_pix_cdc_tb;
  localparam H_WIDTH = 12;
  localparam V_WIDTH = 12;
  localparam COLOR_WIDTH = 4;
  localparam FIFO_ADDR_WIDTH = 3;

  // Create system clock for source domain
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // Create pixel clock for destination domain (slower)
  `TEST_CLK_NS(pixel_clk, 20);

  // Source side signals
  logic                   s_pix_valid;
  logic [COLOR_WIDTH-1:0] s_pix_red;
  logic [COLOR_WIDTH-1:0] s_pix_grn;
  logic [COLOR_WIDTH-1:0] s_pix_blu;
  logic [    H_WIDTH-1:0] s_pix_x;
  logic [    V_WIDTH-1:0] s_pix_y;
  logic                   s_pix_ready;

  // Destination side signals
  logic                   m_pix_valid;
  logic [COLOR_WIDTH-1:0] m_pix_red;
  logic [COLOR_WIDTH-1:0] m_pix_grn;
  logic [COLOR_WIDTH-1:0] m_pix_blu;
  logic [    H_WIDTH-1:0] m_pix_x;
  logic [    V_WIDTH-1:0] m_pix_y;
  logic                   m_pix_ready;

  // Unit under test
  svc_pix_cdc #(
      .H_WIDTH        (H_WIDTH),
      .V_WIDTH        (V_WIDTH),
      .COLOR_WIDTH    (COLOR_WIDTH),
      .FIFO_ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) uut (
      .s_clk      (clk),
      .s_rst_n    (rst_n),
      .s_pix_valid(s_pix_valid),
      .s_pix_red  (s_pix_red),
      .s_pix_grn  (s_pix_grn),
      .s_pix_blu  (s_pix_blu),
      .s_pix_x    (s_pix_x),
      .s_pix_y    (s_pix_y),
      .s_pix_ready(s_pix_ready),

      .m_clk      (pixel_clk),
      .m_rst_n    (rst_n),
      .m_pix_valid(m_pix_valid),
      .m_pix_red  (m_pix_red),
      .m_pix_grn  (m_pix_grn),
      .m_pix_blu  (m_pix_blu),
      .m_pix_x    (m_pix_x),
      .m_pix_y    (m_pix_y),
      .m_pix_ready(m_pix_ready)
  );

  // Test reset state
  task automatic test_reset;
    // Initialize inputs
    s_pix_valid = 1'b0;
    s_pix_red   = '0;
    s_pix_grn   = '0;
    s_pix_blu   = '0;
    s_pix_x     = '0;
    s_pix_y     = '0;
    m_pix_ready = 1'b0;

    // Wait for a few clock cycles after reset
    `TICK(clk);
    `TICK(clk);

    // Check outputs
    `CHECK_FALSE(m_pix_valid);
    `CHECK_TRUE(s_pix_ready);
  endtask

  // Test basic data transfer - simplified smoke test
  task automatic test_basic_transfer;
    // Test values
    logic [COLOR_WIDTH-1:0] test_red = 4'hA;
    logic [COLOR_WIDTH-1:0] test_grn = 4'h5;
    logic [COLOR_WIDTH-1:0] test_blu = 4'hF;
    logic [    H_WIDTH-1:0] test_x = 123;
    logic [    V_WIDTH-1:0] test_y = 456;

    // Allow reads from CDC FIFO
    m_pix_ready = 1'b1;

    // Send data
    s_pix_valid = 1'b1;
    s_pix_red   = test_red;
    s_pix_grn   = test_grn;
    s_pix_blu   = test_blu;
    s_pix_x     = test_x;
    s_pix_y     = test_y;

    `TICK(clk);

    // Ensure data was accepted
    `CHECK_TRUE(s_pix_ready);

    // Wait for data to be transferred across clock domains
    // This might take a few cycles due to CDC synchronization
    `CHECK_WAIT_FOR(pixel_clk, m_pix_valid, 10);

    // Check that data made it across correctly - smoke test success!
    `CHECK_TRUE(m_pix_valid);
    `CHECK_EQ(m_pix_red, test_red);
    `CHECK_EQ(m_pix_grn, test_grn);
    `CHECK_EQ(m_pix_blu, test_blu);
    `CHECK_EQ(m_pix_x, test_x);
    `CHECK_EQ(m_pix_y, test_y);

    // For a smoke test, we won't verify the emptying behavior
    // since that's more complicated and would be in a more advanced test
  endtask

  `TEST_SUITE_BEGIN(svc_pix_cdc_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_basic_transfer);
  `TEST_SUITE_END();

endmodule
