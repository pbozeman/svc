`include "svc_unit.sv"
`include "svc_gfx_line.sv"

// ✨🤖✨ vibe coded with claude
//
// It needed a lot of fixes :/

module svc_gfx_line_tb;
  parameter H_WIDTH = 8;
  parameter V_WIDTH = 8;
  parameter PIXEL_WIDTH = 12;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // Control interface
  logic                   start;
  logic                   done;
  logic [    H_WIDTH-1:0] x0;
  logic [    V_WIDTH-1:0] y0;
  logic [    H_WIDTH-1:0] x1;
  logic [    V_WIDTH-1:0] y1;
  logic [PIXEL_WIDTH-1:0] color;

  // Graphics output interface
  logic                   m_gfx_valid;
  logic [    H_WIDTH-1:0] m_gfx_x;
  logic [    V_WIDTH-1:0] m_gfx_y;
  logic [PIXEL_WIDTH-1:0] m_gfx_pixel;
  logic                   m_gfx_ready;

  // Frame buffer for testing
  logic [PIXEL_WIDTH-1:0] framebuffer     [256][256];

  // Pixel counts for validation
  int                     expected_pixels;
  int                     received_pixels;

  // Device under test
  svc_gfx_line #(
      .H_WIDTH    (H_WIDTH),
      .V_WIDTH    (V_WIDTH),
      .PIXEL_WIDTH(PIXEL_WIDTH)
  ) uut (
      .clk        (clk),
      .rst_n      (rst_n),
      .start      (start),
      .done       (done),
      .x0         (x0),
      .y0         (y0),
      .x1         (x1),
      .y1         (y1),
      .color      (color),
      .m_gfx_valid(m_gfx_valid),
      .m_gfx_x    (m_gfx_x),
      .m_gfx_y    (m_gfx_y),
      .m_gfx_pixel(m_gfx_pixel),
      .m_gfx_ready(m_gfx_ready)
  );

  // Setup task - initialize signals
  task automatic setup;
    start       = 0;
    x0          = 0;
    y0          = 0;
    x1          = 0;
    y1          = 0;
    color       = 0;
    m_gfx_ready = 1;

    // Clear framebuffer
    for (int i = 0; i < 256; i++) begin
      for (int j = 0; j < 256; j++) begin
        framebuffer[i][j] = 0;
      end
    end

    expected_pixels = 0;
    received_pixels = 0;
  endtask

  // Process pixel output from DUT
  always_ff @(posedge clk) begin
    if (m_gfx_valid && m_gfx_ready) begin
      framebuffer[m_gfx_x][m_gfx_y] <= m_gfx_pixel;
      received_pixels               <= received_pixels + 1;
    end
  end

  // Helper function to count pixels in a straight line
  function automatic int count_line_pixels(input int x0_in, input int y0_in,
                                           input int x1_in, input int y1_in);
    int dx, dy, steps;

    dx    = (x1_in > x0_in) ? (x1_in - x0_in) : (x0_in - x1_in);
    dy    = (y1_in > y0_in) ? (y1_in - y0_in) : (y0_in - y1_in);

    // Bresenham needs 1 + max(dx, dy) pixels
    steps = 1 + ((dx > dy) ? dx : dy);
    return steps;
  endfunction

  // Test reset behavior
  task automatic test_reset;
    `CHECK_FALSE(m_gfx_valid);
  endtask

  // Test drawing a horizontal line
  task automatic test_horizontal_line;
    // Draw a horizontal line from (2,5) to (10,5)
    x0 = 2;
    y0 = 5;
    x1 = 10;
    y1 = 5;
    // Red color
    color = 12'hF00;
    expected_pixels = count_line_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for line to complete with timeout
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Check line endpoints
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);

    // Check a few points along the line
    `CHECK_EQ(framebuffer[4][5], color);
    `CHECK_EQ(framebuffer[7][5], color);

    // Make sure adjacent pixels weren't drawn
    `CHECK_NEQ(framebuffer[2][4], color);
    `CHECK_NEQ(framebuffer[10][6], color);
  endtask

  // Test drawing a vertical line
  task automatic test_vertical_line;
    // Draw a vertical line from (5,2) to (5,10)
    x0 = 5;
    y0 = 2;
    x1 = 5;
    y1 = 10;
    // Green color
    color = 12'h0F0;
    expected_pixels = count_line_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for line to complete with timeout
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Check line endpoints
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);

    // Check a few points along the line
    `CHECK_EQ(framebuffer[5][4], color);
    `CHECK_EQ(framebuffer[5][7], color);

    // Make sure adjacent pixels weren't drawn
    `CHECK_NEQ(framebuffer[4][5], color);
    `CHECK_NEQ(framebuffer[6][8], color);
  endtask

  // Test drawing a diagonal line
  task automatic test_diagonal_line;
    // Draw a diagonal line from (3,3) to (9,9)
    x0 = 3;
    y0 = 3;
    x1 = 9;
    y1 = 9;
    // Blue color
    color = 12'h00F;
    expected_pixels = count_line_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for line to complete with timeout
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Check line endpoints
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);

    // Check a few points along the line
    `CHECK_EQ(framebuffer[5][5], color);
    `CHECK_EQ(framebuffer[7][7], color);

    // Perfect diagonal should not have adjacent points
    `CHECK_NEQ(framebuffer[4][5], color);
    `CHECK_NEQ(framebuffer[8][7], color);
  endtask

  // Test drawing a steep line (more vertical than horizontal)
  task automatic test_steep_line;
    // Draw a steep line from (3,2) to (5,10)
    x0 = 3;
    y0 = 2;
    x1 = 5;
    y1 = 10;
    // Magenta color
    color = 12'hF0F;
    expected_pixels = count_line_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for line to complete with timeout
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Check line endpoints
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);

    // Check a point along the line
    `CHECK_EQ(framebuffer[4][6], color);
  endtask

  // Test with backpressure by toggling m_gfx_ready
  task automatic test_backpressure;
    // Draw a steep line from (3,2) to (5,10)
    x0 = 3;
    y0 = 2;
    x1 = 5;
    y1 = 10;
    // Magenta color
    color = 12'hF0F;
    expected_pixels = count_line_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    repeat (10) begin
      `TICK(clk);
      m_gfx_ready = !m_gfx_ready;
    end

    // Wait for line to complete with timeout
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Check line endpoints
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);

    // Check a point along the line
    `CHECK_EQ(framebuffer[4][6], color);
  endtask

  // Test drawing a single pixel (when x0,y0 = x1,y1)
  task automatic test_single_pixel;
    // Draw a single pixel at (7,7)
    x0              = 7;
    y0              = 7;
    x1              = 7;
    y1              = 7;
    // White color
    color           = 12'hFFF;
    expected_pixels = 1;
    received_pixels = 0;

    // Start drawing
    start           = 1;
    `TICK(clk);
    start = 0;

    // Wait for line to complete
    `CHECK_WAIT_FOR(clk, done, 10);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Check the pixel
    `CHECK_EQ(framebuffer[7][7], color);

    // Check adjacent pixels weren't drawn
    `CHECK_NEQ(framebuffer[6][7], color);
    `CHECK_NEQ(framebuffer[7][6], color);
    `CHECK_NEQ(framebuffer[8][7], color);
    `CHECK_NEQ(framebuffer[7][8], color);
  endtask

  `TEST_SUITE_BEGIN(svc_gfx_line_tb);

  `TEST_SETUP(setup);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_horizontal_line);
  `TEST_CASE(test_vertical_line);
  `TEST_CASE(test_diagonal_line);
  `TEST_CASE(test_steep_line);
  `TEST_CASE(test_backpressure);
  `TEST_CASE(test_single_pixel);

  `TEST_SUITE_END();

endmodule
