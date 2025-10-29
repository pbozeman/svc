`include "svc_unit.sv"
`include "svc_gfx_rect_fill.sv"

// ✨🤖✨ vibe coded with claude

module svc_gfx_rect_fill_tb;
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
  svc_gfx_rect_fill #(
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

  // Helper function to count rectangular area pixels
  function automatic int count_rect_pixels(input int x0_in, input int y0_in,
                                           input int x1_in, input int y1_in);
    int x_min, x_max, y_min, y_max;

    // Ensure x_min <= x_max and y_min <= y_max
    x_min = (x0_in <= x1_in) ? x0_in : x1_in;
    x_max = (x0_in <= x1_in) ? x1_in : x0_in;
    y_min = (y0_in <= y1_in) ? y0_in : y1_in;
    y_max = (y0_in <= y1_in) ? y1_in : y0_in;

    // Calculate area
    return (x_max - x_min + 1) * (y_max - y_min + 1);
  endfunction

  // Helper function to verify rectangle pixels
  function automatic int verify_rectangular_area(
      input int x0_in, input int y0_in, input int x1_in, input int y1_in,
      input logic [PIXEL_WIDTH-1:0] expected_color);
    int count = 0;
    int x_min, x_max, y_min, y_max;

    // Ensure x_min <= x_max and y_min <= y_max
    x_min = (x0_in <= x1_in) ? x0_in : x1_in;
    x_max = (x0_in <= x1_in) ? x1_in : x0_in;
    y_min = (y0_in <= y1_in) ? y0_in : y1_in;
    y_max = (y0_in <= y1_in) ? y1_in : y0_in;

    for (int y = y_min; y <= y_max; y++) begin
      for (int x = x_min; x <= x_max; x++) begin
        if (framebuffer[x][y] == expected_color) begin
          count++;
        end
      end
    end

    return count;
  endfunction

  // Test reset behavior
  task automatic test_reset;
    `CHECK_FALSE(m_gfx_valid);
    `CHECK_FALSE(done);
  endtask

  // Test clearing a small square area
  task automatic test_small_square;
    int actual_count;

    // Clear a 10x10 area
    x0 = 5;
    y0 = 5;
    x1 = 14;
    y1 = 14;
    color = 12'hABC;

    expected_pixels = count_rect_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for operation to complete with timeout
    `CHECK_WAIT_FOR(clk, done, 1000);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Verify rectangle area
    actual_count =
        verify_rectangular_area(int'(x0), int'(y0), int'(x1), int'(y1), color);
    `CHECK_EQ(actual_count, expected_pixels);

    // Check corners and middle
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);
    `CHECK_EQ(framebuffer[x1][y0], color);
    `CHECK_EQ(framebuffer[x0][y1], color);
    `CHECK_EQ(framebuffer[(x0+x1)/2][(y0+y1)/2], color);
  endtask

  // Test inverted coordinates
  task automatic test_inverted_coordinates;
    int actual_count;

    // Inverted coordinates (x1 < x0, y1 < y0)
    x0 = 20;
    y0 = 25;
    x1 = 10;
    y1 = 15;
    color = 12'h123;

    expected_pixels = count_rect_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for operation to complete with timeout
    `CHECK_WAIT_FOR(clk, done, 1000);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Verify rectangle area
    actual_count =
        verify_rectangular_area(int'(x0), int'(y0), int'(x1), int'(y1), color);
    `CHECK_EQ(actual_count, expected_pixels);

    // Check corners
    `CHECK_EQ(framebuffer[10][15], color);
    `CHECK_EQ(framebuffer[20][25], color);
  endtask

  // Test drawing a single pixel
  task automatic test_single_pixel;
    int actual_count;

    // Single pixel
    x0              = 30;
    y0              = 30;
    x1              = 30;
    y1              = 30;
    color           = 12'h456;

    expected_pixels = 1;
    received_pixels = 0;

    // Start drawing
    start           = 1;
    `TICK(clk);
    start = 0;

    // Wait for operation to complete
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Verify the pixel
    actual_count =
        verify_rectangular_area(int'(x0), int'(y0), int'(x1), int'(y1), color);
    `CHECK_EQ(actual_count, expected_pixels);

    // Check pixel
    `CHECK_EQ(framebuffer[30][30], color);

    // Check adjacent pixels weren't drawn
    `CHECK_NEQ(framebuffer[29][30], color);
    `CHECK_NEQ(framebuffer[31][30], color);
    `CHECK_NEQ(framebuffer[30][29], color);
    `CHECK_NEQ(framebuffer[30][31], color);
  endtask

  // Test drawing a horizontal line
  task automatic test_horizontal_line;
    int actual_count;

    // Horizontal line
    x0 = 5;
    y0 = 40;
    x1 = 45;
    y1 = 40;
    color = 12'h789;

    expected_pixels = count_rect_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for operation to complete
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Verify line area
    actual_count =
        verify_rectangular_area(int'(x0), int'(y0), int'(x1), int'(y1), color);
    `CHECK_EQ(actual_count, expected_pixels);

    // Check endpoints
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);

    // Check middle point
    `CHECK_EQ(framebuffer[(x0+x1)/2][y0], color);

    // Check pixels above and below weren't drawn
    `CHECK_NEQ(framebuffer[(x0+x1)/2][y0-1], color);
    `CHECK_NEQ(framebuffer[(x0+x1)/2][y0+1], color);
  endtask

  // Test drawing a vertical line
  task automatic test_vertical_line;
    int actual_count;

    // Vertical line
    x0 = 50;
    y0 = 10;
    x1 = 50;
    y1 = 30;
    color = 12'hDEF;

    expected_pixels = count_rect_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start drawing
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait for operation to complete
    `CHECK_WAIT_FOR(clk, done, 100);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Verify line area
    actual_count =
        verify_rectangular_area(int'(x0), int'(y0), int'(x1), int'(y1), color);
    `CHECK_EQ(actual_count, expected_pixels);

    // Check endpoints
    `CHECK_EQ(framebuffer[x0][y0], color);
    `CHECK_EQ(framebuffer[x1][y1], color);

    // Check middle point
    `CHECK_EQ(framebuffer[x0][(y0+y1)/2], color);

    // Check pixels to left and right weren't drawn
    `CHECK_NEQ(framebuffer[x0-1][(y0+y1)/2], color);
    `CHECK_NEQ(framebuffer[x0+1][(y0+y1)/2], color);
  endtask

  // Test with backpressure
  task automatic test_with_backpressure;
    int actual_count;

    // Tiny area with backpressure (just 3x3 = 9 pixels)
    x0 = 60;
    y0 = 60;
    x1 = 62;
    y1 = 62;
    color = 12'h555;

    expected_pixels = count_rect_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start with backpressure
    m_gfx_ready = 0;
    start = 1;
    `TICK(clk);
    start = 0;

    // Module should wait with m_gfx_valid high
    repeat (3) `TICK(clk);
    `CHECK_TRUE(m_gfx_valid);
    `CHECK_FALSE(done);

    // Enable ready to accept pixels, but toggle it to create backpressure
    repeat (expected_pixels * 2) begin
      m_gfx_ready = !m_gfx_ready;
      `TICK(clk);
    end

    // Ensure ready at the end to complete the operation
    m_gfx_ready = 1;

    // Wait for much longer than the line test
    `CHECK_WAIT_FOR(clk, done, 10000);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Verify rectangle area
    actual_count =
        verify_rectangular_area(int'(x0), int'(y0), int'(x1), int'(y1), color);
    `CHECK_EQ(actual_count, expected_pixels);
  endtask

  // Test signal stability during backpressure
  task automatic test_signal_stability;
    int                     actual_count;
    logic [    H_WIDTH-1:0] stable_x;
    logic [    V_WIDTH-1:0] stable_y;
    logic [PIXEL_WIDTH-1:0] stable_pixel;

    // Small area for testing (2x2 = 4 pixels)
    x0 = 70;
    y0 = 70;
    x1 = 71;
    y1 = 71;
    color = 12'hA5A;

    expected_pixels = count_rect_pixels(int'(x0), int'(y0), int'(x1), int'(y1));
    received_pixels = 0;

    // Start operation
    start = 1;
    `TICK(clk);
    start = 0;

    // Wait until we see valid asserted
    repeat (5) begin
      if (!m_gfx_valid) `TICK(clk);
    end

    // Ensure valid is high
    `CHECK_TRUE(m_gfx_valid);

    // Store current output values
    stable_x     = m_gfx_x;
    stable_y     = m_gfx_y;
    stable_pixel = m_gfx_pixel;

    // Apply backpressure
    m_gfx_ready  = 0;

    // Check stability over multiple cycles
    repeat (5) begin
      `TICK(clk);
      `CHECK_TRUE(m_gfx_valid);
      `CHECK_EQ(m_gfx_x, stable_x);
      `CHECK_EQ(m_gfx_y, stable_y);
      `CHECK_EQ(m_gfx_pixel, stable_pixel);
    end

    // Release backpressure to complete the operation
    m_gfx_ready = 1;

    // Wait for operation to complete
    `CHECK_WAIT_FOR(clk, done, 1000);

    // Check pixel count
    `CHECK_EQ(received_pixels, expected_pixels);

    // Verify rectangle area
    actual_count =
        verify_rectangular_area(int'(x0), int'(y0), int'(x1), int'(y1), color);
    `CHECK_EQ(actual_count, expected_pixels);
  endtask

  `TEST_SUITE_BEGIN(svc_gfx_rect_fill_tb);

  `TEST_SETUP(setup);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_small_square);
  `TEST_CASE(test_inverted_coordinates);
  `TEST_CASE(test_single_pixel);
  `TEST_CASE(test_horizontal_line);
  `TEST_CASE(test_vertical_line);
  `TEST_CASE(test_with_backpressure);
  `TEST_CASE(test_signal_stability);

  `TEST_SUITE_END();

endmodule
