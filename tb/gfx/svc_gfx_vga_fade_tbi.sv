`include "svc_unit.sv"

`include "svc_gfx_vga_fade.sv"
`include "svc_vga_mode.sv"

// ✨🤖✨ basic smoke test vibe coded with claude

// verilator lint_off: UNUSEDSIGNAL
module svc_gfx_vga_fade_tbi;
  localparam H_WIDTH = 12;
  localparam V_WIDTH = 12;
  localparam COLOR_WIDTH = 4;
  localparam PIXEL_WIDTH = 12;
  localparam AXI_ADDR_WIDTH = 16;
  localparam AXI_DATA_WIDTH = 16;
  localparam AXI_ID_WIDTH = 4;
  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;
  localparam AGE_BITS = 4;
  localparam FIFO_ADDR_WIDTH = 3;

  // Main system clock
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n, 50);

  // Pixel clock (slower than system clock)
  `TEST_CLK_NS(pixel_clk, 40);

  // Pixel clock reset (using main reset for simplicity)
  logic pixel_rst_n;
  assign pixel_rst_n = rst_n;

  // Graphics input stream
  logic                      s_gfx_valid;
  logic [       H_WIDTH-1:0] s_gfx_x;
  logic [       V_WIDTH-1:0] s_gfx_y;
  logic [   PIXEL_WIDTH-1:0] s_gfx_pixel;
  logic                      s_gfx_ready;

  // Framebuffer start signal
  logic                      fb_start;

  // AXI Memory Interface - Write
  logic                      m_axi_awvalid;
  logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr;
  logic [               1:0] m_axi_awburst;
  logic [  AXI_ID_WIDTH-1:0] m_axi_awid;
  logic [               7:0] m_axi_awlen;
  logic [               2:0] m_axi_awsize;
  logic                      m_axi_awready;
  logic [AXI_DATA_WIDTH-1:0] m_axi_wdata;
  logic                      m_axi_wlast;
  logic                      m_axi_wready;
  logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb;
  logic                      m_axi_wvalid;
  logic                      m_axi_bvalid;
  logic [  AXI_ID_WIDTH-1:0] m_axi_bid;
  logic [               1:0] m_axi_bresp;
  logic                      m_axi_bready;

  // AXI Memory Interface - Read
  logic                      m_axi_arvalid;
  logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr;
  logic [               1:0] m_axi_arburst;
  logic [  AXI_ID_WIDTH-1:0] m_axi_arid;
  logic [               7:0] m_axi_arlen;
  logic [               2:0] m_axi_arsize;
  logic                      m_axi_arready;
  logic                      m_axi_rvalid;
  logic [  AXI_ID_WIDTH-1:0] m_axi_rid;
  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata;
  logic [               1:0] m_axi_rresp;
  logic                      m_axi_rlast;
  logic                      m_axi_rready;

  // VGA Mode settings
  logic [       H_WIDTH-1:0] h_visible;
  logic [       H_WIDTH-1:0] h_sync_start;
  logic [       H_WIDTH-1:0] h_sync_end;
  logic [       H_WIDTH-1:0] h_line_end;

  logic [       V_WIDTH-1:0] v_visible;
  logic [       V_WIDTH-1:0] v_sync_start;
  logic [       V_WIDTH-1:0] v_sync_end;
  logic [       V_WIDTH-1:0] v_frame_end;


  // VGA outputs
  logic [   COLOR_WIDTH-1:0] vga_red;
  logic [   COLOR_WIDTH-1:0] vga_grn;
  logic [   COLOR_WIDTH-1:0] vga_blu;
  logic                      vga_hsync;
  logic                      vga_vsync;
  logic                      vga_error;

  // Unit under test
  svc_gfx_vga_fade #(
      .H_WIDTH        (H_WIDTH),
      .V_WIDTH        (V_WIDTH),
      .COLOR_WIDTH    (COLOR_WIDTH),
      .PIXEL_WIDTH    (PIXEL_WIDTH),
      .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH   (AXI_ID_WIDTH),
      .AGE_BITS       (AGE_BITS),
      .FIFO_ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) uut (
      .clk        (clk),
      .rst_n      (rst_n),
      .pixel_clk  (pixel_clk),
      .pixel_rst_n(pixel_rst_n),

      .s_gfx_valid(s_gfx_valid),
      .s_gfx_x    (s_gfx_x),
      .s_gfx_y    (s_gfx_y),
      .s_gfx_pixel(s_gfx_pixel),
      .s_gfx_ready(s_gfx_ready),

      .fb_start(fb_start),

      // AXI write interface
      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awlen  (m_axi_awlen),
      .m_axi_awsize (m_axi_awsize),
      .m_axi_awready(m_axi_awready),
      .m_axi_wdata  (m_axi_wdata),
      .m_axi_wlast  (m_axi_wlast),
      .m_axi_wready (m_axi_wready),
      .m_axi_wstrb  (m_axi_wstrb),
      .m_axi_wvalid (m_axi_wvalid),
      .m_axi_bvalid (m_axi_bvalid),
      .m_axi_bid    (m_axi_bid),
      .m_axi_bresp  (m_axi_bresp),
      .m_axi_bready (m_axi_bready),

      // AXI read interface
      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arid   (m_axi_arid),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arready(m_axi_arready),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rid    (m_axi_rid),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rlast  (m_axi_rlast),
      .m_axi_rready (m_axi_rready),

      // VGA mode settings
      .h_visible   (h_visible),
      .h_sync_start(h_sync_start),
      .h_sync_end  (h_sync_end),
      .h_line_end  (h_line_end),
      .v_visible   (v_visible),
      .v_sync_start(v_sync_start),
      .v_sync_end  (v_sync_end),
      .v_frame_end (v_frame_end),

      // VGA outputs
      .vga_red  (vga_red),
      .vga_grn  (vga_grn),
      .vga_blu  (vga_blu),
      .vga_hsync(vga_hsync),
      .vga_vsync(vga_vsync),
      .vga_error(vga_error)
  );

  // Simple AXI memory model - respond with fixed pattern data
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_axi_awready <= 1'b0;
      m_axi_wready  <= 1'b0;
      m_axi_bvalid  <= 1'b0;
      // Set response to OKAY
      m_axi_bid     <= '0;
      m_axi_bresp   <= 2'b00;

      m_axi_arready <= 1'b0;
      m_axi_rvalid  <= 1'b0;
      m_axi_rid     <= '0;
      m_axi_rdata   <= '0;
      // Set response to OKAY
      m_axi_rresp   <= 2'b00;
      m_axi_rlast   <= 1'b0;
    end else begin
      // Write address channel
      // Accept address after 1 cycle
      if (m_axi_awvalid && !m_axi_awready) begin
        m_axi_awready <= 1'b1;
      end else begin
        m_axi_awready <= 1'b0;
      end

      // Write data channel
      // Accept data after 1 cycle
      if (m_axi_wvalid && !m_axi_wready) begin
        m_axi_wready <= 1'b1;
      end else begin
        m_axi_wready <= 1'b0;
      end

      // Write response channel
      if (m_axi_wvalid && m_axi_wready && m_axi_wlast && !m_axi_bvalid) begin
        m_axi_bvalid <= 1'b1;
        // Echo back the ID
        m_axi_bid    <= m_axi_awid;
      end else if (m_axi_bvalid && m_axi_bready) begin
        m_axi_bvalid <= 1'b0;
      end

      // Read address channel
      // Accept address after 1 cycle
      if (m_axi_arvalid && !m_axi_arready) begin
        m_axi_arready <= 1'b1;
      end else begin
        m_axi_arready <= 1'b0;
      end

      // Read data channel
      if (m_axi_arready && m_axi_arvalid) begin
        logic [AGE_BITS-1:0] age_value;

        m_axi_rvalid <= 1'b1;
        m_axi_rid    <= m_axi_arid;

        // Simple test pattern with age embedded in the upper bits
        // Age cycles through values 0-15 based on address
        age_value = AGE_BITS'(m_axi_araddr[5:2])
            ;  // Use some address bits to create different ages

        // Format: {age, pixel}
        m_axi_rdata <= {age_value, 4'hA, 4'h5, 4'h0};

        // Always last for simplicity
        m_axi_rlast <= 1'b1;
      end else if (m_axi_rvalid && m_axi_rready) begin
        // Clear when transfer is done
        m_axi_rvalid <= 1'b0;
        m_axi_rlast  <= 1'b0;
      end
    end
  end

  // Simple input pattern generator for gfx stream
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      s_gfx_valid <= 1'b0;
      s_gfx_x     <= '0;
      s_gfx_y     <= '0;
      s_gfx_pixel <= '0;
      fb_start    <= 1'b0;
    end else begin
      // If pixel accepted or not valid
      if ((s_gfx_valid && s_gfx_ready) || !s_gfx_valid) begin
        // Generate pixel at random locations with width casts to avoid warnings
        if (s_gfx_valid == 1'b0 && $urandom_range(0, 10) < 3) begin
          s_gfx_valid <= 1'b1;
          s_gfx_x     <= H_WIDTH'($urandom_range(0, h_visible - 1));
          s_gfx_y     <= V_WIDTH'($urandom_range(0, v_visible - 1));
          s_gfx_pixel <= PIXEL_WIDTH'($urandom_range(0, 2 ** PIXEL_WIDTH - 1));
        end else begin
          s_gfx_valid <= 1'b0;
        end
      end
    end
  end

  task automatic test_smoke;
    // Set VGA mode to 640x480 @ 60Hz
    h_visible    = `VGA_MODE_640x480_H_VISIBLE;
    h_sync_start = `VGA_MODE_640x480_H_SYNC_START;
    h_sync_end   = `VGA_MODE_640x480_H_SYNC_END;
    h_line_end   = `VGA_MODE_640x480_H_LINE_END;

    v_visible    = `VGA_MODE_640x480_V_VISIBLE;
    v_sync_start = `VGA_MODE_640x480_V_SYNC_START;
    v_sync_end   = `VGA_MODE_640x480_V_SYNC_END;
    v_frame_end  = `VGA_MODE_640x480_V_FRAME_END;


    // Start framebuffer operation
    fb_start     = 1'b1;
    `TICK(clk);
    `CHECK_EQ(uut.fb_pix_rst, 1'b1);

    // Write some pixels
    for (int i = 0; i < 20; i++) begin
      repeat (5) @(posedge clk);
    end

    // Verify AXI transactions are happening
    `CHECK_WAIT_FOR(clk, m_axi_awvalid || m_axi_arvalid, 100);
    `CHECK_FALSE(vga_error);

    repeat (20) @(posedge clk);
    `CHECK_FALSE(vga_error);
  endtask

  // Test fade transitions - check basic fade functionality
  task automatic test_fade_transitions;
    // Set VGA mode to 640x480 @ 60Hz
    h_visible    = `VGA_MODE_640x480_H_VISIBLE;
    h_sync_start = `VGA_MODE_640x480_H_SYNC_START;
    h_sync_end   = `VGA_MODE_640x480_H_SYNC_END;
    h_line_end   = `VGA_MODE_640x480_H_LINE_END;

    v_visible    = `VGA_MODE_640x480_V_VISIBLE;
    v_sync_start = `VGA_MODE_640x480_V_SYNC_START;
    v_sync_end   = `VGA_MODE_640x480_V_SYNC_END;
    v_frame_end  = `VGA_MODE_640x480_V_FRAME_END;

    // Start framebuffer operation
    fb_start     = 1'b1;
    `TICK(clk);

    // Let it run for a while to observe different fade scenarios
    repeat (20) @(posedge clk);
    `CHECK_FALSE(vga_error);

    // Check that internal pixel stream is active (using hierarchical reference)
    `CHECK_WAIT_FOR(clk, uut.fb_pix_valid, 50);

    // Just verify that the test doesn't crash
    repeat (10) @(posedge clk);
    `CHECK_FALSE(vga_error);
  endtask

  // Test pixel stream interface (now checking internal signals)
  task automatic test_pixel_stream;
    // Set VGA mode to 640x480 @ 60Hz
    h_visible    = `VGA_MODE_640x480_H_VISIBLE;
    h_sync_start = `VGA_MODE_640x480_H_SYNC_START;
    h_sync_end   = `VGA_MODE_640x480_H_SYNC_END;
    h_line_end   = `VGA_MODE_640x480_H_LINE_END;

    v_visible    = `VGA_MODE_640x480_V_VISIBLE;
    v_sync_start = `VGA_MODE_640x480_V_SYNC_START;
    v_sync_end   = `VGA_MODE_640x480_V_SYNC_END;
    v_frame_end  = `VGA_MODE_640x480_V_FRAME_END;

    // Start framebuffer operation
    fb_start     = 1'b1;
    `TICK(clk);

    // Wait a bit for system to initialize
    repeat (30) @(posedge clk);

    // The internal pixel stream should be active
    `CHECK_WAIT_FOR(clk, uut.fb_pix_valid, 100);

    // Just check that the system is running properly
    repeat (10) @(posedge clk);
    `CHECK_FALSE(vga_error);
  endtask

  // Reset test
  task automatic test_reset;
    // Reset is initially asserted (low) by the TEST_RST_N macro then deasserted
    repeat (5) @(posedge clk);
    `CHECK_EQ(rst_n, 1'b1);  // Should be deasserted by now
    `CHECK_FALSE(vga_error);
  endtask

  `TEST_SUITE_BEGIN(svc_gfx_vga_fade_tbi, 1000);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_smoke);
  `TEST_CASE(test_fade_transitions);
  `TEST_CASE(test_pixel_stream);
  `TEST_SUITE_END();

endmodule
