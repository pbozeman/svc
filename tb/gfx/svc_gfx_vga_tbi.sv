`include "svc_unit.sv"

`include "svc_axi_mem.sv"
`include "svc_gfx_vga.sv"
`include "svc_vga_mode.sv"

// this started as a claued file, but it was really messed up

// verilator lint_off: UNUSEDSIGNAL
module svc_gfx_vga_tbi;
  localparam H_WIDTH = 12;
  localparam V_WIDTH = 12;
  localparam COLOR_WIDTH = 4;
  localparam PIXEL_WIDTH = 12;
  localparam AXI_ADDR_WIDTH = 16;
  localparam AXI_DATA_WIDTH = 16;
  localparam AXI_ID_WIDTH = 4;
  localparam AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8;

  // Main system clock
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n, 50);

  // Pixel clock (slower than system clock)
  `TEST_CLK_NS(pixel_clk, 40);

  // Pixel clock reset (using main reset for simplicity)
  logic pixel_rst_n;
  assign pixel_rst_n = rst_n;

  // Graphics input stream
  logic                      m_gfx_valid;
  logic [       H_WIDTH-1:0] m_gfx_x;
  logic [       V_WIDTH-1:0] m_gfx_y;
  logic [   PIXEL_WIDTH-1:0] m_gfx_pixel;
  logic                      m_gfx_ready;

  // Framebuffer start signal
  logic                      fb_start;

  logic                      mem_axi_awvalid;
  logic [AXI_ADDR_WIDTH-1:0] mem_axi_awaddr;
  logic [               1:0] mem_axi_awburst;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_awid;
  logic [               7:0] mem_axi_awlen;
  logic [               2:0] mem_axi_awsize;
  logic                      mem_axi_awready;
  logic [AXI_DATA_WIDTH-1:0] mem_axi_wdata;
  logic                      mem_axi_wlast;
  logic                      mem_axi_wready;
  logic [AXI_STRB_WIDTH-1:0] mem_axi_wstrb;
  logic                      mem_axi_wvalid;
  logic                      mem_axi_bvalid;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_bid;
  logic [               1:0] mem_axi_bresp;
  logic                      mem_axi_bready;

  // AXI Memory Interface - Read
  logic                      mem_axi_arvalid;
  logic [AXI_ADDR_WIDTH-1:0] mem_axi_araddr;
  logic [               1:0] mem_axi_arburst;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_arid;
  logic [               7:0] mem_axi_arlen;
  logic [               2:0] mem_axi_arsize;
  logic                      mem_axi_arready;
  logic                      mem_axi_rvalid;
  logic [  AXI_ID_WIDTH-1:0] mem_axi_rid;
  logic [AXI_DATA_WIDTH-1:0] mem_axi_rdata;
  logic [               1:0] mem_axi_rresp;
  logic                      mem_axi_rlast;
  logic                      mem_axi_rready;

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
  svc_gfx_vga #(
      .H_WIDTH       (H_WIDTH),
      .V_WIDTH       (V_WIDTH),
      .COLOR_WIDTH   (COLOR_WIDTH),
      .PIXEL_WIDTH   (PIXEL_WIDTH),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) uut (
      .clk        (clk),
      .rst_n      (rst_n),
      .pixel_clk  (pixel_clk),
      .pixel_rst_n(pixel_rst_n),

      .s_gfx_valid(m_gfx_valid),
      .s_gfx_x    (m_gfx_x),
      .s_gfx_y    (m_gfx_y),
      .s_gfx_pixel(m_gfx_pixel),
      .s_gfx_ready(m_gfx_ready),

      .fb_start(fb_start),

      // AXI write interface
      .m_axi_awvalid(mem_axi_awvalid),
      .m_axi_awaddr (mem_axi_awaddr),
      .m_axi_awburst(mem_axi_awburst),
      .m_axi_awid   (mem_axi_awid),
      .m_axi_awlen  (mem_axi_awlen),
      .m_axi_awsize (mem_axi_awsize),
      .m_axi_awready(mem_axi_awready),
      .m_axi_wdata  (mem_axi_wdata),
      .m_axi_wlast  (mem_axi_wlast),
      .m_axi_wready (mem_axi_wready),
      .m_axi_wstrb  (mem_axi_wstrb),
      .m_axi_wvalid (mem_axi_wvalid),
      .m_axi_bvalid (mem_axi_bvalid),
      .m_axi_bid    (mem_axi_bid),
      .m_axi_bresp  (mem_axi_bresp),
      .m_axi_bready (mem_axi_bready),

      // AXI read interface
      .m_axi_arvalid(mem_axi_arvalid),
      .m_axi_araddr (mem_axi_araddr),
      .m_axi_arburst(mem_axi_arburst),
      .m_axi_arid   (mem_axi_arid),
      .m_axi_arlen  (mem_axi_arlen),
      .m_axi_arsize (mem_axi_arsize),
      .m_axi_arready(mem_axi_arready),
      .m_axi_rvalid (mem_axi_rvalid),
      .m_axi_rid    (mem_axi_rid),
      .m_axi_rdata  (mem_axi_rdata),
      .m_axi_rresp  (mem_axi_rresp),
      .m_axi_rlast  (mem_axi_rlast),
      .m_axi_rready (mem_axi_rready),

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

  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_mem_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(mem_axi_awvalid),
      .s_axi_awid   (mem_axi_awid),
      .s_axi_awaddr (mem_axi_awaddr),
      .s_axi_awlen  (mem_axi_awlen),
      .s_axi_awsize (mem_axi_awsize),
      .s_axi_awburst(mem_axi_awburst),
      .s_axi_awready(mem_axi_awready),
      .s_axi_wvalid (mem_axi_wvalid),
      .s_axi_wdata  (mem_axi_wdata),
      .s_axi_wstrb  (mem_axi_wstrb),
      .s_axi_wlast  (mem_axi_wlast),
      .s_axi_wready (mem_axi_wready),
      .s_axi_bvalid (mem_axi_bvalid),
      .s_axi_bid    (mem_axi_bid),
      .s_axi_bresp  (mem_axi_bresp),
      .s_axi_bready (mem_axi_bready),

      .s_axi_arvalid(mem_axi_arvalid),
      .s_axi_arid   (mem_axi_arid),
      .s_axi_araddr (mem_axi_araddr),
      .s_axi_arlen  (mem_axi_arlen),
      .s_axi_arsize (mem_axi_arsize),
      .s_axi_arburst(mem_axi_arburst),
      .s_axi_arready(mem_axi_arready),
      .s_axi_rvalid (mem_axi_rvalid),
      .s_axi_rid    (mem_axi_rid),
      .s_axi_rdata  (mem_axi_rdata),
      .s_axi_rresp  (mem_axi_rresp),
      .s_axi_rlast  (mem_axi_rlast),
      .s_axi_rready (mem_axi_rready)
  );

  // Simple input pattern generator for gfx stream
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_gfx_valid <= 1'b0;
      m_gfx_x     <= '0;
      m_gfx_y     <= '0;
      m_gfx_pixel <= '0;
      fb_start    <= 1'b0;
    end else begin
      m_gfx_valid <= 1'b1;

      if (m_gfx_ready) begin
        if (m_gfx_x < h_visible) begin
          m_gfx_x <= m_gfx_x + 1;
        end else begin
          m_gfx_x <= 0;

          if (m_gfx_y < v_visible) begin
            m_gfx_y <= m_gfx_y + 1;
          end else begin
            m_gfx_y <= 0;
          end
        end

        m_gfx_pixel <= PIXEL_WIDTH'(m_gfx_x);
      end
    end
  end

  task automatic test_reset;
    fb_start = 1'b0;
    `CHECK_FALSE(vga_error);
  endtask

  task automatic test_smoke;
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

    // Write some pixels
    for (int i = 0; i < 20; i++) begin
      repeat (5) @(posedge clk);
    end

    // TODO: validate some of the pixels

    // Run for a while to check for any errors
    repeat (50) @(posedge clk);
    `CHECK_FALSE(vga_error);
  endtask

  `TEST_SUITE_BEGIN(svc_gfx_vga_tbi, 1000);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_smoke);
  `TEST_SUITE_END();

endmodule
