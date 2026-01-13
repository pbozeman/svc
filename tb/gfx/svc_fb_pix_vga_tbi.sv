`include "svc_unit.sv"
`include "svc_fb_pix_vga.sv"
`include "svc_axi_mem.sv"

// ✨🤖✨ vibe coded with claude

// TODO: this test is pretty bad in that it doesn't check the outputs. Fix
// that

// verilator lint_off: UNUSEDSIGNAL
module svc_fb_pix_vga_tbi;
  localparam H_WIDTH = 12;
  localparam V_WIDTH = 12;
  localparam COLOR_WIDTH = 4;
  localparam AXI_ADDR_WIDTH = 16;
  localparam AXI_DATA_WIDTH = 16;
  localparam AXI_ID_WIDTH = 4;
  localparam FIFO_ADDR_WIDTH = 3;

  // Create system clocks
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);
  `TEST_CLK_NS(pixel_clk, 40);

  // AXI read channel
  logic                        m_axi_arvalid;
  logic [  AXI_ADDR_WIDTH-1:0] m_axi_araddr;
  logic [                 1:0] m_axi_arburst;
  logic [    AXI_ID_WIDTH-1:0] m_axi_arid;
  logic [                 7:0] m_axi_arlen;
  logic [                 2:0] m_axi_arsize;
  logic                        m_axi_arready;
  logic                        m_axi_rvalid;
  logic [    AXI_ID_WIDTH-1:0] m_axi_rid;
  logic [  AXI_DATA_WIDTH-1:0] m_axi_rdata;
  logic [                 1:0] m_axi_rresp;
  logic                        m_axi_rlast;
  logic                        m_axi_rready;

  // Video timing
  logic [         H_WIDTH-1:0] h_visible;
  logic [         H_WIDTH-1:0] h_sync_start;
  logic [         H_WIDTH-1:0] h_sync_end;
  logic [         H_WIDTH-1:0] h_line_end;
  logic [         V_WIDTH-1:0] v_visible;
  logic [         V_WIDTH-1:0] v_sync_start;
  logic [         V_WIDTH-1:0] v_sync_end;
  logic [         V_WIDTH-1:0] v_frame_end;

  // Pixel stream
  logic                        m_pix_valid;
  logic [     COLOR_WIDTH-1:0] m_pix_red;
  logic [     COLOR_WIDTH-1:0] m_pix_grn;
  logic [     COLOR_WIDTH-1:0] m_pix_blu;
  logic [         H_WIDTH-1:0] m_pix_x;
  logic [         V_WIDTH-1:0] m_pix_y;
  logic [  AXI_ADDR_WIDTH-1:0] m_pix_addr;
  logic                        m_pix_ready;

  // VGA output
  logic [     COLOR_WIDTH-1:0] vga_red;
  logic [     COLOR_WIDTH-1:0] vga_grn;
  logic [     COLOR_WIDTH-1:0] vga_blu;
  logic                        vga_hsync;
  logic                        vga_vsync;
  logic                        vga_error;

  // Write channel signals (not used in this test, but needed for AXI mem)
  logic                        s_axi_awvalid;
  logic [    AXI_ID_WIDTH-1:0] s_axi_awid;
  logic [  AXI_ADDR_WIDTH-1:0] s_axi_awaddr;
  logic [                 7:0] s_axi_awlen;
  logic [                 2:0] s_axi_awsize;
  logic [                 1:0] s_axi_awburst;
  logic                        s_axi_awready;
  logic                        s_axi_wvalid;
  logic [  AXI_DATA_WIDTH-1:0] s_axi_wdata;
  logic [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb;
  logic                        s_axi_wlast;
  logic                        s_axi_wready;
  logic                        s_axi_bvalid;
  logic [    AXI_ID_WIDTH-1:0] s_axi_bid;
  logic [                 1:0] s_axi_bresp;
  logic                        s_axi_bready;

  // Unit under test
  svc_fb_pix_vga #(
      .H_WIDTH        (H_WIDTH),
      .V_WIDTH        (V_WIDTH),
      .COLOR_WIDTH    (COLOR_WIDTH),
      .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH   (AXI_ID_WIDTH),
      .FIFO_ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) uut (
      .clk          (clk),
      .rst_n        (rst_n),
      .pixel_clk    (pixel_clk),
      .pixel_rst_n  (rst_n),
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
      .h_visible    (h_visible),
      .h_sync_start (h_sync_start),
      .h_sync_end   (h_sync_end),
      .h_line_end   (h_line_end),
      .v_visible    (v_visible),
      .v_sync_start (v_sync_start),
      .v_sync_end   (v_sync_end),
      .v_frame_end  (v_frame_end),
      .m_pix_valid  (m_pix_valid),
      .m_pix_red    (m_pix_red),
      .m_pix_grn    (m_pix_grn),
      .m_pix_blu    (m_pix_blu),
      .m_pix_x      (m_pix_x),
      .m_pix_y      (m_pix_y),
      .m_pix_addr   (m_pix_addr),
      .m_pix_ready  (m_pix_ready),
      .vga_red      (vga_red),
      .vga_grn      (vga_grn),
      .vga_blu      (vga_blu),
      .vga_hsync    (vga_hsync),
      .vga_vsync    (vga_vsync),
      .vga_error    (vga_error)
  );

  // Initialize write channel signals to inactive state
  assign s_axi_awvalid = 1'b0;
  assign s_axi_awid    = 0;
  assign s_axi_awaddr  = 0;
  assign s_axi_awlen   = 0;
  assign s_axi_awsize  = 0;
  assign s_axi_awburst = 0;
  assign s_axi_wvalid  = 1'b0;
  assign s_axi_wdata   = 0;
  assign s_axi_wstrb   = 0;
  assign s_axi_wlast   = 1'b0;
  assign s_axi_bready  = 1'b1;

  // AXI memory model
  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) mem_i (
      .clk  (clk),
      .rst_n(rst_n),

      // Write channel (unused)
      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awready(s_axi_awready),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wready (s_axi_wready),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bid    (s_axi_bid),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_bready (s_axi_bready),

      // Read channel (connected to DUT)
      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arid   (m_axi_arid),
      .s_axi_araddr (m_axi_araddr),
      .s_axi_arlen  (m_axi_arlen),
      .s_axi_arsize (m_axi_arsize),
      .s_axi_arburst(m_axi_arburst),
      .s_axi_arready(m_axi_arready),
      .s_axi_rvalid (m_axi_rvalid),
      .s_axi_rid    (m_axi_rid),
      .s_axi_rdata  (m_axi_rdata),
      .s_axi_rresp  (m_axi_rresp),
      .s_axi_rlast  (m_axi_rlast),
      .s_axi_rready (m_axi_rready)
  );

  // Initialize memory with test pattern
  initial begin
    int         addr;
    logic [3:0] red;
    logic [3:0] grn;
    logic [3:0] blu;

    for (int y = 0; y < 480; y++) begin
      for (int x = 0; x < 640; x++) begin
        addr = (y * 640 + x) * 2;

        // Assign color values based on screen position
        if (x < 213) begin
          red = 4'hF;
          grn = 4'h0;
          blu = 4'h0;
        end else if (x < 426) begin
          red = 4'h0;
          grn = 4'hF;
          blu = 4'h0;
        end else begin
          red = 4'h0;
          grn = 4'h0;
          blu = 4'hF;
        end

        // Access memory directly through the memory array in svc_axi_mem
        mem_i.mem[addr>>1] = {4'h0, red, grn, blu};
      end
    end
  end

  // Test reset state
  task automatic test_reset;
    // Configure video parameters (640x480 @ 60Hz)
    h_visible    = 640;
    h_sync_start = 656;
    h_sync_end   = 752;
    h_line_end   = 800;
    v_visible    = 480;
    v_sync_start = 490;
    v_sync_end   = 492;
    v_frame_end  = 525;

    // Initialize pixel stream
    m_pix_ready  = 1'b1;

    // Wait for a few clock cycles after reset
    `TICK(clk);
    `TICK(clk);

    // Check outputs
    `CHECK_FALSE(m_pix_valid);
  endtask

  // Basic smoke test - just run for a while and make sure no errors
  task automatic test_smoke;
    // Enable pixel stream capture
    m_pix_ready = 1'b1;

    // Run for some time
    repeat (1000) `TICK(clk);

    // Check no VGA errors
    `CHECK_FALSE(vga_error);
  endtask

  // Test pixel stream output
  task automatic test_pixel_stream;
    // Accept all pixels
    m_pix_ready = 1'b1;

    // Run for a while to allow pixel generation
    repeat (5000) `TICK(clk);

    // Check some basic conditions
    `CHECK_FALSE(vga_error);
  endtask

  `TEST_SUITE_BEGIN(svc_fb_pix_vga_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_smoke);
  `TEST_CASE(test_pixel_stream);
  `TEST_SUITE_END();

endmodule
