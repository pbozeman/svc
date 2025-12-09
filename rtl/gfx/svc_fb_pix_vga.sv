`ifndef SVC_FB_PIX_VGA_SV
`define SVC_FB_PIX_VGA_SV

`include "svc.sv"
`include "svc_fb_pix.sv"
`include "svc_pix_cdc.sv"
`include "svc_pix_vga.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

// ✨🤖✨ vibe coded with claude
//
// lots of fixes made since then, but there might be some residual weirdness

module svc_fb_pix_vga #(
    parameter H_WIDTH         = 12,
    parameter V_WIDTH         = 12,
    parameter COLOR_WIDTH     = 4,
    parameter AXI_ADDR_WIDTH  = 16,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_ID_WIDTH    = 4,
    parameter FIFO_ADDR_WIDTH = 3
) (
    input logic clk,
    input logic rst_n,

    input logic pixel_clk,
    input logic pixel_rst_n,

    // fb memory interface
    output logic                      m_axi_arvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               1:0] m_axi_arburst,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready,

    // h video settings
    input logic [H_WIDTH-1:0] h_visible,
    input logic [H_WIDTH-1:0] h_sync_start,
    input logic [H_WIDTH-1:0] h_sync_end,
    input logic [H_WIDTH-1:0] h_line_end,

    // v video settings
    input logic [V_WIDTH-1:0] v_visible,
    input logic [V_WIDTH-1:0] v_sync_start,
    input logic [V_WIDTH-1:0] v_sync_end,
    input logic [V_WIDTH-1:0] v_frame_end,

    // output pixel stream
    output logic                      m_pix_valid,
    output logic [   COLOR_WIDTH-1:0] m_pix_red,
    output logic [   COLOR_WIDTH-1:0] m_pix_grn,
    output logic [   COLOR_WIDTH-1:0] m_pix_blu,
    output logic [       H_WIDTH-1:0] m_pix_x,
    output logic [       V_WIDTH-1:0] m_pix_y,
    output logic [AXI_ADDR_WIDTH-1:0] m_pix_addr,
    input  logic                      m_pix_ready,

    // output pixels
    output logic [COLOR_WIDTH-1:0] vga_red,
    output logic [COLOR_WIDTH-1:0] vga_grn,
    output logic [COLOR_WIDTH-1:0] vga_blu,
    output logic                   vga_hsync,
    output logic                   vga_vsync,
    output logic                   vga_error
);
  localparam AW = AXI_ADDR_WIDTH;
  localparam CW = COLOR_WIDTH;
  localparam HW = H_WIDTH;
  localparam VW = V_WIDTH;
  localparam PIX_FIFO_WIDTH = CW * 3 + HW + VW + AW;

  // FB to PIX signals
  logic                      fb_pix_valid;
  logic [            CW-1:0] fb_pix_red;
  logic [            CW-1:0] fb_pix_grn;
  logic [            CW-1:0] fb_pix_blu;
  logic [            HW-1:0] fb_pix_x;
  logic [            VW-1:0] fb_pix_y;
  logic [            AW-1:0] fb_pix_addr;
  logic                      fb_pix_ready;

  // Internal signal for CDC ready to resolve multiple driver issue
  logic                      cdc_pix_ready;

  // Pixel FIFO signals
  logic                      pix_fifo_w_full;
  logic                      pix_fifo_r_empty;
  logic [PIX_FIFO_WIDTH-1:0] pix_fifo_w_data;
  logic [PIX_FIFO_WIDTH-1:0] pix_fifo_r_data;

  // CDC signals
  logic                      vga_pix_valid;
  logic [            CW-1:0] vga_pix_red;
  logic [            CW-1:0] vga_pix_grn;
  logic [            CW-1:0] vga_pix_blu;
  logic [            HW-1:0] vga_pix_x;
  logic [            VW-1:0] vga_pix_y;
  logic                      vga_pix_ready;

  // Framebuffer to pixel stream
  svc_fb_pix #(
      .H_WIDTH       (H_WIDTH),
      .V_WIDTH       (V_WIDTH),
      .COLOR_WIDTH   (COLOR_WIDTH),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_fb_pix_i (
      .clk          (clk),
      .rst_n        (rst_n),
      .m_pix_valid  (fb_pix_valid),
      .m_pix_red    (fb_pix_red),
      .m_pix_grn    (fb_pix_grn),
      .m_pix_blu    (fb_pix_blu),
      .m_pix_ready  (fb_pix_ready),
      .m_pix_x      (fb_pix_x),
      .m_pix_y      (fb_pix_y),
      .m_pix_addr   (fb_pix_addr),
      .h_visible    (h_visible),
      .v_visible    (v_visible),
      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_arid   (m_axi_arid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arready(m_axi_arready),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rid    (m_axi_rid),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rlast  (m_axi_rlast),
      .m_axi_rready (m_axi_rready)
  );

  // Pack pixel data for FIFO
  assign pix_fifo_w_data = {
    fb_pix_red, fb_pix_grn, fb_pix_blu, fb_pix_x, fb_pix_y, fb_pix_addr
  };

  // Pixel stream FIFO
  svc_sync_fifo #(
      .ADDR_WIDTH(FIFO_ADDR_WIDTH),
      .DATA_WIDTH(PIX_FIFO_WIDTH)
  ) svc_pix_fifo_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .clr        (1'b0),
      .w_inc      (fb_pix_valid && fb_pix_ready),
      .w_data     (pix_fifo_w_data),
      .w_full     (pix_fifo_w_full),
      .w_half_full(),
      .r_inc      (m_pix_valid && m_pix_ready),
      .r_empty    (pix_fifo_r_empty),
      .r_data     (pix_fifo_r_data)
  );

  // Unpack FIFO data to output pixel stream
  assign m_pix_valid = !pix_fifo_r_empty;

  // Connect ready signals
  assign fb_pix_ready = !pix_fifo_w_full && cdc_pix_ready;
  assign {m_pix_red, m_pix_grn, m_pix_blu, m_pix_x, m_pix_y, m_pix_addr} =
      pix_fifo_r_data;

  // Clock domain crossing
  svc_pix_cdc #(
      .H_WIDTH    (H_WIDTH),
      .V_WIDTH    (V_WIDTH),
      .COLOR_WIDTH(COLOR_WIDTH)
  ) svc_pix_cdc_i (
      .s_clk      (clk),
      .s_rst_n    (rst_n),
      .s_pix_valid(fb_pix_valid),
      .s_pix_red  (fb_pix_red),
      .s_pix_grn  (fb_pix_grn),
      .s_pix_blu  (fb_pix_blu),
      .s_pix_x    (fb_pix_x),
      .s_pix_y    (fb_pix_y),
      .s_pix_ready(cdc_pix_ready),

      .m_clk      (pixel_clk),
      .m_rst_n    (pixel_rst_n),
      .m_pix_valid(vga_pix_valid),
      .m_pix_red  (vga_pix_red),
      .m_pix_grn  (vga_pix_grn),
      .m_pix_blu  (vga_pix_blu),
      .m_pix_x    (vga_pix_x),
      .m_pix_y    (vga_pix_y),
      .m_pix_ready(vga_pix_ready)
  );

  // Convert to VGA signal
  svc_pix_vga #(
      .H_WIDTH    (H_WIDTH),
      .V_WIDTH    (V_WIDTH),
      .COLOR_WIDTH(COLOR_WIDTH)
  ) svc_pix_vga_i (
      .clk        (pixel_clk),
      .rst_n      (pixel_rst_n),
      .s_pix_valid(vga_pix_valid),
      .s_pix_red  (vga_pix_red),
      .s_pix_grn  (vga_pix_grn),
      .s_pix_blu  (vga_pix_blu),
      .s_pix_x    (vga_pix_x),
      .s_pix_y    (vga_pix_y),
      .s_pix_ready(vga_pix_ready),

      .h_visible   (h_visible),
      .h_sync_start(h_sync_start),
      .h_sync_end  (h_sync_end),
      .h_line_end  (h_line_end),

      .v_visible   (v_visible),
      .v_sync_start(v_sync_start),
      .v_sync_end  (v_sync_end),
      .v_frame_end (v_frame_end),

      .vga_hsync(vga_hsync),
      .vga_vsync(vga_vsync),
      .vga_red  (vga_red),
      .vga_grn  (vga_grn),
      .vga_blu  (vga_blu),
      .vga_error(vga_error)
  );

`ifdef FORMAL
`ifdef ZIPCPU_PRIVATE
`ifdef FORMAL_SVC_FB_PIX_VGA
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  logic f_past_valid = 0;
  always @(posedge clk) begin
    f_past_valid <= 1;
  end

`ifdef FORMAL_SVC_FB_PIX_VGA
  logic f_pixel_past_valid = 0;
  always @(posedge pixel_clk) begin
    f_pixel_past_valid <= 1;
  end
`endif

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
    assume (pixel_rst_n == f_past_valid);
  end

  // Stability assertions - pixel stream
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      // m_pix_valid should remain stable when m_pix_ready is low
      if ($past(m_pix_valid && !m_pix_ready)) begin
        `ASSERT(as_m_pix_valid_stable, m_pix_valid);
      end
    end
  end

  // Data stability assertions - pixel stream
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      // output signals should be stable until accepted
      if ($past(m_pix_valid && !m_pix_ready) && !m_pix_ready) begin
        `ASSERT(as_stable_m_pix_red, $stable(m_pix_red));
        `ASSERT(as_stable_m_pix_grn, $stable(m_pix_grn));
        `ASSERT(as_stable_m_pix_blu, $stable(m_pix_blu));
        `ASSERT(as_stable_m_pix_x, $stable(m_pix_x));
        `ASSERT(as_stable_m_pix_y, $stable(m_pix_y));
        `ASSERT(as_stable_m_pix_addr, $stable(m_pix_addr));
      end
    end
  end

  // TODO: VGA stream assertions

  // Stall detection from caller
  logic [3:0] stall_cnt;
  always @(posedge clk) begin
    if (!rst_n) begin
      stall_cnt <= 0;
    end else begin
      if (m_pix_valid) begin
        if (m_pix_ready) begin
          stall_cnt <= 0;
        end else begin
          stall_cnt <= stall_cnt + 1;
        end
      end
    end
  end

  // Stall detection - vga signal
  logic [3:0] pixel_stall_cnt;
  always @(posedge pixel_clk) begin
    if (!pixel_rst_n) begin
      pixel_stall_cnt <= 0;
    end else begin
      if (vga_pix_valid) begin
        if (vga_pix_ready) begin
          pixel_stall_cnt <= 0;
        end else begin
          pixel_stall_cnt <= pixel_stall_cnt + 1;
        end
      end
    end
  end

`ifdef FORMAL_SVC_FB_PIX_VGA
  // We don't to make such an assertion for our callers
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      assume (stall_cnt < 2);
    end
  end

  // dito from above
  always @(posedge pixel_clk) begin
    if (f_pixel_past_valid && $past(pixel_rst_n)) begin
      assume (pixel_stall_cnt < 2);
    end
  end
`endif

  // AXI interface compliance
  // verilator lint_off: PINMISSING
  faxi_master #(
      .C_AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .C_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .F_OPT_INITIAL   (1'b0),
      .OPT_EXCLUSIVE   (1'b0),
      .OPT_NARROW_BURST(1'b0),
      .F_LGDEPTH       (9),
      .F_AXI_MAXSTALL  (3),
      .F_AXI_MAXRSTALL (2),
      .F_AXI_MAXDELAY  (3)
  ) faxi_manager_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),
      .i_axi_awvalid(1'b0),
      .i_axi_awready(1'b0),
      .i_axi_awid   (0),
      .i_axi_awaddr (0),
      .i_axi_awlen  (0),
      .i_axi_awsize (0),
      .i_axi_awburst(0),
      .i_axi_awlock (0),
      .i_axi_awcache(0),
      .i_axi_awprot (0),
      .i_axi_awqos  (0),
      .i_axi_wvalid (0),
      .i_axi_wready (0),
      .i_axi_wdata  (0),
      .i_axi_wstrb  (0),
      .i_axi_wlast  (0),
      .i_axi_bvalid (1'b0),
      .i_axi_bready (1'b0),
      .i_axi_bid    (0),
      .i_axi_bresp  (2'b00),

      .i_axi_arvalid(m_axi_arvalid),
      .i_axi_arready(m_axi_arready),
      .i_axi_arid   (m_axi_arid),
      .i_axi_araddr (m_axi_araddr),
      .i_axi_arlen  (m_axi_arlen),
      .i_axi_arsize (m_axi_arsize),
      .i_axi_arburst(m_axi_arburst),
      .i_axi_arlock (0),
      .i_axi_arcache(0),
      .i_axi_arprot (0),
      .i_axi_arqos  (0),
      .i_axi_rvalid (m_axi_rvalid),
      .i_axi_rready (m_axi_rready),
      .i_axi_rdata  (m_axi_rdata),
      .i_axi_rid    (m_axi_rid),
      .i_axi_rlast  (m_axi_rlast),
      .i_axi_rresp  (m_axi_rresp)
  );
  // verilator lint_on: PINMISSING
`endif

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif

endmodule
`endif
