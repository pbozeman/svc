`ifndef SVC_GFX_VGA_FADE_SV
`define SVC_GFX_VGA_FADE_SV

`include "svc_axi_arbiter.sv"
`include "svc_fb_vga.sv"
`include "svc_gfx_fb.sv"
`include "svc_axi_null.sv"
`include "svc_unused.sv"

module svc_gfx_vga_fade #(
    parameter AXI_ADDR_WIDTH = 16,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter COLOR_WIDTH    = 4,
    parameter H_WIDTH        = 12,
    parameter V_WIDTH        = 12,
    parameter PIXEL_WIDTH    = 12
) (
    input logic clk,
    input logic rst_n,

    input logic pixel_clk,
    input logic pixel_rst_n,

    input  logic                   s_gfx_valid,
    input  logic [    H_WIDTH-1:0] s_gfx_x,
    input  logic [    V_WIDTH-1:0] s_gfx_y,
    input  logic [PIXEL_WIDTH-1:0] s_gfx_pixel,
    output logic                   s_gfx_ready,

    // This is not an enable, once started, it runs, even if this goes low
    // again.
    //
    // TODO: change this to a true enable signal, i.e. fb_en, once the display
    // side can resync the signal.
    input logic fb_start,

    output logic                      m_axi_awvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [               1:0] m_axi_awburst,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    input  logic                      m_axi_awready,
    output logic [AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic                      m_axi_wlast,
    input  logic                      m_axi_wready,
    output logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    output logic                      m_axi_wvalid,
    input  logic                      m_axi_bvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [               1:0] m_axi_bresp,
    output logic                      m_axi_bready,

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

    input logic [H_WIDTH-1:0] h_visible,
    input logic [H_WIDTH-1:0] h_sync_start,
    input logic [H_WIDTH-1:0] h_sync_end,
    input logic [H_WIDTH-1:0] h_line_end,

    input logic [V_WIDTH-1:0] v_visible,
    input logic [V_WIDTH-1:0] v_sync_start,
    input logic [V_WIDTH-1:0] v_sync_end,
    input logic [V_WIDTH-1:0] v_frame_end,

    output logic [COLOR_WIDTH-1:0] vga_red,
    output logic [COLOR_WIDTH-1:0] vga_grn,
    output logic [COLOR_WIDTH-1:0] vga_blu,
    output logic                   vga_hsync,
    output logic                   vga_vsync,
    output logic                   vga_error
);
  // incoming gfx, fader, outgoing pix
  localparam NUM_M = 3;
  localparam AS_AXI_ID_WIDTH = AXI_ID_WIDTH - $clog2(NUM_M);

  // arbiter subordinate signals
  logic [NUM_M-1:0]                      as_axi_awvalid;
  logic [NUM_M-1:0][ AXI_ADDR_WIDTH-1:0] as_axi_awaddr;
  logic [NUM_M-1:0][AS_AXI_ID_WIDTH-1:0] as_axi_awid;
  logic [NUM_M-1:0][                7:0] as_axi_awlen;
  logic [NUM_M-1:0][                2:0] as_axi_awsize;
  logic [NUM_M-1:0][                1:0] as_axi_awburst;
  logic [NUM_M-1:0]                      as_axi_awready;
  logic [NUM_M-1:0]                      as_axi_wvalid;
  logic [NUM_M-1:0][ AXI_DATA_WIDTH-1:0] as_axi_wdata;
  logic [NUM_M-1:0][ AXI_STRB_WIDTH-1:0] as_axi_wstrb;
  logic [NUM_M-1:0]                      as_axi_wlast;
  logic [NUM_M-1:0]                      as_axi_wready;
  logic [NUM_M-1:0]                      as_axi_bvalid;
  logic [NUM_M-1:0][AS_AXI_ID_WIDTH-1:0] as_axi_bid;
  logic [NUM_M-1:0][                1:0] as_axi_bresp;
  logic [NUM_M-1:0]                      as_axi_bready;

  logic [NUM_M-1:0]                      as_axi_arvalid;
  logic [NUM_M-1:0][AS_AXI_ID_WIDTH-1:0] as_axi_arid;
  logic [NUM_M-1:0][ AXI_ADDR_WIDTH-1:0] as_axi_araddr;
  logic [NUM_M-1:0][                7:0] as_axi_arlen;
  logic [NUM_M-1:0][                2:0] as_axi_arsize;
  logic [NUM_M-1:0][                1:0] as_axi_arburst;
  logic [NUM_M-1:0]                      as_axi_arready;
  logic [NUM_M-1:0]                      as_axi_rvalid;
  logic [NUM_M-1:0][AS_AXI_ID_WIDTH-1:0] as_axi_rid;
  logic [NUM_M-1:0][ AXI_DATA_WIDTH-1:0] as_axi_rdata;
  logic [NUM_M-1:0][                1:0] as_axi_rresp;
  logic [NUM_M-1:0]                      as_axi_rlast;
  logic [NUM_M-1:0]                      as_axi_rready;

  svc_axi_arbiter #(
      .NUM_M         (NUM_M),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AS_AXI_ID_WIDTH)
  ) svc_axi_arbiter_i (
      .clk          (clk),
      .rst_n        (rst_n),
      .s_axi_awvalid(as_axi_awvalid),
      .s_axi_awaddr (as_axi_awaddr),
      .s_axi_awid   (as_axi_awid),
      .s_axi_awlen  (as_axi_awlen),
      .s_axi_awsize (as_axi_awsize),
      .s_axi_awburst(as_axi_awburst),
      .s_axi_awready(as_axi_awready),
      .s_axi_wdata  (as_axi_wdata),
      .s_axi_wstrb  (as_axi_wstrb),
      .s_axi_wlast  (as_axi_wlast),
      .s_axi_wvalid (as_axi_wvalid),
      .s_axi_wready (as_axi_wready),
      .s_axi_bresp  (as_axi_bresp),
      .s_axi_bid    (as_axi_bid),
      .s_axi_bvalid (as_axi_bvalid),
      .s_axi_bready (as_axi_bready),
      .s_axi_arvalid(as_axi_arvalid),
      .s_axi_araddr (as_axi_araddr),
      .s_axi_arid   (as_axi_arid),
      .s_axi_arready(as_axi_arready),
      .s_axi_arlen  (as_axi_arlen),
      .s_axi_arsize (as_axi_arsize),
      .s_axi_arburst(as_axi_arburst),
      .s_axi_rvalid (as_axi_rvalid),
      .s_axi_rid    (as_axi_rid),
      .s_axi_rresp  (as_axi_rresp),
      .s_axi_rlast  (as_axi_rlast),
      .s_axi_rdata  (as_axi_rdata),
      .s_axi_rready (as_axi_rready),

      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awlen  (m_axi_awlen),
      .m_axi_awsize (m_axi_awsize),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awready(m_axi_awready),
      .m_axi_wdata  (m_axi_wdata),
      .m_axi_wstrb  (m_axi_wstrb),
      .m_axi_wlast  (m_axi_wlast),
      .m_axi_wvalid (m_axi_wvalid),
      .m_axi_wready (m_axi_wready),
      .m_axi_bresp  (m_axi_bresp),
      .m_axi_bid    (m_axi_bid),
      .m_axi_bvalid (m_axi_bvalid),
      .m_axi_bready (m_axi_bready),
      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arid   (m_axi_arid),
      .m_axi_arready(m_axi_arready),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rid    (m_axi_rid),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rlast  (m_axi_rlast),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rready (m_axi_rready)
  );

  svc_gfx_fb #(
      .H_WIDTH       (H_WIDTH),
      .V_WIDTH       (V_WIDTH),
      .PIXEL_WIDTH   (PIXEL_WIDTH),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AS_AXI_ID_WIDTH)
  ) svc_gfx_fb_i (
      .clk          (clk),
      .rst_n        (rst_n),
      .s_gfx_valid  (s_gfx_valid),
      .s_gfx_x      (s_gfx_x),
      .s_gfx_y      (s_gfx_y),
      .s_gfx_pixel  (s_gfx_pixel),
      .s_gfx_ready  (s_gfx_ready),
      .h_visible    (h_visible),
      .v_visible    (v_visible),
      .m_axi_awvalid(as_axi_awvalid[0]),
      .m_axi_awaddr (as_axi_awaddr[0]),
      .m_axi_awid   (as_axi_awid[0]),
      .m_axi_awlen  (as_axi_awlen[0]),
      .m_axi_awsize (as_axi_awsize[0]),
      .m_axi_awburst(as_axi_awburst[0]),
      .m_axi_awready(as_axi_awready[0]),
      .m_axi_wvalid (as_axi_wvalid[0]),
      .m_axi_wdata  (as_axi_wdata[0]),
      .m_axi_wstrb  (as_axi_wstrb[0]),
      .m_axi_wlast  (as_axi_wlast[0]),
      .m_axi_wready (as_axi_wready[0]),
      .m_axi_bvalid (as_axi_bvalid[0]),
      .m_axi_bid    (as_axi_bid[0]),
      .m_axi_bresp  (as_axi_bresp[0]),
      .m_axi_bready (as_axi_bready[0])
  );

  // gfx_fb doesn't read
  assign as_axi_arvalid[0] = 1'b0;
  assign as_axi_arid[0]    = 0;
  assign as_axi_araddr[0]  = 0;
  assign as_axi_arlen[0]   = 0;
  assign as_axi_arsize[0]  = 0;
  assign as_axi_arburst[0] = 0;
  assign as_axi_rready[0]  = 1'b1;

  logic fb_pix_rst;
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      fb_pix_rst <= 1'b0;
    end else begin
      fb_pix_rst <= fb_pix_rst || fb_start;
    end
  end

  svc_fb_vga #(
      .H_WIDTH       (H_WIDTH),
      .V_WIDTH       (V_WIDTH),
      .COLOR_WIDTH   (COLOR_WIDTH),
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AS_AXI_ID_WIDTH)
  ) svc_fb_vga_i (
      .clk  (clk),
      .rst_n(fb_pix_rst),

      .pixel_clk  (pixel_clk),
      .pixel_rst_n(pixel_rst_n),

      .m_axi_arvalid(as_axi_arvalid[1]),
      .m_axi_arid   (as_axi_arid[1]),
      .m_axi_araddr (as_axi_araddr[1]),
      .m_axi_arlen  (as_axi_arlen[1]),
      .m_axi_arsize (as_axi_arsize[1]),
      .m_axi_arburst(as_axi_arburst[1]),
      .m_axi_arready(as_axi_arready[1]),
      .m_axi_rvalid (as_axi_rvalid[1]),
      .m_axi_rid    (as_axi_rid[1]),
      .m_axi_rdata  (as_axi_rdata[1]),
      .m_axi_rresp  (as_axi_rresp[1]),
      .m_axi_rlast  (as_axi_rlast[1]),
      .m_axi_rready (as_axi_rready[1]),

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

  // fb_vga doesn't write
  assign as_axi_awvalid[1] = 1'b0;
  assign as_axi_awid[1]    = 0;
  assign as_axi_awaddr[1]  = 0;
  assign as_axi_awlen[1]   = 0;
  assign as_axi_awsize[1]  = 0;
  assign as_axi_awburst[1] = 0;
  assign as_axi_wvalid[1]  = 1'b0;
  assign as_axi_wdata[1]   = 0;
  assign as_axi_wstrb[1]   = 0;
  assign as_axi_wlast[1]   = 0;
  assign as_axi_bready[1]  = 1'b1;

  // TODO: this will become the fader
  svc_axi_null #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AS_AXI_ID_WIDTH)
  ) svc_axi_null_i (
      .clk  (clk),
      .rst_n(rst_n),

      .m_axi_awvalid(as_axi_awvalid[2]),
      .m_axi_awaddr (as_axi_awaddr[2]),
      .m_axi_awid   (as_axi_awid[2]),
      .m_axi_awlen  (as_axi_awlen[2]),
      .m_axi_awsize (as_axi_awsize[2]),
      .m_axi_awburst(as_axi_awburst[2]),
      .m_axi_awready(as_axi_awready[2]),
      .m_axi_wvalid (as_axi_wvalid[2]),
      .m_axi_wdata  (as_axi_wdata[2]),
      .m_axi_wstrb  (as_axi_wstrb[2]),
      .m_axi_wlast  (as_axi_wlast[2]),
      .m_axi_wready (as_axi_wready[2]),
      .m_axi_bvalid (as_axi_bvalid[2]),
      .m_axi_bid    (as_axi_bid[2]),
      .m_axi_bresp  (as_axi_bresp[2]),
      .m_axi_bready (as_axi_bready[2]),

      .m_axi_arvalid(as_axi_arvalid[2]),
      .m_axi_arid   (as_axi_arid[2]),
      .m_axi_araddr (as_axi_araddr[2]),
      .m_axi_arlen  (as_axi_arlen[2]),
      .m_axi_arsize (as_axi_arsize[2]),
      .m_axi_arburst(as_axi_arburst[2]),
      .m_axi_arready(as_axi_arready[2]),
      .m_axi_rvalid (as_axi_rvalid[2]),
      .m_axi_rid    (as_axi_rid[2]),
      .m_axi_rdata  (as_axi_rdata[2]),
      .m_axi_rresp  (as_axi_rresp[2]),
      .m_axi_rlast  (as_axi_rlast[2]),
      .m_axi_rready (as_axi_rready[2])
  );

  `SVC_UNUSED({as_axi_rvalid[0], as_axi_rresp[0], as_axi_rid[0],
               as_axi_rlast[0], as_axi_rdata[0], as_axi_rid[0],
               as_axi_arready[0], as_axi_awready[1], as_axi_wready[1],
               as_axi_bvalid[1], as_axi_bid[1], as_axi_bresp[1]});

endmodule
`endif
