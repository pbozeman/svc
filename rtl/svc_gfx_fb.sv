`ifndef SVC_GFX_FB_SV
`define SVC_GFX_FB_SV

`include "svc.sv"
`include "svc_sync_fifo_n1.sv"
`include "svc_unused.sv"

// Takes a gfx interface (x, y, pixel) and stores it in an axi backed frame
// buffer
module svc_gfx_fb #(
    parameter H_WIDTH        = 12,
    parameter V_WIDTH        = 12,
    parameter PIXEL_WIDTH    = 12,
    parameter AXI_ADDR_WIDTH = 12,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    input  logic                   s_gfx_valid,
    input  logic [    H_WIDTH-1:0] s_gfx_x,
    input  logic [    V_WIDTH-1:0] s_gfx_y,
    input  logic [PIXEL_WIDTH-1:0] s_gfx_pixel,
    output logic                   s_gfx_ready,

    input logic [H_WIDTH-1:0] h_visible,
    input logic [V_WIDTH-1:0] v_visible,

    output logic                      m_axi_awvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    output logic [               1:0] m_axi_awburst,
    input  logic                      m_axi_awready,
    output logic                      m_axi_wvalid,
    output logic [AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    output logic                      m_axi_wlast,
    input  logic                      m_axi_wready,
    input  logic                      m_axi_bvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [               1:0] m_axi_bresp,
    output logic                      m_axi_bready
);
  logic                      aw_ready;
  logic                      w_ready;

  logic [AXI_ADDR_WIDTH-1:0] fb_addr;
  assign fb_addr     = h_visible * s_gfx_y + AXI_ADDR_WIDTH'(s_gfx_x);

  // split the gfx stream into an AW and W stream with a fifo for each
  assign s_gfx_ready = aw_ready && w_ready;

  svc_sync_fifo_n1 #(
      .DATA_WIDTH(AXI_ADDR_WIDTH)
  ) svc_sync_fifo_n1_aw_i (
      .clk  (clk),
      .rst_n(rst_n),

      .w_inc   (s_gfx_valid && s_gfx_ready),
      .w_data  (fb_addr),
      .w_full_n(aw_ready),

      .r_inc    (m_axi_awvalid && m_axi_awready),
      .r_data   (m_axi_awaddr),
      .r_empty_n(m_axi_awvalid)
  );

  svc_sync_fifo_n1 #(
      .DATA_WIDTH(AXI_DATA_WIDTH)
  ) svc_sync_fifo_n1_w_i (
      .clk  (clk),
      .rst_n(rst_n),

      .w_inc   (s_gfx_valid && s_gfx_ready),
      .w_data  (AXI_DATA_WIDTH'(s_gfx_pixel)),
      .w_full_n(w_ready),

      .r_inc    (m_axi_wvalid && m_axi_wready),
      .r_data   (m_axi_wdata),
      .r_empty_n(m_axi_wvalid)
  );

  assign m_axi_awid    = 0;
  assign m_axi_awlen   = 0;
  assign m_axi_awsize  = `SVC_MAX_AXSIZE(AXI_DATA_WIDTH);
  assign m_axi_awburst = 2'b01;

  assign m_axi_wstrb   = '1;
  assign m_axi_wlast   = 1'b1;

  // We're always ready for a response...because we ignore it ¯\_(ツ)_/¯)
  assign m_axi_bready  = 1'b1;

  `SVC_UNUSED({clk, rst_n, v_visible, m_axi_bvalid, m_axi_bid, m_axi_bresp});
endmodule
`endif
