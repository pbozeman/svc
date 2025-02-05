`ifndef SVC_PIX_VGA_SV
`define SVC_PIX_VGA_SV

//
// Pixel stream to vga signals
//

module svc_pix_vga #(
    parameter H_WIDTH     = 12,
    parameter V_WIDTH     = 12,
    parameter COLOR_WIDTH = 4
) (
    input logic clk,
    input logic rst_n,

    //
    // pixel stream
    //
    input  logic                   s_pix_valid,
    input  logic [COLOR_WIDTH-1:0] s_pix_red,
    input  logic [COLOR_WIDTH-1:0] s_pix_grn,
    input  logic [COLOR_WIDTH-1:0] s_pix_blu,
    output logic                   s_pix_ready,

    //
    // video mode
    // TODO: sync polarity
    //
    input logic [H_WIDTH-1:0] h_visible,
    input logic [H_WIDTH-1:0] h_sync_start,
    input logic [H_WIDTH-1:0] h_sync_end,
    input logic [H_WIDTH-1:0] h_line_end,

    input logic [V_WIDTH-1:0] v_visible,
    input logic [V_WIDTH-1:0] v_sync_start,
    input logic [V_WIDTH-1:0] v_sync_end,
    input logic [V_WIDTH-1:0] v_frame_end,

    //
    // vga signals
    //
    output logic                   vga_hsync,
    output logic                   vga_vsync,
    output logic [COLOR_WIDTH-1:0] vga_red,
    output logic [COLOR_WIDTH-1:0] vga_grn,
    output logic [COLOR_WIDTH-1:0] vga_blu,
    output logic                   vga_error
);
  logic               enabled;
  logic               visible;

  logic [H_WIDTH-1:0] x;
  logic [H_WIDTH-1:0] x_next;

  logic [V_WIDTH-1:0] y;
  logic [V_WIDTH-1:0] y_next;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      enabled <= 1'b0;
    end else begin
      enabled <= enabled || s_pix_valid;
    end
  end

  always_comb begin
    x_next = x;
    y_next = y;

    if (x < h_line_end) begin
      x_next = x + 1;
    end else begin
      x_next = 0;

      if (y < v_frame_end) begin
        y_next = y + 1;
      end else begin
        y_next = 0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      x <= 0;
      y <= 0;
    end else begin
      if (enabled) begin
        x <= x_next;
        y <= y_next;
      end
    end
  end

  assign visible     = enabled && x < h_visible && y < v_visible;
  assign s_pix_ready = visible;

  assign vga_hsync   = (x >= h_sync_start && x < h_sync_end) ? 1'b0 : 1'b1;
  assign vga_vsync   = (y >= v_sync_start && y < v_sync_end) ? 1'b0 : 1'b1;
  assign vga_red     = visible ? s_pix_red : 0;
  assign vga_grn     = visible ? s_pix_grn : 0;
  assign vga_blu     = visible ? s_pix_blu : 0;

  assign vga_error   = visible && !s_pix_valid;

endmodule
`endif
