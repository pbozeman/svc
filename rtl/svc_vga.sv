`ifndef SVC_VGA_SV
`define SVC_VGA_SV

//
// vga stream
//
// The en signal is so that the counters don't start running. This arguably
// could be done with the reset signal. We have to coordinate the counters
// with the first pixel. Alternative designs are to manage counter enables
// ourselves and do so on the first s_valid. Or, since this is all about
// making sure we are synced with the caller, add line and frame start inputs
// and use those to sync the caller's stream. This or the reset method are the
// least resource intensive.

module svc_vga #(
    parameter H_WIDTH     = 12,
    parameter V_WIDTH     = 12,
    parameter COLOR_WIDTH = 4
) (
    input logic clk,
    input logic rst_n,
    input logic en,

    //
    // pixel stream
    //
    input  logic                   s_valid,
    input  logic [COLOR_WIDTH-1:0] s_red,
    input  logic [COLOR_WIDTH-1:0] s_grn,
    input  logic [COLOR_WIDTH-1:0] s_blu,
    output logic                   s_ready,

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
  logic               visible;

  logic [H_WIDTH-1:0] x;
  logic [H_WIDTH-1:0] x_next;

  logic [V_WIDTH-1:0] y;
  logic [V_WIDTH-1:0] y_next;

  always_comb begin
    x_next = x;
    y_next = y;

    if (en) begin
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
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      x <= 0;
      y <= 0;
    end else begin
      x <= x_next;
      y <= y_next;
    end
  end

  assign visible   = x < h_visible && y < v_visible;
  assign s_ready   = visible;

  assign vga_hsync = (x >= h_sync_start && x < h_sync_end) ? 1'b0 : 1'b1;
  assign vga_vsync = (y >= v_sync_start && y < v_sync_end) ? 1'b0 : 1'b1;
  assign vga_red   = visible ? s_red : 0;
  assign vga_grn   = visible ? s_grn : 0;
  assign vga_blu   = visible ? s_blu : 0;

  assign vga_error = visible && !s_valid;

endmodule
`endif
