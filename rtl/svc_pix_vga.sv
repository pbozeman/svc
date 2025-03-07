`ifndef SVC_PIX_VGA_SV
`define SVC_PIX_VGA_SV

`include "svc_skidbuf.sv"

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
    input  logic [    H_WIDTH-1:0] s_pix_x,
    input  logic [    V_WIDTH-1:0] s_pix_y,
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
  localparam CW = COLOR_WIDTH;
  localparam HW = H_WIDTH;
  localparam VW = V_WIDTH;

  // pixel + x/y + v mode settings + h mode settings
  localparam SB_DATA_WIDTH = CW * 3 + HW * 5 + VW * 5;

  logic          sb_valid;
  logic [CW-1:0] sb_pix_red;
  logic [CW-1:0] sb_pix_grn;
  logic [CW-1:0] sb_pix_blu;

  // verilator lint_off: UNUSEDSIGNAL
  // FIXME: use these for sync
  logic [HW-1:0] sb_pix_x;
  logic [VW-1:0] sb_pix_y;
  // verilator lint_on: UNUSEDSIGNAL

  logic [HW-1:0] sb_h_visible;
  logic [HW-1:0] sb_h_sync_start;
  logic [HW-1:0] sb_h_sync_end;
  logic [HW-1:0] sb_h_line_end;

  logic [VW-1:0] sb_v_visible;
  logic [VW-1:0] sb_v_sync_start;
  logic [VW-1:0] sb_v_sync_end;
  logic [VW-1:0] sb_v_frame_end;

  logic          sb_ready;

  logic          enabled;
  logic          visible;

  logic [HW-1:0] x;
  logic [HW-1:0] x_next;

  logic [VW-1:0] y;
  logic [VW-1:0] y_next;

  // TODO: could optimize by converting to x/y to eol, eof
  svc_skidbuf #(
      .DATA_WIDTH(SB_DATA_WIDTH),
      .OPT_OUTREG(1)
  ) svc_skidbuf_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_pix_valid),
      .i_data({
        s_pix_red,
        s_pix_grn,
        s_pix_blu,
        s_pix_x,
        s_pix_y,
        h_visible,
        h_sync_start,
        h_sync_end,
        h_line_end,
        v_visible,
        v_sync_start,
        v_sync_end,
        v_frame_end
      }),
      .o_ready(s_pix_ready),

      .i_ready(sb_ready),
      .o_data({
        sb_pix_red,
        sb_pix_grn,
        sb_pix_blu,
        sb_pix_x,
        sb_pix_y,
        sb_h_visible,
        sb_h_sync_start,
        sb_h_sync_end,
        sb_h_line_end,
        sb_v_visible,
        sb_v_sync_start,
        sb_v_sync_end,
        sb_v_frame_end
      }),
      .o_valid(sb_valid)
  );

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      enabled <= 1'b0;
    end else begin
      enabled <= enabled || sb_valid;
    end
  end

  always_comb begin
    x_next = x;
    y_next = y;

    // TODO: resync using sb_x/y

    if (x < sb_h_line_end) begin
      x_next = x + 1;
    end else begin
      x_next = 0;

      if (y < sb_v_frame_end) begin
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

  assign visible = enabled && x < sb_h_visible && y < sb_v_visible;

  always_ff @(posedge clk) begin
    sb_ready  <= visible;

    vga_hsync <= (x >= sb_h_sync_start && x < sb_h_sync_end) ? 1'b0 : 1'b1;
    vga_vsync <= (y >= sb_v_sync_start && y < sb_v_sync_end) ? 1'b0 : 1'b1;
    vga_red   <= visible ? sb_pix_red : 0;
    vga_grn   <= visible ? sb_pix_grn : 0;
    vga_blu   <= visible ? sb_pix_blu : 0;

    vga_error <= visible && !sb_valid;
  end

endmodule
`endif
