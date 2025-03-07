`include "svc_unit.sv"

`include "svc_pix_vga.sv"
`include "svc_vga_mode.sv"

// TODO: add x/y and resync tests

// verilator lint_off: UNUSEDSIGNAL
module svc_pix_vga_tb;
  localparam AW = 16;
  localparam HW = 12;
  localparam VW = 12;
  localparam CW = 4;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic          m_pix_valid;
  logic [CW-1:0] m_pix_red;
  logic [CW-1:0] m_pix_grn;
  logic [CW-1:0] m_pix_blu;
  logic [HW-1:0] m_pix_x;
  logic [VW-1:0] m_pix_y;
  logic [AW-1:0] m_pix_addr;
  logic          m_pix_ready;

  logic [HW-1:0] h_visible;
  logic [HW-1:0] h_sync_start;
  logic [HW-1:0] h_sync_end;
  logic [HW-1:0] h_line_end;

  logic [HW-1:0] v_visible;
  logic [HW-1:0] v_sync_start;
  logic [HW-1:0] v_sync_end;
  logic [HW-1:0] v_frame_end;

  logic          vga_hsync;
  logic          vga_vsync;
  logic [CW-1:0] vga_red;
  logic [CW-1:0] vga_grn;
  logic [CW-1:0] vga_blu;
  logic          vga_error;

  svc_pix_vga #(
      .H_WIDTH    (HW),
      .V_WIDTH    (VW),
      .COLOR_WIDTH(CW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_pix_valid(m_pix_valid),
      .s_pix_red  (m_pix_red),
      .s_pix_grn  (m_pix_grn),
      .s_pix_blu  (m_pix_blu),
      .s_pix_x    (m_pix_x),
      .s_pix_y    (m_pix_y),
      .s_pix_addr (m_pix_addr),
      .s_pix_ready(m_pix_ready),

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

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_pix_valid <= 1'b0;
      m_pix_red   <= 0;
      m_pix_grn   <= 0;
      m_pix_blu   <= 0;

      m_pix_x     <= 0;
      m_pix_y     <= 0;
      m_pix_addr  <= 0;
    end else begin
      if (m_pix_valid && m_pix_ready) begin
        m_pix_addr <= m_pix_addr + 1;

        if (m_pix_x < h_visible - 1) begin
          m_pix_x <= m_pix_x + 1;
        end else begin
          m_pix_x <= 0;
          if (m_pix_y < v_visible - 1) begin
            m_pix_y <= m_pix_y + 1;
          end else begin
            m_pix_y    <= 0;
            m_pix_addr <= 0;
          end
        end
      end
    end
  end

  task automatic check_line;
    input logic vblank;
    input logic vsync;

    for (int i = 0; i < h_visible; i++) begin
      if (!vblank) begin
        `CHECK_EQ(vga_red, 4'h2);
        `CHECK_EQ(vga_grn, 4'h4);
        `CHECK_EQ(vga_blu, 4'h8);
      end else begin
        `CHECK_EQ(vga_red, 0);
        `CHECK_EQ(vga_grn, 0);
        `CHECK_EQ(vga_blu, 0);
      end

      `CHECK_EQ(vga_hsync, 1'b1);
      `CHECK_EQ(vga_vsync, vsync);
      `CHECK_FALSE(vga_error);

      `TICK(clk);
    end

    for (int i = 0; i < `VGA_MODE_640x480_H_FRONT_PORCH; i++) begin
      `CHECK_EQ(vga_red, 0);
      `CHECK_EQ(vga_grn, 0);
      `CHECK_EQ(vga_blu, 0);

      `CHECK_EQ(vga_hsync, 1'b1);
      `CHECK_EQ(vga_vsync, vsync);
      `CHECK_FALSE(vga_error);

      `TICK(clk);
    end

    for (int i = 0; i < `VGA_MODE_640x480_H_SYNC_PULSE; i++) begin
      `CHECK_EQ(vga_red, 0);
      `CHECK_EQ(vga_grn, 0);
      `CHECK_EQ(vga_blu, 0);

      `CHECK_EQ(vga_hsync, 1'b0);
      `CHECK_EQ(vga_vsync, vsync);
      `CHECK_FALSE(vga_error);

      `TICK(clk);
    end

    for (
        int i = 0;
        i < (`VGA_MODE_640x480_H_WHOLE_LINE - `VGA_MODE_640x480_H_SYNC_END);
        i++
    ) begin
      `CHECK_EQ(vga_red, 0);
      `CHECK_EQ(vga_grn, 0);
      `CHECK_EQ(vga_blu, 0);

      `CHECK_EQ(vga_hsync, 1'b1);
      `CHECK_EQ(vga_vsync, vsync);
      `CHECK_FALSE(vga_error);

      `TICK(clk);
    end
  endtask

  task automatic test_line;
    m_pix_red    = 4'h2;
    m_pix_grn    = 4'h4;
    m_pix_blu    = 4'h8;

    h_visible    = `VGA_MODE_640x480_H_VISIBLE;
    h_sync_start = `VGA_MODE_640x480_H_SYNC_START;
    h_sync_end   = `VGA_MODE_640x480_H_SYNC_END;
    h_line_end   = `VGA_MODE_640x480_H_LINE_END;

    v_visible    = `VGA_MODE_640x480_V_VISIBLE;
    v_sync_start = `VGA_MODE_640x480_V_SYNC_START;
    v_sync_end   = `VGA_MODE_640x480_V_SYNC_END;
    v_frame_end  = `VGA_MODE_640x480_V_FRAME_END;

    // just a weird amount of waiting to make sure we sync at startup
    for (int i = 0; i < 5; i++) begin
      `TICK(clk);
    end

    m_pix_valid = 1'b1;

    `CHECK_WAIT_FOR(clk, uut.visible, 3);
    `TICK(clk);
    check_line(1'b0, 1'b1);
  endtask

  task automatic test_frame;
    m_pix_red    = 4'h2;
    m_pix_grn    = 4'h4;
    m_pix_blu    = 4'h8;

    h_visible    = `VGA_MODE_640x480_H_VISIBLE;
    h_sync_start = `VGA_MODE_640x480_H_SYNC_START;
    h_sync_end   = `VGA_MODE_640x480_H_SYNC_END;
    h_line_end   = `VGA_MODE_640x480_H_LINE_END;

    v_visible    = `VGA_MODE_640x480_V_VISIBLE;
    v_sync_start = `VGA_MODE_640x480_V_SYNC_START;
    v_sync_end   = `VGA_MODE_640x480_V_SYNC_END;
    v_frame_end  = `VGA_MODE_640x480_V_FRAME_END;

    // just a weird amount of waiting to make sure we sync at startup
    for (int i = 0; i < 7; i++) begin
      `TICK(clk);
    end

    m_pix_valid = 1'b1;
    `CHECK_WAIT_FOR(clk, uut.visible, 3);
    `TICK(clk);

    for (int i = 0; i < `VGA_MODE_640x480_V_VISIBLE; i++) begin
      check_line(1'b0, 1'b1);
    end

    for (int i = 0; i < `VGA_MODE_640x480_V_FRONT_PORCH; i++) begin
      check_line(1'b1, 1'b1);
    end

    for (int i = 0; i < `VGA_MODE_640x480_V_SYNC_PULSE; i++) begin
      check_line(1'b1, 1'b0);
    end

    for (
        int i = 0;
        i < (`VGA_MODE_640x480_V_WHOLE_FRAME - `VGA_MODE_640x480_V_SYNC_END);
        i++
    ) begin
      check_line(1'b1, 1'b1);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_pix_vga_tb, 500000);
  `TEST_CASE(test_line);
  `TEST_CASE(test_frame);
  `TEST_SUITE_END();
endmodule
