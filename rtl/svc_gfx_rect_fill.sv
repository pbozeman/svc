`ifndef SVC_GFX_RECT_FILL_SV
`define SVC_GFX_RECT_FILL_SV

`include "svc.sv"

// ✨🤖✨ vibe coded with claude

module svc_gfx_rect_fill #(
    parameter int H_WIDTH     = 12,
    parameter int V_WIDTH     = 12,
    parameter int PIXEL_WIDTH = 12
) (
    input logic clk,
    input logic rst_n,

    // control interface
    input  logic start,
    output logic done,

    // rectangle parameters
    input logic [    H_WIDTH-1:0] x0,
    input logic [    V_WIDTH-1:0] y0,
    input logic [    H_WIDTH-1:0] x1,
    input logic [    V_WIDTH-1:0] y1,
    input logic [PIXEL_WIDTH-1:0] color,

    // graphics interface (manager)
    output logic                   m_gfx_valid,
    output logic [    H_WIDTH-1:0] m_gfx_x,
    output logic [    V_WIDTH-1:0] m_gfx_y,
    output logic [PIXEL_WIDTH-1:0] m_gfx_pixel,
    input  logic                   m_gfx_ready
);

  typedef enum {
    STATE_IDLE,
    STATE_SETUP,
    STATE_CLEARING,
    STATE_DONE
  } state_t;

  state_t                   state;
  state_t                   state_next;

  // Scan variables
  logic   [    H_WIDTH-1:0] x_min;
  logic   [    H_WIDTH-1:0] x_max;
  logic   [    H_WIDTH-1:0] x_min_next;
  logic   [    H_WIDTH-1:0] x_max_next;

  logic   [    V_WIDTH-1:0] y_min;
  logic   [    V_WIDTH-1:0] y_max;
  logic   [    V_WIDTH-1:0] y_min_next;
  logic   [    V_WIDTH-1:0] y_max_next;

  logic   [    H_WIDTH-1:0] curr_x;
  logic   [    H_WIDTH-1:0] curr_x_next;

  logic   [    V_WIDTH-1:0] curr_y;
  logic   [    V_WIDTH-1:0] curr_y_next;

  logic   [PIXEL_WIDTH-1:0] pixel_color;
  logic   [PIXEL_WIDTH-1:0] pixel_color_next;

  // Next state logic
  always_comb begin
    state_next       = state;

    x_min_next       = x_min;
    x_max_next       = x_max;
    y_min_next       = y_min;
    y_max_next       = y_max;

    curr_x_next      = curr_x;
    curr_y_next      = curr_y;

    pixel_color_next = pixel_color;

    done             = 1'b0;
    m_gfx_valid      = 1'b0;
    m_gfx_x          = curr_x;
    m_gfx_y          = curr_y;
    m_gfx_pixel      = pixel_color;

    case (state)
      STATE_IDLE: begin
        if (start) begin
          state_next = STATE_SETUP;
        end
      end

      STATE_SETUP: begin
        // Ensure x_min <= x_max and y_min <= y_max
        x_min_next       = (x0 <= x1) ? x0 : x1;
        x_max_next       = (x0 <= x1) ? x1 : x0;
        y_min_next       = (y0 <= y1) ? y0 : y1;
        y_max_next       = (y0 <= y1) ? y1 : y0;

        curr_x_next      = (x0 <= x1) ? x0 : x1;
        curr_y_next      = (y0 <= y1) ? y0 : y1;

        pixel_color_next = color;

        state_next       = STATE_CLEARING;
      end

      STATE_CLEARING: begin
        // Valid pixel to draw
        m_gfx_valid = 1'b1;

        if (m_gfx_ready) begin
          // Move to next pixel
          if (curr_x < x_max) begin
            // Move right
            curr_x_next = curr_x + 1'b1;
          end else begin
            // Move to beginning of next row
            curr_x_next = x_min;

            if (curr_y < y_max) begin
              // Move to next row
              curr_y_next = curr_y + 1'b1;
            end else begin
              // Finished all rows
              state_next = STATE_DONE;
            end
          end
        end
      end

      STATE_DONE: begin
        done = 1'b1;
        if (!start) begin
          state_next = STATE_IDLE;
        end
      end
    endcase
  end

  // Update state
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  // Update state
  always_ff @(posedge clk) begin
    x_min       <= x_min_next;
    x_max       <= x_max_next;
    y_min       <= y_min_next;
    y_max       <= y_max_next;

    curr_x      <= curr_x_next;
    curr_y      <= curr_y_next;

    pixel_color <= pixel_color_next;
  end

endmodule

`endif
