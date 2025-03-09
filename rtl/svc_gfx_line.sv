`ifndef SVC_GFX_LINE_SV
`define SVC_GFX_LINE_SV

`include "svc.sv"

// ✨🤖✨ vibe coded with claude

// Implements Bresenham's line algorithm, drawing a line between two points
// Acts as a manager on the gfx interface that can be connected to svc_gfx_fb
module svc_gfx_line #(
    parameter H_WIDTH     = 12,
    parameter V_WIDTH     = 12,
    parameter PIXEL_WIDTH = 12
) (
    input logic clk,
    input logic rst_n,

    // Control interface
    input  logic                   start,
    output logic                   done,
    input  logic [    H_WIDTH-1:0] x0,
    input  logic [    V_WIDTH-1:0] y0,
    input  logic [    H_WIDTH-1:0] x1,
    input  logic [    V_WIDTH-1:0] y1,
    input  logic [PIXEL_WIDTH-1:0] color,

    // Graphics output interface (manager)
    output logic                   m_gfx_valid,
    output logic [    H_WIDTH-1:0] m_gfx_x,
    output logic [    V_WIDTH-1:0] m_gfx_y,
    output logic [PIXEL_WIDTH-1:0] m_gfx_pixel,
    input  logic                   m_gfx_ready
);

  // State machine states
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_SETUP,
    STATE_DRAWING,
    STATE_DONE
  } state_t;

  state_t                    state;
  state_t                    state_next;

  // Bresenham algorithm variables
  logic signed [  H_WIDTH:0] dx;
  logic signed [  H_WIDTH:0] dx_next;

  logic signed [  V_WIDTH:0] dy;
  logic signed [  V_WIDTH:0] dy_next;

  logic signed [  V_WIDTH:0] error;
  logic signed [  V_WIDTH:0] error_next;

  logic        [H_WIDTH-1:0] current_x;
  logic        [H_WIDTH-1:0] current_x_next;

  logic        [V_WIDTH-1:0] current_y;
  logic        [V_WIDTH-1:0] current_y_next;

  logic                      step_x;
  logic                      step_x_next;

  logic                      step_y;
  logic                      step_y_next;

  logic                      steep;
  logic                      steep_next;

  logic                      last_pixel;
  logic                      last_pixel_next;

  // State machine and algorithm implementation
  always_comb begin
    // Default values - maintain current state
    state_next      = state;
    dx_next         = dx;
    dy_next         = dy;
    error_next      = error;
    current_x_next  = current_x;
    current_y_next  = current_y;
    step_x_next     = step_x;
    step_y_next     = step_y;
    steep_next      = steep;
    last_pixel_next = last_pixel;

    m_gfx_valid     = 1'b0;
    m_gfx_x         = steep ? current_y : current_x;
    m_gfx_y         = steep ? current_x : current_y;
    m_gfx_pixel     = color;
    done            = 1'b0;

    case (state)
      STATE_IDLE: begin
        if (start) begin
          state_next = STATE_SETUP;
        end
      end

      STATE_SETUP: begin
        // Determine if line is steep (|dy| > |dx|)
        steep_next = ($signed({1'b0, y1}) - $signed({1'b0, y0})) >
            ($signed({1'b0, x1}) - $signed({1'b0, x0})) ? 1'b1 : 1'b0;

        // If steep, swap x and y coordinates
        if (steep_next) begin
          // Initialize with swapped coordinates for steep line
          current_x_next = y0;
          current_y_next = x0;

          // Calculate dx and dy for swapped coordinates
          dx_next        = y1 > y0 ? {1'b0, y1 - y0} : {1'b0, y0 - y1};
          dy_next        = x1 > x0 ? {1'b0, x1 - x0} : {1'b0, x0 - x1};

          // Determine step direction
          step_x_next    = y1 > y0 ? 1'b1 : 1'b0;
          step_y_next    = x1 > x0 ? 1'b1 : 1'b0;
        end else begin
          // Initialize for non-steep line
          current_x_next = x0;
          current_y_next = y0;

          // Calculate dx and dy
          dx_next        = x1 > x0 ? {1'b0, x1 - x0} : {1'b0, x0 - x1};
          dy_next        = y1 > y0 ? {1'b0, y1 - y0} : {1'b0, y0 - y1};

          // Determine step direction
          step_x_next    = x1 > x0 ? 1'b1 : 1'b0;
          step_y_next    = y1 > y0 ? 1'b1 : 1'b0;
        end

        // Initialize error
        error_next      = (dx_next >> 1);

        // Check if this is a single pixel
        last_pixel_next = (dx_next == 0 && dy_next == 0) ? 1'b1 : 1'b0;

        state_next      = STATE_DRAWING;
      end

      STATE_DRAWING: begin
        m_gfx_valid = 1'b1;

        if (m_gfx_ready) begin
          if (last_pixel) begin
            state_next = STATE_DONE;
          end else begin
            // Calculate next position
            error_next = error - dy;

            // Update y if needed
            if ($signed(error_next) < 0) begin
              current_y_next = step_y ? current_y + 1'b1 : current_y - 1'b1;
              error_next     = error_next + dx;
            end

            // Always update x
            current_x_next = step_x ? current_x + 1'b1 : current_x - 1'b1;

            // Check if this is the last pixel
            if (steep) begin
              last_pixel_next = current_x_next == y1;
            end else begin
              last_pixel_next = current_x_next == x1;
            end
          end
        end
      end

      STATE_DONE: begin
        state_next = STATE_IDLE;
        done       = 1'b1;
      end

      default: state_next = STATE_IDLE;
    endcase
  end

  // State and variable updates with synchronous reset
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state      <= STATE_IDLE;

      dx         <= 0;
      dy         <= 0;
      error      <= 0;

      current_x  <= 0;
      current_y  <= 0;

      step_x     <= 0;
      step_y     <= 0;

      steep      <= 0;
      last_pixel <= 0;
    end else begin
      state      <= state_next;

      dx         <= dx_next;
      dy         <= dy_next;
      error      <= error_next;

      current_x  <= current_x_next;
      current_y  <= current_y_next;

      step_x     <= step_x_next;
      step_y     <= step_y_next;

      steep      <= steep_next;
      last_pixel <= last_pixel_next;
    end
  end
endmodule
`endif
