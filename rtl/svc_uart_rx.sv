`ifndef SVC_UART_RX_SV
`define SVC_UART_RX_SV

`include "svc.sv"
`include "svc_uart_baud_gen.sv"

module svc_uart_rx #(
    parameter CLOCK_FREQ = 100_000_000,
    parameter BAUD_RATE  = 115_200
) (
    input logic clk,
    input logic rst_n,

    output logic       urx_valid,
    output logic [7:0] urx_data,

    input logic urx_pin
);
  localparam DATA_WIDTH = 8;
  localparam IDX_W = $clog2(DATA_WIDTH);
  localparam [IDX_W-1:0] BIT_MAX = IDX_W'(7);

  typedef enum {
    STATE_IDLE,
    STATE_START,
    STATE_DATA,
    STATE_STOP,
    STATE_VALID
  } state_t;

  state_t             state;
  state_t             state_next;

  logic   [IDX_W-1:0] idx;
  logic   [IDX_W-1:0] idx_next;

  logic   [      7:0] data;
  logic   [      7:0] data_next;

  logic               b_rst_n;
  logic               tick;

  logic               urx_valid_next;

  svc_uart_baud_gen #(
      .CLOCK_FREQ(CLOCK_FREQ),
      .BAUD_RATE (BAUD_RATE),
      .TICK_DIV  (2)
  ) baud_gen (
      .clk  (clk),
      .rst_n(b_rst_n),
      .tick (tick)
  );

  always_comb begin
    state_next     = state;
    idx_next       = idx;
    data_next      = data;
    urx_valid_next = urx_valid;
    b_rst_n        = 1'b1;

    case (state)
      STATE_IDLE: begin
        b_rst_n = 1'b0;

        if (urx_pin == 1'b0) begin
          state_next = STATE_START;
          idx_next   = 0;
        end
      end

      STATE_START: begin
        if (tick) begin
          if (urx_pin == 1'b0) begin
            state_next = STATE_DATA;
          end else begin
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_DATA: begin
        if (tick) begin
          data_next[idx] = urx_pin;

          if (idx != BIT_MAX) begin
            idx_next = idx + 1;
          end else begin
            idx_next   = 0;
            state_next = STATE_STOP;
          end
        end
      end

      STATE_STOP: begin
        if (tick) begin
          if (urx_pin) begin
            state_next     = STATE_VALID;
            urx_valid_next = 1'b1;
          end else begin
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_VALID: begin
        urx_valid_next = 1'b0;
        state_next     = STATE_IDLE;
      end

      default: begin
        state_next = STATE_IDLE;
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state     <= STATE_IDLE;
      idx       <= '0;
      data      <= '0;
      urx_valid <= 1'b0;
    end else begin
      state     <= state_next;
      idx       <= idx_next;
      data      <= data_next;
      urx_valid <= urx_valid_next;
    end
  end

  assign urx_data = data;

endmodule
`endif
