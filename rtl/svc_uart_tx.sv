`ifndef UART_TX_SV
`define UART_TX_SV

`include "svc.sv"

module svc_uart_tx #(
    parameter CLOCK_FREQ = 100_000_000,
    parameter BAUD_RATE  = 115_200
) (
    input logic clk,
    input logic rst_n,

    input  logic       utx_en,
    input  logic [7:0] utx_data,
    output logic       utx_busy,

    output logic utx_pin
);
  // Fixed at 8-n-1 to simplify the code since that's all I expect to use
  localparam DATA_WIDTH = 8;

  // handle super fast, not realistic, 1 clock per bit for test benches,
  // in which case we need to bump to 2 cpb so we don't try to $clog2(1)
  localparam CPB_ACTUAL = CLOCK_FREQ / BAUD_RATE;
  localparam CPB = CPB_ACTUAL == 1 ? 2 : CPB_ACTUAL;
  localparam CNT_W = $clog2(CPB);
  localparam IDX_W = $clog2(DATA_WIDTH);

  // sized/typed comparison values
  localparam [CNT_W-1:0] CNT_MAX = CNT_W'(CPB - 1);
  localparam [IDX_W-1:0] BIT_MAX = IDX_W'(7);

  typedef enum {
    STATE_IDLE,
    STATE_START,
    STATE_DATA,
    STATE_STOP
  } state_t;

  state_t             state;
  state_t             state_next;

  logic   [CNT_W-1:0] cnt;
  logic   [CNT_W-1:0] cnt_next;

  logic   [IDX_W-1:0] idx;
  logic   [IDX_W-1:0] idx_next;

  logic   [      7:0] data;
  logic   [      7:0] data_next;

  // tick's advance the uart state machine, i.e. they are effectively
  // a divided clock based on the uart buad rate
  logic               tick;

  // uart clock/tick
  always_comb begin
    cnt_next = cnt;
    tick     = 1'b0;

    if (state == STATE_IDLE) begin
      cnt_next = 0;
    end else begin
      if (cnt != CNT_MAX) begin
        cnt_next = cnt + 1;
      end else begin
        cnt_next = 0;
        tick     = 1'b1;
      end
    end
  end

  always_comb begin
    state_next = state;
    idx_next   = idx;
    data_next  = data;

    utx_busy   = 1'b1;

    case (state)
      STATE_IDLE: begin
        utx_busy = 1'b0;
        utx_pin  = 1'b1;

        if (utx_en) begin
          data_next  = utx_data;
          state_next = STATE_START;
        end
      end

      STATE_START: begin
        utx_pin  = 1'b0;
        idx_next = 0;
        if (tick) begin
          state_next = STATE_DATA;
        end
      end

      STATE_DATA: begin
        utx_pin = data[idx];
        if (tick) begin
          if (idx != BIT_MAX) begin
            idx_next = idx + 1;
          end else begin
            idx_next   = 0;
            state_next = STATE_STOP;
          end
        end
      end

      STATE_STOP: begin
        utx_pin = 1'b1;
        if (tick) begin
          state_next = STATE_IDLE;
        end
      end

      default: begin
        utx_pin = 1'b1;
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  always_ff @(posedge clk) begin
    cnt  <= cnt_next;
    idx  <= idx_next;
    data <= data_next;
  end

endmodule
`endif
