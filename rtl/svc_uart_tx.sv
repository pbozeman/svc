`ifndef SVC_UART_TX_SV
`define SVC_UART_TX_SV

`include "svc.sv"
`include "svc_uart_baud_gen.sv"

module svc_uart_tx #(
    parameter CLOCK_FREQ = 100_000_000,
    parameter BAUD_RATE  = 115_200
) (
    input logic clk,
    input logic rst_n,

    input  logic       utx_valid,
    input  logic [7:0] utx_data,
    output logic       utx_ready,

    output logic utx_pin
);
  // Fixed at 8-n-1 to simplify the code since that's all I expect to use
  localparam DATA_WIDTH = 8;
  localparam IDX_W = $clog2(DATA_WIDTH);
  localparam [IDX_W-1:0] BIT_MAX = IDX_W'(7);

  typedef enum {
    STATE_IDLE,
    STATE_START,
    STATE_DATA,
    STATE_STOP
  } state_t;

  state_t             state;
  state_t             state_next;
  logic   [IDX_W-1:0] idx;
  logic   [IDX_W-1:0] idx_next;
  logic   [      7:0] data;
  logic   [      7:0] data_next;
  logic               b_rst_n;
  logic               tick;

  svc_uart_baud_gen #(
      .CLOCK_FREQ(CLOCK_FREQ),
      .BAUD_RATE (BAUD_RATE)
  ) baud_gen (
      .clk  (clk),
      .rst_n(b_rst_n),
      .tick (tick)
  );

  always_comb begin
    state_next = state;
    idx_next   = idx;
    data_next  = data;
    utx_ready  = 1'b0;
    b_rst_n    = 1'b1;

    case (state)
      STATE_IDLE: begin
        utx_ready = 1'b1;
        utx_pin   = 1'b1;
        b_rst_n   = 1'b0;

        if (utx_valid && utx_ready) begin
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
      idx   <= '0;
      data  <= '0;
    end else begin
      state <= state_next;
      idx   <= idx_next;
      data  <= data_next;
    end
  end

endmodule
`endif
