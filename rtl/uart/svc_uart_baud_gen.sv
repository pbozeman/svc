`ifndef SVC_UART_BAUD_GEN_SV
`define SVC_UART_BAUD_GEN_SV

`include "svc.sv"

// TICK_DIV can be used to adjust the phase. If 1, ticks happen at the end of
// the full cycle. If 2, they happen at the mid point. This is useful for mid
// bit sampling for receive baud_gen.

module svc_uart_baud_gen #(
    parameter CLOCK_FREQ = 100_000_000,
    parameter BAUD_RATE  = 115_200,
    parameter TICK_DIV   = 1
) (
    input  logic clk,
    input  logic rst_n,
    output logic tick
);
  // Handle super fast, not realistic, 1 clock per bit for test benches,
  // in which case we need to bump to 2 cpb so we don't try to $clog2(1)
  localparam CPB_ACTUAL = CLOCK_FREQ / BAUD_RATE;
  localparam CPB = CPB_ACTUAL == 1 ? 2 : CPB_ACTUAL;
  localparam CNT_W = $clog2(CPB);

  logic [CNT_W-1:0] cnt;
  logic [CNT_W-1:0] cnt_next;

  localparam [CNT_W-1:0] CNT_MAX = CNT_W'(CPB - 1);
  localparam [CNT_W-1:0] CNT_TICK = CNT_W'(CPB / TICK_DIV);

  // Baud rate generation logic
  always_comb begin
    cnt_next = cnt;
    tick     = 1'b0;

    if (cnt != CNT_MAX) begin
      cnt_next = cnt + 1;
      if (TICK_DIV > 1) begin
        if (cnt == CNT_TICK) begin
          tick = 1'b1;
        end
      end
    end else begin
      cnt_next = '0;
      if (TICK_DIV == 1) begin
        tick = 1'b1;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      cnt <= '0;
    end else begin
      cnt <= cnt_next;
    end
  end

endmodule
`endif
