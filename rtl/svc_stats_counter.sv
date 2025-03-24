`ifndef SVC_STATS_COUNTER_SV
`define SVC_STATS_COUNTER_SV

`include "svc.sv"

// counter stat

module svc_stats_counter #(
    parameter STAT_WIDTH = 32
) (
    input logic clk,
    input logic rst_n,

    input logic stat_clear,
    input logic stat_inc,
    input logic stat_dec,

    output logic [STAT_WIDTH-1:0] stat_cnt,
    output logic [STAT_WIDTH-1:0] stat_max
);

  logic [STAT_WIDTH-1:0] stat_cnt_next;

  always_comb begin
    stat_cnt_next = stat_cnt;

    case ({
      stat_dec, stat_inc
    })
      2'b01: begin
        stat_cnt_next = stat_cnt + 1;
      end

      2'b10: begin
        stat_cnt_next = stat_cnt - 1;
      end

      default: begin
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      stat_cnt <= 0;
    end else begin
      stat_cnt <= stat_cnt_next;
    end
  end

  // Pipeline the max stat by using stat_cnt rather than stat_cnt_next.
  // This was necessary to meet timing on the ice40 at 100mhz, with 32 bit
  // counters.
  always_ff @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      stat_max <= 0;
    end else begin
      if (stat_cnt > stat_max) begin
        stat_max <= stat_cnt;
      end
    end
  end

endmodule
`endif
