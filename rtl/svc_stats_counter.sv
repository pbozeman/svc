`ifndef SVC_STATS_COUNTER_SV
`define SVC_STATS_COUNTER_SV

`include "svc.sv"
`include "svc_accumulator.sv"

// counter stat

module svc_stats_counter #(
    parameter STAT_WIDTH  = 32,
    parameter STAT_STAGES = 4
) (
    input logic clk,
    input logic rst_n,

    input logic stat_clear,
    input logic stat_inc,
    input logic stat_dec,

    output logic [STAT_WIDTH-1:0] stat_cnt,
    output logic [STAT_WIDTH-1:0] stat_max
);
  logic                  acc_en;
  logic [STAT_WIDTH-1:0] acc_val;

  svc_accumulator #(
      .WIDTH (STAT_WIDTH),
      .STAGES(STAT_STAGES)
  ) svc_acc_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (stat_clear),
      .en   (acc_en),
      .val  (acc_val),
      .acc  (stat_cnt)
  );

  always_comb begin
    case ({
      stat_dec, stat_inc
    })
      2'b01: begin
        acc_en  = 1;
        acc_val = 1;
      end

      2'b10: begin
        acc_en  = 1;
        acc_val = -1;
      end

      default: begin
        acc_en  = 0;
        acc_val = 0;
      end
    endcase
  end

  // Note: max is implicitly pipelined because the accumulator
  // registers its output
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
