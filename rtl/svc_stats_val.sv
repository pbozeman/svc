`ifndef SVC_STATS_VAL_SV
`define SVC_STATS_VAL_SV

`include "svc.sv"
`include "svc_stats.sv"
`include "svc_stats_max.sv"
`include "svc_stats_min.sv"
`include "svc_stats_sum.sv"

module svc_stats_val #(
    parameter WIDTH          = 32,
    parameter STAT_WIDTH     = 32,
    parameter BITS_PER_STAGE = `SVC_PIPE_BPS
) (
    input  logic                  clk,
    input  logic                  rst_n,
    input  logic                  clr,
    input  logic                  en,
    input  logic [     WIDTH-1:0] val,
    output logic [     WIDTH-1:0] min,
    output logic [     WIDTH-1:0] max,
    output logic [STAT_WIDTH-1:0] sum
);
  svc_stats_min #(
      .WIDTH         (WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) svc_stats_min_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (clr),
      .en   (en),
      .val  (val),
      .min  (min)
  );

  svc_stats_max #(
      .WIDTH         (WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) svc_stats_max_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (clr),
      .en   (en),
      .val  (val),
      .max  (max)
  );

  svc_stats_sum #(
      .WIDTH         (WIDTH),
      .STAT_WIDTH    (STAT_WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) svc_stats_sum_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (clr),
      .en   (en),
      .val  (val),
      .sum  (sum)
  );

endmodule
`endif
