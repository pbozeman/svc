`ifndef SVC_STATS_SUM_SV
`define SVC_STATS_SUM_SV

`include "svc.sv"
`include "svc_accumulator.sv"
`include "svc_stats.sv"

// This is a direct pass through to the accumulator, but can be used
// along side other stat modules with consistent naming.

module svc_stats_sum #(
    parameter WIDTH          = 32,
    parameter STAT_WIDTH     = 32,
    parameter BITS_PER_STAGE = `SVC_PIPE_BPS
) (
    input logic clk,

    input logic             clr,
    input logic             en,
    input logic [WIDTH-1:0] val,

    output logic [STAT_WIDTH-1:0] sum
);
  svc_accumulator #(
      .WIDTH         (STAT_WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) svc_acc_i (
      .clk(clk),
      .clr(clr),
      .en (en),
      .val(STAT_WIDTH'(val)),
      .acc(sum)
  );
endmodule
`endif
