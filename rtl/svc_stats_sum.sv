`ifndef SVC_STATS_SUM_SV
`define SVC_STATS_SUM_SV

`include "svc.sv"
`include "svc_accumulator.sv"

// This is a direct pass through to the accumulator, but can be used
// along side other stat modules with consistent naming.

module svc_stats_sum #(
    parameter WIDTH      = 8,
    parameter STAT_WIDTH = 32,
    parameter STAGES     = 4
) (
    input logic clk,
    input logic rst_n,

    input logic             clr,
    input logic             en,
    input logic [WIDTH-1:0] val,

    output logic [STAT_WIDTH-1:0] sum
);
  svc_accumulator #(
      .WIDTH (STAT_WIDTH),
      .STAGES(STAGES)
  ) svc_acc_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (clr),
      .en   (en),
      .val  (STAT_WIDTH'(val)),
      .acc  (sum)
  );
endmodule
`endif
