`ifndef SVC_STATS_VAL_SV
`define SVC_STATS_VAL_SV

`include "svc.sv"

// val stat

module svc_stats_val #(
    parameter WIDTH      = 8,
    parameter STAT_WIDTH = 32
) (
    input logic clk,
    input logic rst_n,

    input logic             stat_clear,
    input logic             stat_en,
    input logic [WIDTH-1:0] stat_val,

    output logic [     WIDTH-1:0] stat_min,
    output logic [     WIDTH-1:0] stat_max,
    output logic [STAT_WIDTH-1:0] stat_sum
);

  always_ff @(posedge clk) begin
    if (!rst_n || stat_clear) begin
      stat_min <= '1;
      stat_max <= 0;
      stat_sum <= 0;
    end else begin
      if (stat_en) begin
        if (stat_val < stat_min) begin
          stat_min <= stat_val;
        end

        if (stat_val > stat_max) begin
          stat_max <= stat_val;
        end

        stat_sum <= STAT_WIDTH'(stat_val) + stat_sum;
      end
    end
  end

endmodule
`endif
