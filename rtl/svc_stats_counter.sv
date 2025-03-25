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

    input logic clr,
    input logic inc,
    input logic dec,

    output logic [STAT_WIDTH-1:0] cnt
);
  logic                  acc_en;
  logic [STAT_WIDTH-1:0] acc_val;

  svc_accumulator #(
      .WIDTH (STAT_WIDTH),
      .STAGES(STAT_STAGES)
  ) svc_acc_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (clr),
      .en   (acc_en),
      .val  (acc_val),
      .acc  (cnt)
  );

  always_comb begin
    case ({
      dec, inc
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

endmodule
`endif
