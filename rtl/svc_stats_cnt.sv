`ifndef SVC_STATS_CNT_SV
`define SVC_STATS_CNT_SV

`include "svc.sv"
`include "svc_accumulator.sv"
`include "svc_stats.sv"

// counter stat

module svc_stats_cnt #(
    parameter STAT_WIDTH     = 32,
    parameter BITS_PER_STAGE = `SVC_PIPE_BPS
) (
    input logic clk,

    input logic clr,
    input logic inc,
    input logic dec,

    output logic [STAT_WIDTH-1:0] cnt
);
  logic                  acc_en;
  logic [STAT_WIDTH-1:0] acc_val;

  svc_accumulator #(
      .WIDTH         (STAT_WIDTH),
      .BITS_PER_STAGE(BITS_PER_STAGE)
  ) svc_acc_i (
      .clk(clk),
      .clr(clr),
      .en (acc_en),
      .val(acc_val),
      .acc(cnt)
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
