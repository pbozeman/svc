`ifndef SVC_STATS_MIN_SV
`define SVC_STATS_MIN_SV

`include "svc.sv"

// This module tracks the minimum value ever seen on `val` when `en` is high.
// It supports optional pipelining. STAGES == 0 uses a direct compare/update.
// STAGES > 0 inserts pipeline registers between the input and final comparison.

module svc_stats_min #(
    parameter int WIDTH  = 32,
    parameter int STAGES = 4
) (
    input logic clk,
    input logic rst_n,

    input  logic             clr,
    input  logic             en,
    input  logic [WIDTH-1:0] val,
    output logic [WIDTH-1:0] min
);
  if (STAGES == 0) begin : gen_stage_z
    always_ff @(posedge clk) begin
      if (!rst_n || clr) begin
        // initialize to max value
        min <= '1;
      end else if (en && val < min) begin
        min <= val;
      end
    end
  end else begin : gen_stage_nz
    logic [WIDTH-1:0] data_p [0:STAGES];
    logic             valid_p[0:STAGES];

    // Stage 0: latch input when enabled
    always_ff @(posedge clk) begin
      if (!rst_n || clr) begin
        data_p[0]  <= '1;
        valid_p[0] <= 1'b0;
      end else if (en) begin
        data_p[0]  <= val;
        valid_p[0] <= 1'b1;
      end else begin
        valid_p[0] <= 1'b0;
      end
    end

    // Pipeline stages
    for (genvar i = 1; i <= STAGES; ++i) begin : gen_pipeline
      always_ff @(posedge clk) begin
        if (!rst_n || clr) begin
          data_p[i]  <= '1;
          valid_p[i] <= 1'b0;
        end else begin
          data_p[i]  <= valid_p[i-1] ? data_p[i-1] : data_p[i];
          valid_p[i] <= valid_p[i-1];
        end
      end
    end

    // Final compare at the end of the pipeline
    always_ff @(posedge clk) begin
      if (!rst_n || clr) begin
        min <= '1;
      end else if (valid_p[STAGES] && data_p[STAGES] < min) begin
        min <= data_p[STAGES];
      end
    end
  end

endmodule
`endif
