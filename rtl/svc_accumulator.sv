`ifndef SVC_ACCUMULATOR_SV
`define SVC_ACCUMULATOR_SV

`include "svc.sv"

// This accumulator slices the carry chain into segments with registers
// in between them, useful when the carry chain propagation starts causing
// timing issues. STAGES 0 is a pass through mode with a direct add.
//
// TODO: set the STAGES default programatically based on WIDTH and
// the target FPGA. While the ice40 needs it for 32 bit adds in non-trivial
// designs, xilinx chips do not.
module svc_accumulator #(
    parameter int WIDTH  = 32,
    parameter int STAGES = 4
) (
    input logic clk,
    input logic rst_n,

    input  logic             clr,
    input  logic             en,
    input  logic [WIDTH-1:0] val,
    output logic [WIDTH-1:0] acc
);
  if (STAGES == 0) begin : gen_stage_z
    always_ff @(posedge clk) begin
      if (!rst_n || clr) begin
        acc <= 0;
      end else begin
        if (en) begin
          acc <= acc + val;
        end
      end
    end
  end else begin : gen_stage_nz
    logic [WIDTH-1:0] data_p [0:STAGES];
    logic             valid_p[0:STAGES];

    // Stage 0 = input stage
    always_ff @(posedge clk) begin
      if (!rst_n || clr) begin
        data_p[0]  <= '0;
        valid_p[0] <= 1'b0;
      end else if (en) begin
        data_p[0]  <= val;
        valid_p[0] <= 1'b1;
      end else begin
        valid_p[0] <= 1'b0;
      end
    end

    // Internal pipeline stages
    for (genvar i = 1; i <= STAGES; ++i) begin : gen_pipeline
      always_ff @(posedge clk) begin
        if (!rst_n || clr) begin
          data_p[i]  <= '0;
          valid_p[i] <= 1'b0;
        end else begin
          data_p[i]  <= valid_p[i-1] ? data_p[i-1] : data_p[i];
          valid_p[i] <= valid_p[i-1];
        end
      end
    end

    always_ff @(posedge clk) begin
      if (!rst_n || clr) begin
        acc <= '0;
      end else begin
        if (valid_p[STAGES]) begin
          acc <= acc + data_p[STAGES];
        end
      end
    end
  end

endmodule

`endif
