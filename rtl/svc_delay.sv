`ifndef SVC_DELAY_SV
`define SVC_DELAY_SV

`include "svc.sv"

module svc_delay #(
    parameter CYCLES = 1,
    parameter WIDTH  = 1
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
  logic [WIDTH-1:0] shift_reg[CYCLES-1:0];

  // using an always_ff here confuses iverilog and results in
  //
  // warning: A for statement must use the index (i) in the condition
  // expression to be synthesized in an always_ff process.
  //
  // But only if the CYCLES parameter isn't a single integer. If
  // its made from something like localparam DELAY = ADC_DELAY + 2,
  // then there is a warning, which tbh, doesn't make much sense.
  always @(posedge clk) begin
    if (!rst_n) begin
      for (int i = 0; i < CYCLES; i++) begin
        shift_reg[i] <= '0;
      end
    end else begin
      shift_reg[0] <= in;
      for (int i = 1; i < CYCLES; i++) begin
        shift_reg[i] <= shift_reg[i-1];
      end
    end
  end

  assign out = shift_reg[CYCLES-1];

endmodule
`endif
