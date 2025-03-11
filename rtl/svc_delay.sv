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

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int i = 0; i < CYCLES; i++) begin
        shift_reg[i] <= '0;
      end
      out <= '0;
    end else begin
      shift_reg[0] <= in;
      for (int i = 1; i < CYCLES; i++) begin
        shift_reg[i] <= shift_reg[i-1];
      end
      out <= shift_reg[CYCLES-1];
    end
  end

endmodule
`endif
