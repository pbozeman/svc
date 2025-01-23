`ifndef SVC_EDGE_FELL_SV
`define SVC_EDGE_FELL_SV

`include "svc.sv"

module svc_edge_fell (
    input  logic clk,
    input  logic i,
    output logic fell
);
  logic i_prev = 0;
  assign fell = ~i & i_prev;

  always_ff @(posedge clk) begin
    i_prev <= i;
  end

endmodule

`endif
