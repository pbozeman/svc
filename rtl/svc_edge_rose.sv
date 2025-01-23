`ifndef SVC_EDGE_ROSE_SV
`define SVC_EDGE_ROSE_SV

`include "svc.sv"

module svc_edge_rose (
    input  logic clk,
    input  logic i,
    output logic rose
);
  logic i_prev = 0;
  assign rose = i & ~i_prev;

  always_ff @(posedge clk) begin
    i_prev <= i;
  end

endmodule

`endif
