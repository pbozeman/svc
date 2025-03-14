`ifndef SVC_STICKY_BIT_SV
`define SVC_STICKY_BIT_SV

`include "svc.sv"

module svc_sticky_bit (
    input  logic clk,
    input  logic rst_n,
    input  logic clear,
    input  logic in,
    output logic out
);
  logic sticky = 0;

  always_comb begin
    out = sticky || in;
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      sticky <= 0;
    end else begin
      if (clear) begin
        sticky <= 0;
      end else begin
        sticky <= sticky || in;
      end
    end
  end

endmodule
`endif
