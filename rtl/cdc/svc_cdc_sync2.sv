`ifndef SVC_CDC_SYNC2_SV
`define SVC_CDC_SYNC2_SV

`include "svc.sv"

//
// sync2 from
// https://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf
//

// sync signal to different clock domain
module svc_cdc_sync2 #(
    parameter WIDTH = 1
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] d,
    output logic [WIDTH-1:0] q
);

  (* async_reg = "true" *)logic [WIDTH-1:0] q1 = 0;
  (* async_reg = "true" *)logic [WIDTH-1:0] q_int = 0;

  assign q = q_int;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      q_int <= 0;
      q1    <= 0;
    end else begin
      q_int <= q1;
      q1    <= d;
    end
  end
endmodule

`endif
