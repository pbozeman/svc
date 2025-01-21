`ifndef SVC_PRIORITY_ENCODER_SV
`define SVC_PRIORITY_ENCODER_SV

`include "svc.sv"

//
// Priority encoder with the low order request bits having priority
//
module svc_priority_encoder #(
    parameter WIDTH     = 4,
    parameter ENC_WIDTH = $clog2(WIDTH)
) (
    input  logic [    WIDTH-1:0] i_unencoded,
    output logic                 o_valid,
    output logic [ENC_WIDTH-1:0] o_encoded
);
  always_comb begin
    o_valid   = 1'b0;
    o_encoded = 0;

    for (int i = WIDTH - 1; i >= 0; i--) begin
      if (i_unencoded[i]) begin
        o_valid   = 1'b1;
        o_encoded = ENC_WIDTH'(i);
      end
    end
  end
endmodule

`endif
