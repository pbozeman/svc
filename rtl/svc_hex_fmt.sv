`ifndef SVC_HEX_FMT_SV
`define SVC_HEX_FMT_SV

`include "svc.sv"

module svc_hex_fmt #(
    parameter int WIDTH = 32,
    parameter int N     = WIDTH / 8
) (
    input  logic [ 8*N-1:0] val,
    output logic [16*N-1:0] ascii
);
  function automatic [7:0] nibble_to_ascii(input [3:0] nibble);
    case (nibble)
      4'h0:    nibble_to_ascii = "0";
      4'h1:    nibble_to_ascii = "1";
      4'h2:    nibble_to_ascii = "2";
      4'h3:    nibble_to_ascii = "3";
      4'h4:    nibble_to_ascii = "4";
      4'h5:    nibble_to_ascii = "5";
      4'h6:    nibble_to_ascii = "6";
      4'h7:    nibble_to_ascii = "7";
      4'h8:    nibble_to_ascii = "8";
      4'h9:    nibble_to_ascii = "9";
      4'hA:    nibble_to_ascii = "A";
      4'hB:    nibble_to_ascii = "B";
      4'hC:    nibble_to_ascii = "C";
      4'hD:    nibble_to_ascii = "D";
      4'hE:    nibble_to_ascii = "E";
      4'hF:    nibble_to_ascii = "F";
      default: nibble_to_ascii = "?";
    endcase
  endfunction

  always @(*) begin
    for (int i = 0; i < N; i++) begin
      logic [7:0] char;
      char                   = val[(N-1-i)*8+:8];
      ascii[(N-1-i)*16+:8]   = nibble_to_ascii(char[3:0]);
      ascii[(N-1-i)*16+8+:8] = nibble_to_ascii(char[7:4]);
    end
  end

endmodule
`endif
