`ifndef SVC_MUX_ONEHOT_SV
`define SVC_MUX_ONEHOT_SV

`include "svc.sv"

//
// One-hot multiplexer
//
// Selects one of N data inputs based on a one-hot selector signal.
// If no bit is set, output is zero. If multiple bits are set,
// output is OR of selected inputs.
//
// The data input is a packed vector with MSB-to-LSB ordering:
//   .data({data_N-1, ..., data_1, data_0})
//
module svc_mux_onehot #(
    parameter int WIDTH = 32,
    parameter int N     = 4
) (
    input  logic [      N-1:0] sel,
    input  logic [N*WIDTH-1:0] data,
    output logic [  WIDTH-1:0] out
);

  always_comb begin
    out = '0;
    for (int i = 0; i < N; i++) begin
      out |= {WIDTH{sel[i]}} & data[i*WIDTH+:WIDTH];
    end
  end

`ifdef FORMAL
`ifdef FORMAL_SVC_MUX_ONEHOT
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)
`else
  `define FASSERT(label, a) label: assume(a)
  `define FASSUME(label, a) label: assert(a)
  `define FCOVER(label, a)
`endif

  //
  // Assume inputs
  //
  always_comb begin
    `FASSUME(a_sel_onehot0, $onehot0(sel));
  end

  //
  // Assert correct output for each possible select
  //
  always_comb begin
    if (sel == '0) begin
      `FASSERT(a_zero_sel, out == '0);
    end
  end

  for (genvar i = 0; i < N; i++) begin : g_formal_sel
    always_comb begin
      if (sel == (1 << i)) begin
`ifdef FORMAL_SVC_MUX_ONEHOT
        assert (out == data[i*WIDTH+:WIDTH]);
`else
        assume (out == data[i*WIDTH+:WIDTH]);
`endif
      end
    end

    //
    // Cover each input being selected
    //
`ifdef FORMAL_SVC_MUX_ONEHOT
    always_comb begin
      cover (sel[i]);
    end
`endif
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
