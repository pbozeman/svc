`ifndef SVC_MUXN_SV
`define SVC_MUXN_SV

`include "svc.sv"

//
// Generalized N-way multiplexer
//
// Selects one of N data inputs based on a selector signal.
// Uses logarithmic encoding: N inputs require $clog2(N) selector bits.
//
// The exact mux structure is generated at elaboration time based on N:
// - Power-of-2 values: Uses case without default (all cases covered)
// - Non-power-of-2: Uses case with default for out-of-range selectors
// - N > 8: Falls back to generic if-based mux
//
// The data input is a packed vector with MSB-to-LSB ordering:
//   .data({data_N-1, ..., data_1, data_0})
//
module svc_muxn #(
    parameter int WIDTH = 32,
    parameter int N     = 4
) (
    input  logic [$clog2(N)-1:0] sel,
    input  logic [  N*WIDTH-1:0] data,
    output logic [    WIDTH-1:0] out
);

  //
  // Generate exact mux based on N
  //
  // verilog_format: off
  if (N == 1) begin : g_mux1
    //
    // Trivial mux
    //
    assign out = data[WIDTH-1:0];

  end else if (N == 2) begin : g_mux2
    //
    // 2-way mux (power-of-2)
    //
    assign out = sel ? data[1*WIDTH+:WIDTH] : data[0*WIDTH+:WIDTH];

  end else if (N == 3) begin : g_mux3
    //
    // 3-way mux
    //
    assign out = (sel == 2'd0) ? data[0*WIDTH+:WIDTH] :
                 (sel == 2'd1) ? data[1*WIDTH+:WIDTH] :
                 (sel == 2'd2) ? data[2*WIDTH+:WIDTH] : {WIDTH{1'bx}};

  end else if (N == 4) begin : g_mux4
    //
    // 4-way mux (power-of-2)
    //
    assign out = (sel == 2'd0) ? data[0*WIDTH+:WIDTH] :
                 (sel == 2'd1) ? data[1*WIDTH+:WIDTH] :
                 (sel == 2'd2) ? data[2*WIDTH+:WIDTH] : data[3*WIDTH+:WIDTH];

  end else if (N == 5) begin : g_mux5
    //
    // 5-way mux
    //
    assign out = (sel == 3'd0) ? data[0*WIDTH+:WIDTH] :
                 (sel == 3'd1) ? data[1*WIDTH+:WIDTH] :
                 (sel == 3'd2) ? data[2*WIDTH+:WIDTH] :
                 (sel == 3'd3) ? data[3*WIDTH+:WIDTH] :
                 (sel == 3'd4) ? data[4*WIDTH+:WIDTH] : {WIDTH{1'bx}};

  end else if (N == 6) begin : g_mux6
    //
    // 6-way mux
    //
    assign out = (sel == 3'd0) ? data[0*WIDTH+:WIDTH] :
                 (sel == 3'd1) ? data[1*WIDTH+:WIDTH] :
                 (sel == 3'd2) ? data[2*WIDTH+:WIDTH] :
                 (sel == 3'd3) ? data[3*WIDTH+:WIDTH] :
                 (sel == 3'd4) ? data[4*WIDTH+:WIDTH] :
                 (sel == 3'd5) ? data[5*WIDTH+:WIDTH] : {WIDTH{1'bx}};

  end else if (N == 7) begin : g_mux7
    //
    // 7-way mux
    //
    assign out = (sel == 3'd0) ? data[0*WIDTH+:WIDTH] :
                 (sel == 3'd1) ? data[1*WIDTH+:WIDTH] :
                 (sel == 3'd2) ? data[2*WIDTH+:WIDTH] :
                 (sel == 3'd3) ? data[3*WIDTH+:WIDTH] :
                 (sel == 3'd4) ? data[4*WIDTH+:WIDTH] :
                 (sel == 3'd5) ? data[5*WIDTH+:WIDTH] :
                 (sel == 3'd6) ? data[6*WIDTH+:WIDTH] : {WIDTH{1'bx}};

  end else if (N == 8) begin : g_mux8
    //
    // 8-way mux (power-of-2)
    //
    assign out = (sel == 3'd0) ? data[0*WIDTH+:WIDTH] :
                 (sel == 3'd1) ? data[1*WIDTH+:WIDTH] :
                 (sel == 3'd2) ? data[2*WIDTH+:WIDTH] :
                 (sel == 3'd3) ? data[3*WIDTH+:WIDTH] :
                 (sel == 3'd4) ? data[4*WIDTH+:WIDTH] :
                 (sel == 3'd5) ? data[5*WIDTH+:WIDTH] :
                 (sel == 3'd6) ? data[6*WIDTH+:WIDTH] : data[7*WIDTH+:WIDTH];

  end else begin : g_mux_generic
    //
    // Generic N-way mux for larger values
    //
    always_comb begin
      if (sel < N) begin
        out = data[sel*WIDTH+:WIDTH];
      end else begin
        out = {WIDTH{1'bx}};
      end
    end
  end
  // verilog_format: on

endmodule

`endif
