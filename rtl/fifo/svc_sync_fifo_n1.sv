`ifndef SVC_SYNC_FIFO_N1_SV
`define SVC_SYNC_FIFO_N1_SV

`include "svc.sv"
`include "svc_skidbuf.sv"

// A 1 element fifo with the _n interface
//
// Rather than using an actual sync_fifo_n with addr width of 1,
// this is built on top of a skidbuffer, which has the same functionality
// just with slightly different semantics.
//
// This comes with less of an efficiency improvement than the zl1 v.s.
// width 1 zl, but, it's still an improvement.

module svc_sync_fifo_n1 #(
    parameter DATA_WIDTH = 8
) (
    input logic clk,
    input logic rst_n,

    input  logic                  w_inc,
    input  logic [DATA_WIDTH-1:0] w_data,
    output logic                  w_full_n,

    input  logic                  r_inc,
    output logic [DATA_WIDTH-1:0] r_data,
    output logic                  r_empty_n
);
  svc_skidbuf #(
      .DATA_WIDTH(DATA_WIDTH),
      .OPT_OUTREG(1)
  ) svc_skidbuf_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(w_inc),
      .i_data (w_data),
      .o_ready(w_full_n),

      .i_ready(r_inc),
      .o_data (r_data),
      .o_valid(r_empty_n)
  );
endmodule
`endif
