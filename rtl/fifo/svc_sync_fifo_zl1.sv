`ifndef SVC_SYNC_FIFO_ZL1_SV
`define SVC_SYNC_FIFO_ZL1_SV

`include "svc.sv"
`include "svc_skidbuf.sv"

// A 1 element version of the zero-latency fifo.
//
// Rather than using an actual zero latency fifo with addr width of 1,
// this is built on top of a skidbuffer, which has the same functionality
// just with slightly different semantics. The 1 ADDR_WIDTH zl fifo used
// ~50% more cells than the SB version (roughly 90 compared to 60).
//
// See the old axil reflect modules for the pattern this replaces. While
// using a pure sb in that scenario can likely be made to work without the
// weirdness, modeling the solution as a fifo made so much more intuitive
// sense to me.
module svc_sync_fifo_zl1 #(
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
      .DATA_WIDTH(DATA_WIDTH)
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
