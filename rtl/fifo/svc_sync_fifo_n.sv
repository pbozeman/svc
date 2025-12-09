`ifndef SVC_SYNC_FIFO_N_SV
`define SVC_SYNC_FIFO_N_SV

`include "svc.sv"
`include "svc_sync_fifo.sv"

// This is like svc_sync_fifo, but with _n versions of full/empty,
// and no half_full. This is the same interface as the zl version.
//
// The _n version is a nicer interface for some use cases.

module svc_sync_fifo_n #(
    parameter ADDR_WIDTH = 1,
    parameter DATA_WIDTH = 8
) (
    input logic clk,
    input logic rst_n,
    input logic clr,

    input  logic                  w_inc,
    input  logic [DATA_WIDTH-1:0] w_data,
    output logic                  w_full_n,

    input  logic                  r_inc,
    output logic                  r_empty_n,
    output logic [DATA_WIDTH-1:0] r_data
);
  logic w_full;
  logic r_empty;

  assign w_full_n  = !w_full;
  assign r_empty_n = !r_empty;

  svc_sync_fifo #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) svc_sync_fifo_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .clr        (clr),
      .w_inc      (w_inc),
      .w_data     (w_data),
      .w_half_full(),
      .w_full     (w_full),
      .r_inc      (r_inc),
      .r_empty    (r_empty),
      .r_data     (r_data)
  );

endmodule
`endif
