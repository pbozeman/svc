`ifndef SVC_SYNC_FIFO_ZL_SV
`define SVC_SYNC_FIFO_ZL_SV

`include "svc.sv"
`include "svc_sync_fifo.sv"

//
// Synchronous FIFO with FWFT and zero latency writes, i.e the read data is
// made available in the *same clock cycle* as the write. This provides
// skid buffer like access when writing to an empty fifo, but regular
// fifo latencies if the fifo becomes non-empty.
//
// Because the first use cases were using this in conjunction with
// ready/valid based back pressure signaling, w_full and r_empty were
// made active low signals so that they could be assigned directly to
// ready and valid signals.
//
// Note: the underlying r_empty and w_full signals are registered,
// so using w_full_n as a ready signal is effectively registered as well.
//
module svc_sync_fifo_zl #(
    parameter ADDR_WIDTH = 3,
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
  logic                  fifo_w_full;

  logic                  fifo_r_empty;
  logic [DATA_WIDTH-1:0] fifo_r_data;

  assign w_full_n = !fifo_w_full;

  // zero latency output signals
  always_comb begin
    if (fifo_r_empty) begin
      r_empty_n = w_inc;
      r_data    = w_data;
    end else begin
      r_empty_n = 1'b1;
      r_data    = fifo_r_data;
    end
  end

  svc_sync_fifo #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) fifo_inst (
      .clk  (clk),
      .rst_n(rst_n),
      .clr  (1'b0),

      // prevent fifo write if data is being consumed in zero-latency mode.
      // note: r_inc on an empty fifo is a no-op, so it doesn't need a guard
      .w_inc      (w_inc && !(fifo_r_empty && r_inc)),
      .w_data     (w_data),
      .w_full     (fifo_w_full),
      .w_half_full(),
      .r_inc      (r_inc),
      .r_empty    (fifo_r_empty),
      .r_data     (fifo_r_data)
  );

`ifdef FORMAL
`ifdef FORMAL_SVC_SYNC_FIFO_ZL
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  // The sby file for this module also keeps asserts on in the lower fifo
  // module, rather than turning them into assumptions. Cover is left
  // enabled as well. We don't need to reproduce all the interesting fifo
  // asserts and covers here, just the zero latency related ones.

  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(posedge clk) begin
    if (f_past_valid && rst_n && $past(rst_n)) begin
      // this is covered in the lower level fifo, but let's just be explicit,
      // since this is the main point of this module.
      `COVER(c_zl_read, w_inc && r_inc && $past(!r_empty_n));

      // zero latency data assertion
      if (w_inc && $past(!r_empty_n)) begin
        `ASSERT(a_zl_read, r_data == w_data);
      end

      // data stored if not read same cycle
      if ($past(w_inc && !r_inc) && $past(!r_empty_n, 1)) begin
        `ASSERT(a_defered_read, r_data == $past(w_data));
      end
    end
  end

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif

endmodule
`endif
