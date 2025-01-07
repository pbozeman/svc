`ifndef SVC_SYNC_FIFO_SV
`define SVC_SYNC_FIFO_SV

`include "svc.sv"

//
// Synchronous FIFO with FWFT (first word fall through.)
//
module svc_sync_fifo #(
    parameter ADDR_WIDTH = 4,
    parameter DATA_WIDTH = 8
) (
    input logic clk,
    input logic rst_n,

    input  logic                  w_inc,
    input  logic [DATA_WIDTH-1:0] w_data,
    output logic                  w_full,
    output logic                  w_half_full,

    input  logic                  r_inc,
    output logic                  r_empty,
    output logic [DATA_WIDTH-1:0] r_data
);
  localparam MEM_DEPTH = 1 << ADDR_WIDTH;

  logic [DATA_WIDTH-1:0] mem       [MEM_DEPTH-1:0];

  logic [  ADDR_WIDTH:0] w_ptr = 0;
  logic [ADDR_WIDTH-1:0] w_addr;

  logic [  ADDR_WIDTH:0] r_ptr = 0;
  logic [ADDR_WIDTH-1:0] r_addr;

  // Extract addresses from pointers
  assign w_addr = w_ptr[ADDR_WIDTH-1:0];
  assign r_addr = r_ptr[ADDR_WIDTH-1:0];

  // write
  always @(posedge clk) begin
    if (!rst_n) begin
      w_ptr <= 0;
    end else begin
      if (w_inc & !w_full) begin
        mem[w_addr] <= w_data;
        w_ptr       <= w_ptr + 1;
      end
    end
  end

  // read
  always @(posedge clk) begin
    if (!rst_n) begin
      r_ptr <= 0;
    end else begin
      if (r_inc & !r_empty) begin
        r_ptr <= r_ptr + 1;
      end
    end
  end

  assign w_full = (w_ptr[ADDR_WIDTH] ^ r_ptr[ADDR_WIDTH]) && w_addr == r_addr;
  assign w_half_full = ((w_ptr[ADDR_WIDTH:0] - r_ptr[ADDR_WIDTH:0]) >= (MEM_DEPTH >> 1));
  assign r_empty = (w_ptr == r_ptr);
  assign r_data = mem[r_addr];


`ifdef FORMAL
`ifdef FORMAL_SVC_SYNC_FIFO
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  // TODO: it would be nice to add checks that the data read is what was
  // written. It doesn't seem the system verilog queues are supported, so
  // testing the reads of writes would pretty much need to reimplement the
  // fifo logic, which would be pointless. Look into if there is some system
  // verilog function or class that can be used.

  // track how many elements are in the fifo
  int f_count = 0;
  int f_max_count = (1 << ADDR_WIDTH);
  always @(posedge clk) begin
    if (~rst_n) begin
      f_count <= 0;
    end else if ((w_inc && !w_full) && (!r_inc || r_empty)) begin
      f_count <= f_count + 1;
    end else if ((r_inc && !r_empty) && (!w_inc || w_full)) begin
      f_count <= f_count - 1;
    end
  end

  always @(posedge clk) begin
    if ($rose(rst_n)) begin
      `ASSERT(a_reset_ptrs, w_ptr == 0 && r_ptr == 0);
      `ASSERT(a_reset_flags, r_empty && !w_full);
    end
  end

  always @(posedge clk) begin
    if (rst_n) begin
      `ASSERT(a_oflow, f_count <= f_max_count);
      `ASSERT(a_full, !w_full || f_count == f_max_count);

      `COVER(c_full, w_inc && !r_inc && f_count == f_max_count - 1);

      `ASSERT(a_empty, !r_empty || f_count == 0);
      `COVER(c_empty, r_inc && !w_inc && f_count == 1);

      `COVER(c_write_full, (w_inc && w_full));
      `COVER(c_write_empty, (w_inc && r_empty));
      `COVER(c_read_empty, (r_inc && r_empty));
      `COVER(c_read_full, (r_inc && w_full));
      `COVER(c_rw_simultaneous, (w_inc && r_inc));

      `COVER(c_nzero_write, (w_inc && |w_data));
      `COVER(c_nzero_read, (r_inc && |r_data));

      // Half-full verification
      `ASSERT(a_half_full_count, w_half_full == (f_count >= (f_max_count >> 1)));
      `COVER(c_half_full_rise, $rose(w_half_full));
      `COVER(c_half_full_fall, $fell(w_half_full));

      // Cover interesting half-full scenarios
      `COVER(c_write_half_full, (w_inc && !w_half_full && f_count == (f_max_count >> 1) - 1));
      `COVER(c_read_half_full, (r_inc && w_half_full && f_count == (f_max_count >> 1)));
      `COVER(c_rw_half_full, (w_inc && r_inc && w_half_full));
    end
  end

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif
endmodule
`endif
