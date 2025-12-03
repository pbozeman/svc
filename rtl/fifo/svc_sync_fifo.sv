`ifndef SVC_SYNC_FIFO_SV
`define SVC_SYNC_FIFO_SV

`include "svc.sv"

//
// Synchronous FIFO with FWFT (first word fall through.)
//
// Full/empty signals are registered
//
module svc_sync_fifo #(
    parameter ADDR_WIDTH = 3,
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

  logic [DATA_WIDTH-1:0] mem         [MEM_DEPTH-1:0];

  logic [  ADDR_WIDTH:0] w_ptr = 0;
  logic [  ADDR_WIDTH:0] w_ptr_next;

  logic [  ADDR_WIDTH:0] r_ptr = 0;
  logic [  ADDR_WIDTH:0] r_ptr_next;

  logic [ADDR_WIDTH-1:0] w_addr;
  logic [ADDR_WIDTH-1:0] w_addr_next;

  logic [ADDR_WIDTH-1:0] r_addr;
  logic [ADDR_WIDTH-1:0] r_addr_next;

  logic                  w_full_next;

  logic [  ADDR_WIDTH:0] used_next;

  //
  // w_ptr
  //
  always_comb begin
    w_ptr_next = w_ptr;
    if (w_inc & !w_full) begin
      w_ptr_next = w_ptr + 1;
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      w_ptr <= 0;
    end else begin
      w_ptr <= w_ptr_next;
    end
  end

  //
  // r_ptr
  //
  always_comb begin
    r_ptr_next = r_ptr;
    if (r_inc & !r_empty) begin
      r_ptr_next = r_ptr_next + 1;
    end
  end

  always @(posedge clk) begin
    if (!rst_n) begin
      r_ptr <= 0;
    end else begin
      r_ptr <= r_ptr_next;
    end
  end

  // Extract addresses from pointers
  assign w_addr_next = w_ptr_next[ADDR_WIDTH-1:0];
  assign r_addr_next = r_ptr_next[ADDR_WIDTH-1:0];

  // the ptr subtraction needs to use ADDR_WITH bits,
  // not ADDR_WIDTH -1
  assign used_next = w_ptr_next - r_ptr_next;
  assign w_full_next = ((w_ptr_next[ADDR_WIDTH] ^ r_ptr_next[ADDR_WIDTH]) &&
                        w_addr_next == r_addr_next);

  always @(posedge clk) begin
    if (!rst_n) begin
      w_addr      <= 0;
      w_full      <= 1'b0;
      w_half_full <= 1'b0;

      r_empty     <= 1'b1;
      r_addr      <= 0;
    end else begin
      w_addr      <= w_addr_next;
      w_half_full <= used_next >= MEM_DEPTH >> 1;
      w_full      <= w_full_next;

      r_empty     <= w_ptr_next == r_ptr_next;
      r_addr      <= r_addr_next;
    end
  end

  //
  // mem
  //
  always @(posedge clk) begin
    // the rst_n check here helps with timing on the ice40
    if (rst_n) begin
      if (w_inc & !w_full) begin
        mem[w_addr] <= w_data;
      end
    end
  end

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

  logic f_past_valid = 0;
  always @(posedge clk) begin
    f_past_valid <= 1;
  end

  always @(posedge clk) begin
    if (!f_past_valid) begin
      assume (rst_n == 0);
    end
  end

`ifndef FORMAL_SVC_SYNC_FIFO
`ifndef FORMAL_NO_SUBMODULES
  always @(posedge clk) begin
    if (rst_n) begin
      assert (!(w_inc && w_full));
      assert (!(r_inc && r_empty));
    end
  end
`endif
`endif

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
    if (f_past_valid && $rose(rst_n)) begin
      `ASSERT(a_reset_ptrs, w_ptr == 0 && r_ptr == 0);
      `ASSERT(a_reset_empty, r_empty);
      `ASSERT(a_reset_full, !w_full);
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
      `ASSERT(a_half_full_count,
              w_half_full == (f_count >= (f_max_count >> 1)));
      `COVER(c_half_full_rise, $rose(w_half_full));
      `COVER(c_half_full_fall, $fell(w_half_full));

      // Cover interesting half-full scenarios
      `COVER(c_write_half_full,
             (w_inc && !w_half_full && f_count == (f_max_count >> 1) - 1));
      `COVER(c_read_half_full,
             (r_inc && w_half_full && f_count == (f_max_count >> 1)));
      `COVER(c_rw_half_full, (w_inc && r_inc && w_half_full));
    end
  end

`ifdef FORMAL_SVC_SYNC_FIFO_DATA
  //
  // data validation
  //
  // This causes verification to take a long time to run, which is why
  // its controlled by an ifdef. Calling modules almost certainly don't
  // need this to be run during their verification. The ADDR_WIDTH should also
  // be reduced when in this mode.
  localparam F_MAX_COUNT = (1 << ADDR_WIDTH);
  logic [DATA_WIDTH-1:0] f_shadow_queue    [0:F_MAX_COUNT-1];
  int                    f_shadow_rptr = 0;
  int                    f_shadow_wptr = 0;

  always @(posedge clk) begin
    if (~rst_n) begin
      f_shadow_rptr <= 0;
      f_shadow_wptr <= 0;
    end else begin
      // Write operation
      if (w_inc && !w_full) begin
        f_shadow_queue[f_shadow_wptr] <= w_data;
        f_shadow_wptr                 <= (f_shadow_wptr + 1) % f_max_count;
      end
      // Read operation
      if (r_inc && !r_empty) begin
        f_shadow_rptr <= (f_shadow_rptr + 1) % f_max_count;
      end
    end
  end

  always @(posedge clk) begin
    if (rst_n && r_inc && !r_empty) begin
      `ASSERT(a_data_valid, r_data == f_shadow_queue[f_shadow_rptr]);
    end
  end
`endif

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif
endmodule
`endif
