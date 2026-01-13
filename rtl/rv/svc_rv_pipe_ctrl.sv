`ifndef SVC_RV_PIPE_CTRL_SV
`define SVC_RV_PIPE_CTRL_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Pipeline control module
//
// Computes control signals for data registers.
// Single instance per pipeline stage boundary, shared control outputs drive
// multiple svc_rv_pipe_data instances.
//
// Control outputs (active high, mutually exclusive):
//   advance_o - load new data from input
//   flush_o   - clear data to flush value
//   bubble_o  - clear data to bubble value
//
// Priority order:
// 1. Flush - clears data
// 2. Bubble (when can accept) - clears data
// 3. Advance (when can accept) - loads new data
// 4. Hold (when stalled) - retains data
//
module svc_rv_pipe_ctrl #(
    parameter bit REG = 1
) (
    input logic clk,
    input logic rst_n,

    input logic stall_i,
    input logic flush_i,
    input logic bubble_i,

    output logic advance_o,
    output logic flush_o,
    output logic bubble_o
);

  if (REG != 0) begin : g_registered
    // Stall takes priority - when stalled, nothing advances
    always_comb begin
      flush_o   = flush_i;
      bubble_o  = !stall_i && bubble_i && !flush_i;
      advance_o = !stall_i && !bubble_i && !flush_i;
    end

    `SVC_UNUSED({clk, rst_n});

  end else begin : g_passthrough
    assign flush_o   = 1'b0;
    assign bubble_o  = 1'b0;
    assign advance_o = 1'b1;

    `SVC_UNUSED({clk, rst_n, stall_i, flush_i, bubble_i});
  end

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_PIPE_CTRL
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)
`else
  `define FASSERT(label, a) label: assume(a)
  `define FASSUME(label, a) label: assert(a)
  `define FCOVER(label, a)
`endif

  logic f_past_valid = 1'b0;

  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  //
  // Stall assertions: stall_i prevents advance_o (registered mode only)
  //
  if (REG != 0) begin : g_stall_assertions
    always_comb begin
      if (stall_i) begin
        `FASSERT(a_stall_prevents_advance, !advance_o);
        `FASSERT(a_stall_prevents_bubble, !bubble_o);
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `FCOVER(c_flush, flush_o);
      `FCOVER(c_bubble, bubble_o);
      `FCOVER(c_advance, advance_o);
      `FCOVER(c_stall, stall_i);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
