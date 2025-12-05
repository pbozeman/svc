`ifndef SVC_RV_PIPE_CTRL_SV
`define SVC_RV_PIPE_CTRL_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Pipeline control module
//
// Manages the valid signal and computes control signals for data registers.
// Single instance per pipeline stage boundary, shared control outputs drive
// multiple svc_rv_pipe_data instances.
//
// Control outputs (active high, mutually exclusive):
//   advance_o - load new data from input
//   flush_o   - clear data to flush value
//   bubble_o  - clear data to bubble value
//
// Priority order:
// 1. Reset - clears valid
// 2. Flush - clears valid
// 3. Bubble (when can accept) - clears valid
// 4. Advance (when can accept) - loads valid_i
// 5. Hold - retains valid_o
//
module svc_rv_pipe_ctrl #(
    parameter bit REG = 1
) (
    input logic clk,
    input logic rst_n,

    input  logic valid_i,
    output logic valid_o,
    input  logic ready_i,

    input logic flush_i,
    input logic bubble_i,

    output logic advance_o,
    output logic flush_o,
    output logic bubble_o
);

  if (REG != 0) begin : g_registered
    logic can_accept;
    assign can_accept = !valid_o || ready_i;

    always_comb begin
      flush_o   = flush_i;
      bubble_o  = can_accept && bubble_i && !flush_i;
      advance_o = can_accept && valid_i && !bubble_i && !flush_i;
    end

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        valid_o <= 1'b0;
      end else if (flush_i) begin
        valid_o <= 1'b0;
      end else if (can_accept) begin
        valid_o <= valid_i && !bubble_i;
      end
    end

  end else begin : g_passthrough
    assign valid_o   = valid_i;
    assign flush_o   = 1'b0;
    assign bubble_o  = 1'b0;
    assign advance_o = 1'b1;

    `SVC_UNUSED({clk, rst_n, flush_i, bubble_i, ready_i});
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

  // Input assumptions: valid_i stable while stalled
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(valid_i && valid_o && !ready_i)) begin
        `FASSUME(a_valid_i_stable, valid_i);
      end
    end
  end

  // Output assertions: valid_o stable while stalled (unless flush)
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(valid_o && !ready_i && !flush_i)) begin
        `FASSERT(a_valid_o_stable, valid_o);
      end
    end
  end

  // Reset clears valid
  always_ff @(posedge clk) begin
    if (f_past_valid && !$past(rst_n)) begin
      `FASSERT(a_reset_clears_valid, valid_o == 1'b0);
    end
  end

  // Cover properties
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `FCOVER(c_flush, flush_o);
      `FCOVER(c_bubble, bubble_o);
      `FCOVER(c_advance, advance_o);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
