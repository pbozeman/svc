`ifndef SVC_RV_PIPE_CTRL_RV_SV
`define SVC_RV_PIPE_CTRL_RV_SV

`include "svc.sv"
`include "svc_rv_pipe_ctrl.sv"

//
// Pipeline control module with ready/valid backpressure
//
// Wrapper around svc_rv_pipe_ctrl that adds ready_i support by converting
// backpressure (valid_o && !ready_i) into a stall signal.
//
// Use this module for pipeline stages that need downstream backpressure.
// For stages without backpressure, use svc_rv_pipe_ctrl directly.
//
module svc_rv_pipe_ctrl_rv #(
    parameter bit REG = 1
) (
    input logic clk,
    input logic rst_n,

    input  logic valid_i,
    output logic valid_o,
    input  logic ready_i,

    input logic stall_i,
    input logic flush_i,
    input logic bubble_i,

    output logic advance_o,
    output logic flush_o,
    output logic bubble_o
);

  //
  // Convert backpressure to stall
  //
  logic bp_stall;
  assign bp_stall = valid_o && !ready_i;

  svc_rv_pipe_ctrl #(
      .REG(REG)
  ) u_ctrl (
      .clk      (clk),
      .rst_n    (rst_n),
      .valid_i  (valid_i),
      .valid_o  (valid_o),
      .stall_i  (stall_i || bp_stall),
      .flush_i  (flush_i),
      .bubble_i (bubble_i),
      .advance_o(advance_o),
      .flush_o  (flush_o),
      .bubble_o (bubble_o)
  );

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_PIPE_CTRL_RV
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
  // Input assumptions: valid_i stable during backpressure (unless flush/bubble)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(
              valid_i && valid_o && !ready_i && !flush_i && !bubble_i
          ) && !ready_i) begin
        `FASSUME(a_valid_i_stable, valid_i);
      end
    end
  end

  //
  // Output assertions: valid_o stable during backpressure (unless flush)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(valid_o && !ready_i && !flush_i)) begin
        `FASSERT(a_valid_o_stable, valid_o);
      end
    end
  end

  //
  // Backpressure prevents advance
  //
  if (REG != 0) begin : g_bp_assertions
    always_comb begin
      if (valid_o && !ready_i) begin
        `FASSERT(a_bp_prevents_advance, !advance_o);
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `FCOVER(c_backpressure, valid_o && !ready_i);
      `FCOVER(c_bp_then_ready, $past(valid_o && !ready_i) && ready_i);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
