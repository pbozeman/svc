`ifndef SVC_RV_PIPE_DATA_SV
`define SVC_RV_PIPE_DATA_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Pipeline data register
//
// Simple data register driven by control signals from svc_rv_pipe_ctrl.
// Multiple instances per pipeline stage, each with different policies.
//
// *_REG parameters control whether to load from data_i or use the
// corresponding *_VAL parameter for each event type.
//
module svc_rv_pipe_data #(
    parameter int               WIDTH      = 8,
    parameter bit               REG        = 1,
    parameter bit               RESET_REG  = 0,
    parameter bit               FLUSH_REG  = 0,
    parameter bit               BUBBLE_REG = 0,
    parameter logic [WIDTH-1:0] RESET_VAL  = '0,
    parameter logic [WIDTH-1:0] FLUSH_VAL  = '0,
    parameter logic [WIDTH-1:0] BUBBLE_VAL = '0
) (
    input logic clk,
    input logic rst_n,

    input logic advance,
    input logic flush,
    input logic bubble,

                          input  logic [WIDTH-1:0] data_i,
    (* max_fanout = 32 *) output logic [WIDTH-1:0] data_o
);

  if (REG != 0) begin : g_registered
    //
    // Generate-time selection of values for each event type
    //
    logic [WIDTH-1:0] reset_load_val;
    logic [WIDTH-1:0] flush_load_val;
    logic [WIDTH-1:0] bubble_load_val;

    if (RESET_REG) begin : g_reset_data_i
      assign reset_load_val = data_i;
    end else begin : g_reset_val
      assign reset_load_val = RESET_VAL;
    end

    if (FLUSH_REG) begin : g_flush_data_i
      assign flush_load_val = data_i;
    end else begin : g_flush_val
      assign flush_load_val = FLUSH_VAL;
    end

    if (BUBBLE_REG) begin : g_bubble_data_i
      assign bubble_load_val = data_i;
    end else begin : g_bubble_val
      assign bubble_load_val = BUBBLE_VAL;
    end

    //
    // Data register with priority-based loading
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        data_o <= reset_load_val;
      end else if (flush) begin
        data_o <= flush_load_val;
      end else if (bubble) begin
        data_o <= bubble_load_val;
      end else if (advance) begin
        data_o <= data_i;
      end
    end

  end else begin : g_passthrough
    //
    // Passthrough: combinational path
    //
    assign data_o = data_i;

    `SVC_UNUSED({clk, rst_n, flush, bubble, advance});
  end

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_PIPE_DATA
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

  // Reset behavior
  always_ff @(posedge clk) begin
    if (f_past_valid && !$past(rst_n)) begin
      if (RESET_REG) begin
        `FASSERT(a_reset_loads_input, data_o == $past(data_i));
      end else begin
        `FASSERT(a_reset_loads_val, data_o == RESET_VAL);
      end
    end
  end

  // Data behavior assertions
  always_ff @(posedge clk) begin
    // Priority in implementation: reset > flush > bubble > advance
    // Assertions must account for this priority order.
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(advance && !flush && !bubble)) begin
        `FASSERT(a_advance_loads_data, data_o == $past(data_i));
      end
      if ($past(!flush && !bubble && !advance)) begin
        `FASSERT(a_hold_retains_data, data_o == $past(data_o));
      end
    end
  end

  // Cover properties
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `FCOVER(c_advance, $past(advance));
      `FCOVER(c_hold, $past(!flush && !bubble && !advance));
      `FCOVER(c_flush, $past(flush));
      `FCOVER(c_bubble, $past(bubble));
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
