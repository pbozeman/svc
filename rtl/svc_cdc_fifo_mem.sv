`ifndef SVC_CDC_FIFO_MEM_SV
`define SVC_CDC_FIFO_MEM_SV

`include "svc.sv"

//
// From:
// http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf
//
// 6.2 fifomem.v - FIFO memory buffer
//

module svc_cdc_fifo_mem #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
) (
    input logic w_clk,
    input logic w_clk_en,
    input logic w_full,

    // write interface
    input logic [ADDR_WIDTH-1:0] w_addr,
    input logic [DATA_WIDTH-1:0] w_data,

    // read interface
    input  logic [ADDR_WIDTH-1:0] r_addr,
    output logic [DATA_WIDTH-1:0] r_data
);
  localparam DEPTH = 1 << ADDR_WIDTH;
  logic [DATA_WIDTH-1:0] mem[0:DEPTH-1];

  always_ff @(posedge w_clk) begin
    if (w_clk_en && !w_full) begin
      mem[w_addr] <= w_data;
    end
  end

  assign r_data = mem[r_addr];

`ifndef SYNTHESIS
  // The discarded signal was not part of the Cummings design, but it's useful
  // to assert on in unit tests or during formal verification.
  //
  // verilator lint_off UNUSEDSIGNAL
  logic discarded;
  assign discarded = w_clk_en && w_full;
  // verilator lint_on UNUSEDSIGNAL
`endif

endmodule

`endif
