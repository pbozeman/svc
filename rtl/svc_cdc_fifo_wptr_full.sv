`ifndef SVC_CDC_FIFO_WPTR_FULL_SV
`define SVC_CDC_FIFO_WPTR_FULL_SV

`include "svc.sv"

//
// From:
// http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf
//
// 6.6 wptr_full.v - Write pointer & full generation logic
//

module svc_cdc_fifo_wptr_full #(
    parameter ADDR_WIDTH = 4
) (
    input                  w_clk,
    input                  w_rst_n,
    input                  w_inc,
    input [ADDR_WIDTH : 0] w_q2_rptr,

    output logic                  w_full,
    output logic [ADDR_WIDTH : 0] w_ptr = 0,
    output logic [ADDR_WIDTH-1:0] w_addr
);
  logic [ADDR_WIDTH:0] w_bin = 0;
  logic [ADDR_WIDTH:0] w_bin_next;
  logic [ADDR_WIDTH:0] w_gray_next;

  // Memory write-address pointer (okay to use binary to address memory)
  assign w_addr      = w_bin[ADDR_WIDTH-1:0];

  //
  // Pointers
  //
  // next pointer values
  //
  assign w_bin_next  = (w_inc && !w_full) ? w_bin + 1 : w_bin;
  assign w_gray_next = (w_bin_next >> 1) ^ w_bin_next;

  // register next pointer values
  always_ff @(posedge w_clk) begin
    if (!w_rst_n) begin
      w_bin <= 0;
      w_ptr <= 0;
    end else begin
      w_bin <= w_bin_next;
      w_ptr <= w_gray_next;
    end
  end

  //
  // Full
  //
  logic w_full_val;
  assign w_full_val = (w_gray_next == {~w_q2_rptr[ADDR_WIDTH:ADDR_WIDTH-1],
                                       w_q2_rptr[ADDR_WIDTH-2:0]});

  // Register full flags
  always_ff @(posedge w_clk) begin
    if (!w_rst_n) begin
      w_full <= 1'b0;
    end else begin
      w_full <= w_full_val;
    end
  end

endmodule

`endif
