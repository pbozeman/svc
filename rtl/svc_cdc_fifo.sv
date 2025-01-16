`ifndef SVC_CDC_FIFO_SV
`define SVC_CDC_FIFO_SV

`include "svc.sv"

`include "svc_cdc_fifo_mem.sv"
`include "svc_cdc_fifo_rptr_empty.sv"
`include "svc_cdc_fifo_wptr_full.sv"
`include "svc_cdc_sync2.sv"

//
// From:
// http://www.sunburst-design.com/papers/CummingsSNUG2002SJ_FIFO1.pdf
//
// 6.1 fifo1.v - FIFO top-level module
//

module svc_cdc_fifo #(
    parameter DATA_WIDTH = 8,
    parameter ADDR_WIDTH = 4
) (
    // Write clock domain inputs
    input logic                  w_clk,
    input logic                  w_rst_n,
    input logic                  w_inc,
    input logic [DATA_WIDTH-1:0] w_data,

    // Write clock domain output
    output logic w_full,

    // Read clock domain inputs
    input logic r_clk,
    input logic r_rst_n,
    input logic r_inc,

    // Read clock domain outputs
    output logic                  r_empty,
    output logic [DATA_WIDTH-1:0] r_data
);
  logic [ADDR_WIDTH-1:0] w_addr;
  logic [ADDR_WIDTH-1:0] r_addr;

  logic [  ADDR_WIDTH:0] w_ptr;
  logic [  ADDR_WIDTH:0] r_ptr;
  logic [  ADDR_WIDTH:0] w_q2_rptr;
  logic [  ADDR_WIDTH:0] r_q2_wptr;

  svc_cdc_sync2 #(
      .WIDTH(ADDR_WIDTH + 1)
  ) sync_cdc_sync2_r2w_i (
      .clk  (w_clk),
      .rst_n(w_rst_n),
      .d    (r_ptr),
      .q    (w_q2_rptr)
  );

  svc_cdc_sync2 #(
      .WIDTH(ADDR_WIDTH + 1)
  ) svc_cdc_sync_w2r_i (
      .clk  (r_clk),
      .rst_n(r_rst_n),
      .d    (w_ptr),
      .q    (r_q2_wptr)
  );

  svc_cdc_fifo_mem #(
      .ADDR_WIDTH(ADDR_WIDTH),
      .DATA_WIDTH(DATA_WIDTH)
  ) svc_cdc_fifo_mem_i (
      .w_clk   (w_clk),
      .w_clk_en(w_inc),
      .w_full  (w_full),
      .w_addr  (w_addr),
      .w_data  (w_data),
      .r_addr  (r_addr),
      .r_data  (r_data)
  );

  svc_cdc_fifo_rptr_empty #(
      .ADDR_WIDTH(ADDR_WIDTH)
  ) svc_cdc_fifo_rptr_empty_i (
      .r_clk    (r_clk),
      .r_rst_n  (r_rst_n),
      .r_inc    (r_inc),
      .r_q2_wptr(r_q2_wptr),
      .r_empty  (r_empty),
      .r_ptr    (r_ptr),
      .r_addr   (r_addr)
  );

  svc_cdc_fifo_wptr_full #(
      .ADDR_WIDTH(ADDR_WIDTH)
  ) svc_cdc_fifo_wptr_full_i (
      .w_clk    (w_clk),
      .w_rst_n  (w_rst_n),
      .w_inc    (w_inc),
      .w_q2_rptr(w_q2_rptr),
      .w_full   (w_full),
      .w_ptr    (w_ptr),
      .w_addr   (w_addr)
  );

  // Ideally this would be formally verified here, using techniques from
  // https://github.com/ZipCPU/wb2axip/blob/master/rtl/afifo.v.
  //
  // But, given that this is a direct port of Starburst paper,
  // with only superficial changes, it's likely fine to skip it.


endmodule

`endif
