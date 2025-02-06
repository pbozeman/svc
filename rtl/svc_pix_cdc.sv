`ifndef SVC_PIX_CDC_SV
`define SVC_PIX_CDC_SV

`include "svc.sv"
`include "svc_cdc_fifo.sv"

module svc_pix_cdc #(
    parameter COLOR_WIDTH     = 4,
    parameter FIFO_ADDR_WIDTH = 3
) (
    //
    // s side is in the main clock domain
    //
    input logic s_clk,
    input logic s_rst_n,

    input  logic                   s_pix_valid,
    input  logic [COLOR_WIDTH-1:0] s_pix_red,
    input  logic [COLOR_WIDTH-1:0] s_pix_grn,
    input  logic [COLOR_WIDTH-1:0] s_pix_blu,
    output logic                   s_pix_ready,

    //
    // m side in the pixel clock domain
    //
    input logic m_clk,
    input logic m_rst_n,

    output logic                   m_pix_valid,
    output logic [COLOR_WIDTH-1:0] m_pix_red,
    output logic [COLOR_WIDTH-1:0] m_pix_grn,
    output logic [COLOR_WIDTH-1:0] m_pix_blu,
    input  logic                   m_pix_ready
);
  logic s_full;
  assign s_pix_ready = !s_full;

  logic m_empty;
  assign m_pix_valid = !m_empty;

  // ship it
  svc_cdc_fifo #(
      .DATA_WIDTH(COLOR_WIDTH * 3),
      .ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) cdc_fifo_i (
      .w_clk  (s_clk),
      .w_rst_n(s_rst_n),
      .w_inc  (s_pix_valid && s_pix_ready),
      .w_data ({s_pix_red, s_pix_grn, s_pix_blu}),
      .w_full (s_full),

      .r_clk  (m_clk),
      .r_rst_n(m_rst_n),
      .r_inc  (m_pix_valid && m_pix_ready),
      .r_empty(m_empty),
      .r_data ({m_pix_red, m_pix_grn, m_pix_blu})
  );

endmodule
`endif
