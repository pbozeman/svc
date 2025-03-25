`ifndef SVC_HEX_FMT_STREAM_SV
`define SVC_HEX_FMT_STREAM_SV

`include "svc.sv"
`include "svc_hex_fmt.sv"
`include "svc_skidbuf.sv"

module svc_hex_fmt_stream #(
    parameter WIDTH      = 32,
    parameter USER_WIDTH = 1,
    parameter N          = WIDTH / 8
) (
    input logic clk,
    input logic rst_n,

    input  logic                  s_valid,
    input  logic [       8*N-1:0] s_data,
    input  logic [USER_WIDTH-1:0] s_user,
    output logic                  s_ready,

    output logic                  m_valid,
    output logic [      16*N-1:0] m_data,
    output logic [USER_WIDTH-1:0] m_user,
    input  logic                  m_ready
);
  localparam W = WIDTH;
  localparam UW = USER_WIDTH;
  localparam HW = WIDTH * 2;

  logic          sb_valid;
  logic [ W-1:0] sb_data;
  logic [UW-1:0] sb_user;
  logic          sb_ready;

  logic [HW-1:0] ascii_data;

  svc_skidbuf #(
      .DATA_WIDTH(WIDTH + USER_WIDTH),
      .OPT_OUTREG(1)
  ) svc_skidbuf_s_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_valid),
      .i_data ({s_user, s_data}),
      .o_ready(s_ready),

      .o_valid(sb_valid),
      .o_data ({sb_user, sb_data}),
      .i_ready(sb_ready)
  );

  svc_hex_fmt #(
      .WIDTH(WIDTH)
  ) svc_hex_fmt_i (
      .val  (sb_data),
      .ascii(ascii_data)
  );

  svc_skidbuf #(
      .DATA_WIDTH(HW + USER_WIDTH),
      .OPT_OUTREG(1)
  ) svc_skidbuf_m_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(sb_valid),
      .i_data ({sb_user, ascii_data}),
      .o_ready(sb_ready),

      .o_valid(m_valid),
      .o_data ({m_user, m_data}),
      .i_ready(m_ready)
  );

endmodule
`endif
