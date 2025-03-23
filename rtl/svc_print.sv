`ifndef SVC_PRINT_SV
`define SVC_PRINT_SV

`include "svc.sv"
`include "svc_str.sv"
`include "svc_str_iter.sv"
`include "svc_unused.sv"

module svc_print (
    input logic clk,
    input logic rst_n,

    input  logic                     prn_toggle,
    input  logic [SVC_STR_WIDTH-1:0] prn_msg,
    output logic                     prn_busy,

    output logic       utx_en,
    output logic [7:0] utx_data,
    input  logic       utx_busy
);
  logic                     m_valid;
  logic [SVC_STR_WIDTH-1:0] m_msg;
  logic                     m_ready;

  logic                     s_valid;
  logic [              7:0] s_data;
  logic                     s_ready;

  logic                     prn_toggle_last;

  svc_str_iter #(
      .MAX_STR_LEN(SVC_STR_MAX_LEN)
  ) svc_str_iter_i (
      .clk    (clk),
      .rst_n  (rst_n),
      .s_valid(m_valid),
      .s_msg  (m_msg),
      .s_ready(m_ready),
      .m_valid(s_valid),
      .m_char (s_data),
      .m_ready(s_ready)
  );

  assign prn_busy = ((m_valid && !m_ready) || (prn_toggle != prn_toggle_last));
  assign s_ready  = !utx_busy;
  assign utx_en   = s_valid && !utx_busy;
  assign utx_data = s_data;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_valid         <= 1'b0;
      prn_toggle_last <= 1'b0;
    end else begin
      m_valid         <= m_valid && !m_ready;
      prn_toggle_last <= prn_toggle;

      if (!m_valid || m_ready) begin
        if (prn_toggle != prn_toggle_last) begin
          m_valid <= 1'b1;
          m_msg   <= prn_msg;
        end
      end
    end
  end
endmodule

// utx_en, data, and busy are passed in so the uart can be used with a mux
`define SVC_PRINT_INIT(utx_en, utx_data, utx_busy, clk = clk, rst_n = rst_n) \
  logic svc_prn_msg_toggle;                                                  \
  logic [SVC_STR_WIDTH-1:0] svc_prn_msg;                                     \
  logic svc_prn_msg_busy;                                                    \
                                                                             \
  initial svc_prn_msg_toggle = 1'b0;                                         \
                                                                             \
  svc_print svc_print_i (                                                    \
      .clk       (clk),                                                      \
      .rst_n     (rst_n),                                                    \
      .prn_toggle(svc_prn_msg_toggle),                                       \
      .prn_msg   (svc_prn_msg),                                              \
      .prn_busy  (svc_prn_msg_busy),                                         \
      .utx_en    (utx_en),                                                   \
      .utx_data  (utx_data),                                                 \
      .utx_busy  (utx_busy)                                                  \
  );                                                                         \
                                                                             \
  `SVC_UNUSED({svc_prn_msg_busy});

`define SVC_PRINT(str)                                                       \
`ifndef VERILATOR                                                            \
  `SVC_STR_INIT(svc_prn_msg, str);                                           \
`else                                                                        \
  `SVC_STR_INIT(svc_prn_msg, "");                                            \
`endif                                                                       \
   svc_prn_msg_toggle <= ~svc_prn_msg_toggle;

`define SVC_PRINT_BUSY svc_prn_msg_busy

`endif
