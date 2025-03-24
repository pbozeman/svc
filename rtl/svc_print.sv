`ifndef SVC_PRINT_SV
`define SVC_PRINT_SV

`include "svc.sv"
`include "svc_str.sv"
`include "svc_str_iter.sv"
`include "svc_unused.sv"

module svc_print (
    input logic clk,
    input logic rst_n,

    input  logic                     prn_en,
    input  logic [SVC_STR_WIDTH-1:0] prn_msg,
    input  logic                     prn_bin,
    input  logic [              3:0] prn_bin_len,
    output logic                     prn_busy,

    output logic       utx_en,
    output logic [7:0] utx_data,
    input  logic       utx_busy
);
  logic                     m_valid;
  logic [SVC_STR_WIDTH-1:0] m_msg;
  logic                     m_bin;
  logic [              3:0] m_bin_len;
  logic                     m_ready;

  logic                     s_valid;
  logic [              7:0] s_data;
  logic                     s_ready;

  svc_str_iter #(
      .MAX_STR_LEN(SVC_STR_MAX_LEN)
  ) svc_str_iter_i (
      .clk      (clk),
      .rst_n    (rst_n),
      .s_valid  (m_valid),
      .s_msg    (m_msg),
      .s_bin    (m_bin),
      .s_bin_len(m_bin_len),
      .s_ready  (m_ready),
      .m_valid  (s_valid),
      .m_char   (s_data),
      .m_ready  (s_ready)
  );

  assign prn_busy = m_valid || prn_en;
  assign s_ready  = !utx_busy;
  assign utx_en   = s_valid && !utx_busy;
  assign utx_data = s_data;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_valid <= 1'b0;
    end else begin
      m_valid <= m_valid && !m_ready;

      // this use to check valid, but it was hard to meet timing.
      // the caller shouldn't be toggling when valid is high anyway
      if (prn_en) begin
        m_valid   <= 1'b1;
        m_msg     <= prn_msg;
        m_bin     <= prn_bin;
        m_bin_len <= prn_bin_len;
      end
    end
  end

endmodule

// utx_en, data, and busy are passed in so the uart can be used with a mux
`define SVC_PRINT_INIT(utx_en, utx_data, utx_busy, clk = clk, rst_n = rst_n) \
  logic svc_prn_en;                                                          \
  logic [SVC_STR_WIDTH-1:0] svc_prn_msg;                                     \
  logic svc_prn_bin;                                                         \
  logic [3:0] svc_prn_bin_len;                                               \
  logic svc_prn_msg_busy;                                                    \
                                                                             \
  svc_print svc_print_i (                                                    \
      .clk        (clk),                                                     \
      .rst_n      (rst_n),                                                   \
      .prn_en     (svc_prn_en),                                              \
      .prn_msg    (svc_prn_msg),                                             \
      .prn_bin    (svc_prn_bin),                                             \
      .prn_bin_len(svc_prn_bin_len),                                         \
      .prn_busy   (svc_prn_msg_busy),                                        \
      .utx_en     (utx_en),                                                  \
      .utx_data   (utx_data),                                                \
      .utx_busy   (utx_busy)                                                 \
  );                                                                         \
                                                                             \
  `SVC_UNUSED({svc_prn_msg_busy});

`define SVC_PRINT_INIT_FF \
  svc_prn_en <= 1'b0;

`define SVC_PRINT(str)                                                       \
`ifndef VERILATOR                                                            \
  `SVC_STR_INIT(svc_prn_msg, str);                                           \
`else                                                                        \
  `SVC_STR_INIT(svc_prn_msg, "");                                            \
`endif                                                                       \
   svc_prn_bin <= 1'b0;                                                      \
   svc_prn_bin_len <= 0;                                                     \
   svc_prn_en <= 1'b1;

`define SVC_PRINT_BUSY svc_prn_msg_busy

`define SVC_PRINT_U8(val)                                                    \
   svc_str_init_val(svc_prn_msg, SVC_STR_WIDTH'(val));                       \
   svc_prn_bin <= 1'b1;                                                      \
   svc_prn_bin_len <= 1;                                                     \
   svc_prn_en <= 1'b1

`define SVC_PRINT_U32(val)                                                   \
   svc_str_init_val(svc_prn_msg, SVC_STR_WIDTH'(val));                       \
   svc_prn_bin <= 1'b1;                                                      \
   svc_prn_bin_len <= 4;                                                     \
   svc_prn_en <= 1'b1

`endif
