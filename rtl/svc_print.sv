`ifndef SVC_PRINT_SV
`define SVC_PRINT_SV

`include "svc.sv"
`include "svc_str_iter.sv"
`include "svc_unused.sv"

parameter SVC_STR_MAX_LEN = 128;
parameter SVC_STR_WIDTH = 8 * SVC_STR_MAX_LEN;

module svc_print (
    input logic clk,
    input logic rst_n,

    input  logic                     prn_en,
    input  logic [SVC_STR_WIDTH-1:0] prn_msg,
    input  logic                     prn_bin,
    input  logic [              3:0] prn_bin_len,
    output logic                     prn_busy,

    output logic       utx_valid,
    output logic [7:0] utx_data,
    input  logic       utx_ready
);
  logic                     m_valid;
  logic [SVC_STR_WIDTH-1:0] m_msg;
  logic                     m_bin;
  logic [              3:0] m_bin_len;
  logic                     m_ready;

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
      .m_valid  (utx_valid),
      .m_char   (utx_data),
      .m_ready  (utx_ready)
  );

  assign prn_busy = m_valid || prn_en;

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
`define SVC_PRINT_INIT(utx_valid, utx_data, utx_ready, clk = clk, rst_n = rst_n) \
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
      .utx_valid  (utx_valid),                                               \
      .utx_data   (utx_data),                                                \
      .utx_ready  (utx_ready)                                                \
  );                                                                         \
                                                                             \
  `SVC_UNUSED({svc_prn_msg_busy});

`define SVC_PRINT_INIT_FF \
  svc_prn_en <= 1'b0;

`define SVC_PRINT_BUSY svc_prn_msg_busy

// the lines sent to PRINT end in \r\n since that's the norm for serial comms.
// but when printed during a tb, the \r results in an extra new line.
// just strip it all off and use display when printing strings
`ifdef SVC_TB_PRINT
function automatic string svc_strip_crlf(input string s);
  int last = s.len() - 1;

  if (last >= 0 && s[last] == "\n") last--;
  if (last >= 0 && s[last] == "\r") last--;

  svc_strip_crlf = s.substr(0, last);
endfunction
`endif

`define SVC_PRINT_U8(val)                                                    \
   svc_prn_msg <= SVC_STR_WIDTH'(val);                                       \
   svc_prn_bin <= 1'b1;                                                      \
   svc_prn_bin_len <= 1;                                                     \
   svc_prn_en <= 1'b1;                                                       \
   `ifdef SVC_TB_PRINT                                                       \
     $write("%0h", val);                                                     \
   `endif

`define SVC_PRINT_U16(val)                                                   \
   svc_prn_msg <= SVC_STR_WIDTH'(val);                                       \
   svc_prn_bin <= 1'b1;                                                      \
   svc_prn_bin_len <= 2;                                                     \
   svc_prn_en <= 1'b1;                                                       \
   `ifdef SVC_TB_PRINT                                                       \
     $write("%0h", val);                                                     \
   `endif

`define SVC_PRINT_U32(val)                                                   \
   svc_prn_msg <= SVC_STR_WIDTH'(val);                                       \
   svc_prn_bin <= 1'b1;                                                      \
   svc_prn_bin_len <= 4;                                                     \
   svc_prn_en <= 1'b1;                                                       \
   `ifdef SVC_TB_PRINT                                                       \
     $write("%0h", val);                                                     \
   `endif

`define SVC_PRINT(val)                                                       \
   svc_prn_msg <= SVC_STR_WIDTH'(val);                                       \
   svc_prn_bin <= 1'b0;                                                      \
   svc_prn_bin_len <= 0;                                                     \
   svc_prn_en <= 1'b1;                                                       \
   `ifdef SVC_TB_PRINT                                                       \
      $display("%s", svc_strip_crlf(val))                                    \
   `endif

`endif
