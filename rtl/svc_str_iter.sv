`ifndef SVC_STR_ITER_SV
`define SVC_STR_ITER_SV

`include "svc.sv"

// Iterator for ascii strings and bin to hex. It's a bit weird for this
// to double duty, but it makes it convenient to use with outputs without
// having to mux between strings and binary.
//
// I would prefer to use unpacked array, but yosys doesn't support them
// in ports

// verilator lint_off: UNUSEDSIGNAL
module svc_str_iter #(
    parameter MAX_STR_LEN = 128,
    parameter MSG_WIDTH   = MAX_STR_LEN * 8
) (
    input logic clk,
    input logic rst_n,

    // Input string interface
    input  logic                 s_valid,
    input  logic [MSG_WIDTH-1:0] s_msg,
    input  logic                 s_bin,
    input  logic [          3:0] s_bin_len,
    output logic                 s_ready,

    // Output character interface
    output logic       m_valid,
    output logic [7:0] m_char,
    input  logic       m_ready
);
  localparam IDX_W = $clog2(MAX_STR_LEN + 1);

  typedef enum {
    STATE_IDLE,
    STATE_ITER_STR,
    STATE_ITER_BIN_1,
    STATE_ITER_BIN_2
  } state_t;

  state_t             state;
  state_t             state_next;

  logic   [IDX_W-1:0] idx;
  logic   [IDX_W-1:0] idx_next;

  logic               m_valid_next;
  logic   [      7:0] m_char_next;

  // hex conversion table
  // verilog_format: off
  logic [7:0] hex_conv [15:0];
  // verilog_format: on
  assign hex_conv[4'h0] = 8'h30;
  assign hex_conv[4'h1] = 8'h31;
  assign hex_conv[4'h2] = 8'h32;
  assign hex_conv[4'h3] = 8'h33;
  assign hex_conv[4'h4] = 8'h34;
  assign hex_conv[4'h5] = 8'h35;
  assign hex_conv[4'h6] = 8'h36;
  assign hex_conv[4'h7] = 8'h37;
  assign hex_conv[4'h8] = 8'h38;
  assign hex_conv[4'h9] = 8'h39;
  assign hex_conv[4'hA] = 8'h61;
  assign hex_conv[4'hB] = 8'h62;
  assign hex_conv[4'hC] = 8'h63;
  assign hex_conv[4'hD] = 8'h64;
  assign hex_conv[4'hE] = 8'h65;
  assign hex_conv[4'hF] = 8'h66;

  logic [7:0] char;
  logic [3:0] nibble_1;
  logic [3:0] nibble_2;

  // for str conv
  assign char     = s_msg[8*idx+:8];

  // for hex conv
  assign nibble_1 = char[7:4];
  assign nibble_2 = char[3:0];

  always_comb begin
    state_next   = state;
    s_ready      = 1'b0;
    idx_next     = idx;

    m_valid_next = m_valid && !m_ready;
    m_char_next  = m_char;

    case (state)
      STATE_IDLE: begin
        m_char_next = 0;

        if (s_valid) begin
          if (!s_bin) begin
            state_next = STATE_ITER_STR;
            idx_next   = 0;
          end else begin
            state_next = STATE_ITER_BIN_1;
            idx_next   = IDX_W'(s_bin_len) - 1'b1;
          end
        end
      end

      STATE_ITER_STR: begin
        if (!m_valid || m_ready) begin
          if (char != 8'h00) begin
            m_valid_next = 1'b1;
            m_char_next  = char;
            idx_next     = idx + 1;
          end else begin
            s_ready    = 1'b1;
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_ITER_BIN_1: begin
        if (!m_valid || m_ready) begin
          if (idx < MAX_STR_LEN) begin
            m_valid_next = 1'b1;
            m_char_next  = hex_conv[nibble_1];
            state_next   = STATE_ITER_BIN_2;
          end else begin
            s_ready    = 1'b1;
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_ITER_BIN_2: begin
        if (!m_valid || m_ready) begin
          m_valid_next = 1'b1;
          m_char_next  = hex_conv[nibble_2];
          state_next   = STATE_ITER_BIN_1;
          idx_next     = idx - 1;
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state   <= STATE_IDLE;
      m_valid <= 1'b0;
    end else begin
      state   <= state_next;
      m_valid <= m_valid_next;
    end
  end

  always_ff @(posedge clk) begin
    idx    <= idx_next;
    m_char <= m_char_next;
  end

endmodule
`endif
