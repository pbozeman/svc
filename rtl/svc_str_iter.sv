`ifndef SVC_STR_ITER_SV
`define SVC_STR_ITER_SV

`include "svc.sv"

// Iterator for a null terminated string
//
// I would prefer to use unpacked array, but yosys doesn't support them
// in ports

module svc_str_iter #(
    parameter MAX_STR_LEN = 128,
    parameter MSG_WIDTH   = MAX_STR_LEN * 8
) (
    input logic clk,
    input logic rst_n,

    // Input string interface
    input  logic                 s_valid,
    input  logic [MSG_WIDTH-1:0] s_msg,
    output logic                 s_ready,

    // Output character interface
    output logic       m_valid,
    output logic [7:0] m_char,
    input  logic       m_ready
);
  localparam IDX_W = $clog2(MAX_STR_LEN);

  typedef enum {
    STATE_IDLE,
    STATE_ITER
  } state_t;

  state_t             state;
  state_t             state_next;

  logic   [IDX_W-1:0] idx;
  logic   [IDX_W-1:0] idx_next;

  logic               m_valid_next;
  logic   [      7:0] m_char_next;

  always_comb begin
    logic [7:0] char;

    state_next   = state;
    s_ready      = 1'b0;
    idx_next     = idx;
    char         = s_msg[8*idx+:8];

    m_valid_next = m_valid && !m_ready;
    m_char_next  = m_char;

    case (state)
      STATE_IDLE: begin
        m_char_next = 0;

        if (s_valid) begin
          state_next = STATE_ITER;
          idx_next   = 0;
        end
      end

      STATE_ITER: begin
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
