`ifndef SVC_AXI_BURST_ITER_AX_SV
`define SVC_AXI_BURST_ITER_AX_SV

`include "svc.sv"

// Iterates through AXI address bursts, where each iteration output
// can be used as a stand alone AR/AW request.
//
// There is an m_last to inform the downstream axi module about the end of the
// original burst.
//
// git commit 7da8fda73 replaced a zero latency version of this module with one
// that is pipelined. The zero latency version doubled the gate count
// of the pipelined version, and, was always showing up at the longest path
// in timing reports. It was also somewhat more complex conceptually than the
// pipelined version. So, while cool, it seemed like the tradeoff for
// 0 latency wasn't going to be worth it in the long run.
//
module svc_axi_burst_iter_ax #(
    parameter AXI_ADDR_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI Ax subordinate interface
    //
    input  logic                      s_valid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_addr,
    input  logic [  AXI_ID_WIDTH-1:0] s_id,
    input  logic [               7:0] s_len,
    input  logic [               2:0] s_size,
    input  logic [               1:0] s_burst,
    output logic                      s_ready,

    //
    // AXI Ax manager interface
    //
    output logic                      m_valid,
    output logic [AXI_ADDR_WIDTH-1:0] m_addr,
    output logic [  AXI_ID_WIDTH-1:0] m_id,
    output logic [               7:0] m_len,
    output logic [               2:0] m_size,
    output logic [               1:0] m_burst,
    output logic                      m_last,
    input  logic                      m_ready
);
  typedef enum {
    STATE_IDLE,
    STATE_BURST
  } state_t;

  state_t                      state;
  state_t                      state_next;

  logic                        s_ready_next;

  logic   [  AXI_ID_WIDTH-1:0] burst_id;
  logic   [  AXI_ID_WIDTH-1:0] burst_id_next;

  logic   [               7:0] burst_len;
  logic   [               7:0] burst_len_next;

  logic   [               2:0] burst_size;
  logic   [               2:0] burst_size_next;

  logic   [               1:0] burst_type;
  logic   [               1:0] burst_type_next;

  logic                        m_valid_next;
  logic   [AXI_ADDR_WIDTH-1:0] m_addr_next;
  logic                        m_last_next;

  assign m_id    = burst_id;
  assign m_len   = 0;
  assign m_size  = burst_size;
  assign m_burst = 0;

  always_comb begin
    state_next      = state;

    s_ready_next    = 1'b0;

    burst_id_next   = burst_id;
    burst_len_next  = burst_len;
    burst_size_next = burst_size;
    burst_type_next = burst_type;

    m_valid_next    = m_valid && !m_ready;
    m_addr_next     = m_addr;
    m_last_next     = m_last;

    case (state)
      STATE_IDLE: begin
        s_ready_next = 1'b1;

        if (s_valid && s_ready) begin
          state_next      = STATE_BURST;
          s_ready_next    = 1'b0;

          m_addr_next     = s_addr;
          burst_len_next  = s_len;
          burst_id_next   = s_id;
          burst_len_next  = s_len;
          burst_size_next = s_size;
          burst_type_next = s_burst;

          m_valid_next    = 1'b1;
          m_last_next     = s_len == 0;
        end
      end

      STATE_BURST: begin
        if (m_valid && m_ready) begin
          if (burst_len == 0) begin
            state_next   = STATE_IDLE;
            s_ready_next = 1'b1;
          end else begin
            m_valid_next   = 1'b1;
            burst_len_next = burst_len - 1;
            m_last_next    = burst_len_next == 0;
            if (burst_type != 2'b00) begin
              m_addr_next = m_addr + (1 << burst_size);
            end
          end
        end
      end

    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      state   <= STATE_IDLE;
      m_valid <= 1'b0;
      s_ready <= 1'b1;
    end else begin
      state   <= state_next;
      m_valid <= m_valid_next;
      s_ready <= s_ready_next;
    end
  end

  always_ff @(posedge clk) begin
    burst_id   <= burst_id_next;
    burst_len  <= burst_len_next;
    burst_size <= burst_size_next;
    burst_type <= burst_type_next;

    m_addr     <= m_addr_next;
    m_last     <= m_last_next;
  end

`ifdef FORMAL
`ifdef FORMAL_SVC_BURST_ITER_AX
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
`ifdef FORMAL_NO_SUBMODULES
  `define ASSERT(lable, a)
  `define ASSUME(lable, a)
  `define COVER(lable, a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif
`endif

  // This could get a lot more comprehensive asserts.
  //
  // However, this gets used in a larger axi design that runs through the
  // very comprehensive faxi verification modules, and I expect that it will
  // get a workout there. Any issues will get added as regression asserts
  // here. (Note: the integration with the larger module hadn't yet happened
  // at the time this comment was written.)

  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  //
  // assumptions
  //
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (s_valid) begin
        `ASSUME(am_size_valid, s_size == 3'b00 || s_size == 3'b01);
      end
      // stability
      if ($past(s_valid && !s_ready)) begin
        `ASSUME(am_valid, s_valid);
        `ASSUME(am_stable_addr, $stable(s_addr));
        `ASSUME(am_stable_id, $stable(s_id));
        `ASSUME(am_stable_len, $stable(s_len));
        `ASSUME(am_stable_size, $stable(s_size));
        `ASSUME(am_stable_burst, $stable(s_burst));
      end
    end
  end

  //
  // simple assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // m_ signals should be stable until accepted
      if ($past(m_valid && !m_ready) && !m_ready) begin
        `ASSERT(as_stable_addr, $stable(m_addr));
        `ASSERT(as_stable_id, $stable(m_id));
        `ASSERT(as_stable_len, $stable(m_len));
        `ASSERT(as_stable_size, $stable(m_size));
        `ASSERT(as_stable_burst, $stable(m_burst));
        `ASSERT(as_stable_last, $stable(m_last));

        if ($past(s_valid && s_ready && s_len == 0)) begin
          `ASSERT(as_initial_last, m_last == 1'b1);
        end
      end
    end
  end

  //
  // track and confirm the beats in a burst
  //
  int f_beats_remaining = 0;
  always @(posedge clk) begin
    if (!rst_n) begin
      f_beats_remaining <= 0;
    end else begin
      if (s_valid && s_ready) begin
        f_beats_remaining <= 32'(s_len);
      end

      if (m_valid && m_ready) begin
        if (f_beats_remaining == 0) begin
          `ASSERT(as_m_last, m_last == 1'b1);
          f_beats_remaining <= 0;
        end else begin
          `ASSERT(as_m_not_last, m_last == 1'b0);
          f_beats_remaining <= f_beats_remaining - 1;
        end
      end
    end
  end

  //
  // basic addr checks
  //
  logic [AXI_ADDR_WIDTH-1:0] f_addr_expected;
  logic [AXI_ADDR_WIDTH-1:0] f_addr_inc;

  always @(posedge clk) begin
    if (rst_n) begin
      if (s_valid && s_ready) begin
        f_addr_expected <= s_addr;

        if (s_burst == 2'b00) begin
          f_addr_inc <= 0;
        end else begin
          f_addr_inc <= 1 << s_size;
        end
      end else begin
        if (m_valid && m_ready) begin
          f_addr_expected <= f_addr_expected + f_addr_inc;
          `ASSERT(as_addr_calc, m_addr == f_addr_expected);
        end
      end
    end
  end

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif

endmodule
`endif
