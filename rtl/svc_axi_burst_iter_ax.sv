`ifndef SVC_AXI_BURST_ITER_AX_SV
`define SVC_AXI_BURST_ITER_AX_SV

`include "svc.sv"

// Iterates through AXI address bursts, where each iteration output
// can be used as a stand alone AR/AW request.
//
// This module operates with 0 latency, i.e. the m_valid signal
// goes high in the same clock cycle that s_valid does. This is
// like a skidbuffer that does a transform on the data that passes through it.
//
// There is an m_last to inform the downstream axi module about the end of the
// original burst.
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
  // initial burst signals
  logic                      burst_valid;
  logic                      burst_valid_next;

  logic [AXI_ADDR_WIDTH-1:0] burst_addr;
  logic [AXI_ADDR_WIDTH-1:0] burst_addr_next;

  logic [               7:0] burst_len;
  logic [               7:0] burst_len_next;

  // follow up beat signals after the initial beat
  logic                      beat_valid;
  logic                      beat_valid_next;

  logic [AXI_ADDR_WIDTH-1:0] beat_addr;
  logic [AXI_ADDR_WIDTH-1:0] beat_addr_next;

  logic [               7:0] beat_len;
  logic [               7:0] beat_len_next;

  // signals for initial + follow up beats
  logic [  AXI_ID_WIDTH-1:0] id;
  logic [  AXI_ID_WIDTH-1:0] id_next;

  logic [               2:0] size;
  logic [               2:0] size_next;

  logic [               1:0] burst;
  logic [               1:0] burst_next;

  // The addr and len to use are sort of like skid buffers, but with math
  // performed on the original signals. We use the current s_ values, or,
  // the original burst values, or the current beat values, depending on where
  // we are are in the flow, and if m_ready && m_value was true at the time s_valid
  // && s_ready was true.
  //
  // To my kids chagrin, I wanted to call these skibidi buffers.
  logic [AXI_ADDR_WIDTH-1:0] skidish_addr;
  logic [               7:0] skidish_len;

  logic [  AXI_ID_WIDTH-1:0] skidish_id;
  logic [               2:0] skidish_size;
  logic [               1:0] skidish_burst;

  // since the skibidi signals are the key to making this module zero latency,
  // lets set their values up front.
  always_comb begin
    if (burst_valid) begin
      skidish_addr = burst_addr;
      skidish_len  = burst_len;
    end else if (beat_valid) begin
      skidish_addr = beat_addr;
      skidish_len  = beat_len;
    end else if (s_valid) begin
      skidish_addr = s_addr;
      skidish_len  = s_len;
    end else begin
      skidish_addr = 0;
      skidish_len  = 0;
    end
  end

  always_comb begin
    if (burst_valid || beat_valid) begin
      skidish_id    = id;
      skidish_size  = size;
      skidish_burst = burst;
    end else if (s_valid) begin
      skidish_id    = s_id;
      skidish_size  = s_size;
      skidish_burst = s_burst;
    end else begin
      skidish_id    = 0;
      skidish_size  = 0;
      skidish_burst = 0;
    end
  end

  assign s_ready = !burst_valid && !beat_valid;

  assign m_valid = rst_n && (s_valid || burst_valid || beat_valid);
  assign m_addr  = skidish_addr;
  assign m_id    = skidish_id;
  assign m_size  = skidish_size;
  assign m_last  = skidish_len == 0;
  assign m_len   = 0;
  assign m_burst = 0;

  always_comb begin
    burst_valid_next = burst_valid;
    burst_addr_next  = burst_addr;
    burst_len_next   = burst_len;

    beat_valid_next  = beat_valid;
    beat_addr_next   = beat_addr;
    beat_len_next    = beat_len;

    id_next          = id;
    size_next        = size;
    burst_next       = burst;

    // burst is starting
    if (s_valid && s_ready) begin
      burst_valid_next = 1'b1;
      burst_addr_next  = s_addr;
      burst_len_next   = s_len;

      id_next          = s_id;
      size_next        = s_size;
      burst_next       = s_burst;

      beat_addr_next   = s_addr;

      if (s_len > 0) begin
        beat_valid_next = 1'b1;
        beat_len_next   = s_len - 1;
        if (s_burst != 2'b00) begin
          beat_addr_next = s_addr + (1 << s_size);
        end
      end
    end

    // a beat was accepted: note that this might still be in the same clock as
    // the burst acceptance above
    if (m_valid && m_ready) begin
      burst_valid_next = 1'b0;

      if (skidish_len == 0) begin
        beat_valid_next = 1'b0;
      end else begin
        beat_valid_next = 1'b1;
        beat_len_next   = skidish_len - 1;
        if (skidish_burst != 2'b00) begin
          beat_addr_next = skidish_addr + (1 << skidish_size);
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      burst_valid <= 1'b0;
      beat_valid  <= 1'b0;
    end else begin
      burst_valid <= burst_valid_next;
      burst_addr  <= burst_addr_next;
      burst_len   <= burst_len_next;

      beat_valid  <= beat_valid_next;
      beat_addr   <= beat_addr_next;
      beat_len    <= beat_len_next;

      id          <= id_next;
      size        <= size_next;
      burst       <= burst_next;
    end
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
      if ($past(m_valid && !m_ready)) begin
        `ASSERT(as_stable_addr, $stable(m_addr));
        `ASSERT(as_stable_id, $stable(m_id));
        `ASSERT(as_stable_len, $stable(m_len));
        `ASSERT(as_stable_size, $stable(m_size));
        `ASSERT(as_stable_burst, $stable(m_burst));
        `ASSERT(as_stable_last, $stable(m_last));

        if (s_valid && s_ready && s_len == 0) begin
          `ASSERT(as_immediate_last, m_last == 1'b1);
        end
      end
    end
  end

  //
  // track and confirm the beats in a burst
  //
  // (This, and the as_last asserts above, catch a surprising number of corner
  // cases.)
  int f_beats_remaining = 0;
  always @(posedge clk) begin
    if (!rst_n) begin
      f_beats_remaining <= 0;
    end else begin
      if (s_valid && s_ready) begin
        if (m_valid && m_ready && s_len > 0) begin
          f_beats_remaining <= int'(s_len) - 1;
        end else begin
          f_beats_remaining <= int'(s_len);
        end
      end else begin
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

        if (m_valid && m_ready) begin
          `ASSERT(as_fast_addr, m_addr == s_addr);
          if (s_burst != 2'b00) begin
            f_addr_expected <= s_addr + (1 << s_size);
          end
        end
      end else begin
        if (m_valid && m_ready) begin
          f_addr_expected <= f_addr_expected + f_addr_inc;
          `ASSERT(as_addr_calc, m_addr == f_addr_expected);
        end
      end
    end
  end
`endif

endmodule
`endif
