`ifndef SVC_RV_IMEM_CACHE_IF_SV
`define SVC_RV_IMEM_CACHE_IF_SV

`include "svc.sv"

//
// RISC-V Instruction Memory to Cache Interface Bridge
//
// Converts CPU imem pulse-based signals to cache valid/ready protocol.
// Read-only interface - no write support (instructions are not written).
// No I/O bypass - all accesses go through cache.
//
// Design choices:
//   * On cache HIT:
//       - rd_valid asserted in *same* cycle as imem_ren
//       - no imem_stall
//       - rd_data_valid from cache next cycle -> forwarded to imem_rdata
//   * On cache MISS:
//       - miss detected when a request is accepted and no response arrives
//         the next cycle
//       - imem_stall asserted while miss is in-flight and for one extra
//         cycle after the miss response (to use registered rdata)
//
module svc_rv_imem_cache_if (
    input logic clk,
    input logic rst_n,

    // CPU imem interface
    input  logic        imem_ren,
    input  logic [31:0] imem_raddr,
    output logic [31:0] imem_rdata,

    (* max_fanout = 16 *) output logic imem_stall,

    // Cache interface
    output logic        cache_rd_valid,
    output logic [31:0] cache_rd_addr,
    input  logic        cache_rd_ready,

    input logic [31:0] cache_rd_data,
    input logic        cache_rd_data_valid,
    input logic        cache_rd_hit
);
  //
  // State machine
  //
  typedef enum {
    STATE_IDLE,
    STATE_WAIT
  } state_t;

  state_t        state;
  state_t        state_next;

  //
  // Cache request tracking
  //
  logic          cache_rd_start;
  logic   [31:0] cache_rd_addr_reg;
  logic          cache_rd_fire;
  logic          cache_rd_fire_q;
  logic          cache_miss_detected;
  logic          cache_miss_inflight;
  logic          cache_miss_return_hold;

  //
  // Read data hold
  //
  logic   [31:0] rdata_reg_data;
  logic          rdata_reg_valid;

  //
  // Cache io start conditions and signals
  //
  // Detect miss in the cycle immediately after a request is accepted.
  //
  // Use cache_rd_hit (rather than cache_rd_data_valid) so miss detection
  // depends only on the tag compare result, not on the broader rd_data muxing
  // logic. This helps keep the stall path short without impacting hit latency.
  assign cache_miss_detected = (cache_rd_fire_q && !cache_rd_hit &&
                                !cache_miss_inflight);

  assign cache_rd_start = ((state == STATE_IDLE) && imem_ren &&
                           !cache_miss_inflight && !cache_miss_return_hold &&
                           !cache_miss_detected);

  assign cache_rd_valid = cache_rd_start || (state == STATE_WAIT);

  assign imem_stall = ((state == STATE_WAIT) || cache_miss_inflight ||
                       cache_miss_return_hold || cache_miss_detected);

  // Keep cache_rd_addr stable only when we must hold rd_valid high across
  // backpressure (STATE_WAIT). Do not select cache_rd_addr based on imem_stall
  // (or other cache-driven signals), to avoid a combinational timing path from
  // cache hit/miss determination back into the cache's BRAM address inputs.
  assign cache_rd_addr = (state == STATE_WAIT) ? cache_rd_addr_reg : imem_raddr;

  //
  // State machine for miss tracking
  //
  // imem_stall is set directly here based on state.
  //
  always_comb begin
    state_next = state;

    unique case (state)
      STATE_IDLE: begin
        if (cache_rd_start) begin
          if (!cache_rd_ready) begin
            state_next = STATE_WAIT;
          end
        end
      end

      STATE_WAIT: begin
        if (cache_rd_ready) begin
          state_next = STATE_IDLE;
        end
      end

      default: state_next = STATE_IDLE;
    endcase
  end

  assign cache_rd_fire = cache_rd_valid && cache_rd_ready;

  //
  // Registered state registers
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  //
  // Registered holds
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rdata_reg_valid        <= 1'b0;
      cache_rd_fire_q        <= 1'b0;
      cache_miss_inflight    <= 1'b0;
      cache_miss_return_hold <= 1'b0;
    end else if (cache_rd_data_valid) begin
      rdata_reg_valid <= 1'b1;
      cache_rd_fire_q <= cache_rd_fire;
      if (cache_miss_inflight) begin
        cache_miss_inflight    <= 1'b0;
        cache_miss_return_hold <= 1'b1;
      end else if (cache_miss_return_hold) begin
        cache_miss_return_hold <= 1'b0;
      end
    end else begin
      cache_rd_fire_q <= cache_rd_fire;
      if (cache_miss_detected) begin
        cache_miss_inflight <= 1'b1;
      end
      if (cache_miss_return_hold) begin
        cache_miss_return_hold <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      cache_rd_addr_reg <= '0;
    end else if (cache_rd_start) begin
      cache_rd_addr_reg <= imem_raddr;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rdata_reg_data <= 32'h00000013;
    end else if (cache_rd_data_valid) begin
      rdata_reg_data <= cache_rd_data;
    end
  end

  //
  // Read data mux
  //
  // Priority: cache data valid > registered hold
  //
  // - cache_rd_data_valid: live data from cache (hit or miss return)
  // - imem_stall/rdata_reg_valid: registered data hold (BRAM-style stable output)
  //
  always_comb begin
    if (cache_rd_data_valid) begin
      imem_rdata = cache_rd_data;
    end else if (imem_stall || rdata_reg_valid) begin
      imem_rdata = rdata_reg_data;
    end else begin
      imem_rdata = 32'h0;
    end
  end

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_IMEM_CACHE_IF
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)
`else
  `define FASSERT(label, a) label: assume(a)
  `define FASSUME(label, a) label: assert(a)
  `define FCOVER(label, a)
`endif

  logic f_past_valid = 1'b0;
  logic f_start_hit;
  logic f_hit_completing;
  logic f_wait_cache_inflight;
  logic f_miss_inflight;
  logic f_miss_returning;

  // cache_rd_start is defined in functional logic above
  assign f_start_hit           = cache_rd_data_valid && cache_rd_hit;
  assign f_hit_completing      = cache_rd_data_valid && cache_rd_hit;
  assign f_wait_cache_inflight = (state == STATE_WAIT);
  assign f_miss_inflight       = cache_miss_inflight;
  assign f_miss_returning      = cache_miss_return_hold;

  always_ff @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  initial begin
    assume (!rst_n);
    assume (f_rd_pending == 0);
    assume (f_expected_rdata == rdata_reg_data);
    assume (f_cache_load_pending == 0);
  end

  //
  // Track outstanding cache read requests
  //
  // cache_rd_data_valid should only occur when there's a pending request.
  // Use a counter: increment on request accepted, decrement on response.
  //
  logic [1:0] f_rd_pending;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_rd_pending <= 2'b0;
    end else begin
      case ({
        cache_rd_valid && cache_rd_ready, cache_rd_data_valid
      })
        2'b10:   f_rd_pending <= f_rd_pending + 1'b1;
        2'b01:   f_rd_pending <= f_rd_pending - 1'b1;
        default: f_rd_pending <= f_rd_pending;
      endcase
    end
  end

  //
  // Input assumptions
  //
  always_ff @(posedge clk) begin
    if (cache_rd_data_valid) begin
      `FASSUME(a_rd_data_valid_needs_pending, f_rd_pending > 0);
    end

    // cache_rd_hit implies cache_rd_data_valid in same cycle
    if (cache_rd_hit) begin
      `FASSUME(a_hit_implies_data_valid, cache_rd_data_valid);
    end

    // Hits return with fixed 1-cycle latency after a handshake.
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (cache_rd_data_valid && cache_rd_hit) begin
        `FASSUME(a_hit_timing, $past(cache_rd_valid && cache_rd_ready));
      end
    end
  end

  //
  // External assertions (module ports only)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cache miss stalls on detection
      if ($past(cache_rd_valid && cache_rd_ready) && !cache_rd_data_valid) begin
        `FASSERT(a_miss_stalls, imem_stall);
      end

      // Read valid/ready stability: valid stays high until ready
      if ($past(cache_rd_valid && !cache_rd_ready)) begin
        `FASSERT(a_rd_valid_stable, cache_rd_valid);
        `FASSERT(a_rd_addr_stable, cache_rd_addr == $past(cache_rd_addr));
      end
    end
  end

  //
  // Read data correctness (module ports only)
  //
  // Key contract: when imem_stall drops after a cache read,
  // imem_rdata must equal the cache_rd_data captured when
  // cache_rd_data_valid pulsed.
  //
  logic [31:0] f_expected_rdata;
  logic        f_cache_load_pending;

  always_ff @(posedge clk) begin
    if (cache_rd_data_valid) begin
      f_expected_rdata <= cache_rd_data;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_cache_load_pending <= 1'b0;
    end else begin
      // Track loads that actually STARTED, not just requests.
      if (cache_rd_start) begin
        f_cache_load_pending <= 1'b1;
      end else if (!imem_stall) begin
        f_cache_load_pending <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // When stall drops after a cache load, data should be correct.
      // Exclude f_hit_completing case - hits write data directly without stall.
      if ($past(
              imem_stall
          ) && !imem_stall && $past(
              f_cache_load_pending
          ) && !$past(
              f_hit_completing
          ) && !cache_rd_data_valid) begin
        `FASSERT(a_rdata_correct_on_complete, imem_rdata == f_expected_rdata);
      end
    end
  end

  //
  // Internal assertions (implementation details)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      if (f_start_hit) begin
        `FASSERT(a_hit_no_stall, !imem_stall);
      end

      if (f_miss_inflight) begin
        `FASSERT(a_miss_inflight_stalls, imem_stall);
      end

      if (f_miss_returning) begin
        `FASSERT(a_miss_returning_stalls, imem_stall);
      end

      if (f_wait_cache_inflight) begin
        `FASSERT(a_wait_cache_stalls, imem_stall);
      end
    end

    if (f_past_valid && !$past(rst_n)) begin
      `FASSERT(a_reset_no_wait_cache, !f_wait_cache_inflight);
      `FASSERT(a_reset_no_miss, !cache_miss_inflight);
      `FASSERT(a_reset_no_returning, !f_miss_returning);
      `FASSERT(a_reset_no_data_reg, !rdata_reg_valid);
    end

    if (f_past_valid && $past(rst_n) && rst_n) begin
      // When cache_rd_data_valid, imem_rdata uses live data
      if (cache_rd_data_valid) begin
        `FASSERT(a_rdata_live, imem_rdata == cache_rd_data);
      end

      // When rdata_reg_valid is active (not f_miss_returning), imem_rdata uses
      // rdata_reg_data
      if (rdata_reg_valid && !cache_rd_data_valid) begin
        `FASSERT(a_rdata_miss_reg, imem_rdata == rdata_reg_data);
      end
    end
  end


  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cache hit path (zero stall)
      `FCOVER(c_cache_hit, f_start_hit);
      `FCOVER(c_cache_hit_no_stall, f_start_hit && !imem_stall);

      // Cache miss path
      `FCOVER(c_cache_miss, cache_miss_detected);
      `FCOVER(c_wait_cache, f_wait_cache_inflight);
      `FCOVER(c_miss_inflight, f_miss_inflight);
      `FCOVER(c_miss_returning, f_miss_returning);
      `FCOVER(c_miss_complete, $past(f_miss_returning) && !f_miss_returning);

      // Back-to-back operations
      `FCOVER(c_back_to_back_hits, $past(f_start_hit) && f_start_hit);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
