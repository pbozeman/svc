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
//       - imem_stall asserted while in STATE_MISS or STATE_MISS_RETURN
//       - STATE_MISS entered when we start a miss
//       - returns to IDLE when cache_rd_data_valid for the miss
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
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_WAIT_CACHE,
    STATE_MISS,
    STATE_MISS_RETURN
  } state_t;

  state_t        state;
  state_t        state_next;

  //
  // Cache request tracking
  //
  logic          cache_rd_start;
  logic   [31:0] cache_rd_addr_reg;

  //
  // Read data hold
  //
  logic   [31:0] rdata_reg_data;
  logic          rdata_reg_valid;

  //
  // Cache io start conditions and signals
  //
  always_comb begin
    cache_rd_start = (state == STATE_IDLE) && imem_ren;

    cache_rd_valid = cache_rd_start || (state == STATE_WAIT_CACHE);
    cache_rd_addr  = cache_rd_start ? imem_raddr : cache_rd_addr_reg;

    imem_stall     = state != STATE_IDLE;
  end

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
          if (cache_rd_ready) begin
            if (!cache_rd_hit) begin
              state_next = STATE_MISS;
            end
          end else begin
            state_next = STATE_WAIT_CACHE;
          end
        end
      end

      STATE_WAIT_CACHE: begin
        if (cache_rd_ready) begin
          if (cache_rd_hit) begin
            state_next = STATE_IDLE;
          end else begin
            state_next = STATE_MISS;
          end
        end
      end

      STATE_MISS: begin
        if (cache_rd_data_valid) begin
          state_next = STATE_MISS_RETURN;
        end
      end

      STATE_MISS_RETURN: begin
        state_next = STATE_IDLE;
      end

      default: state_next = STATE_IDLE;
    endcase
  end

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
      rdata_reg_valid <= 1'b0;
    end else begin
      rdata_reg_valid <=
          ((state == STATE_MISS_RETURN) ||
           (state == STATE_WAIT_CACHE && cache_rd_ready && cache_rd_hit));
    end
  end

  always_ff @(posedge clk) begin
    if (cache_rd_start) begin
      cache_rd_addr_reg <= imem_raddr;
    end

    if (cache_rd_data_valid) begin
      rdata_reg_data <= cache_rd_data;
    end
  end

  //
  // Read data mux
  //
  // Priority: cache data valid > stall/miss hold > default 0
  //
  // - cache_rd_data_valid: live data from cache (hit or miss return)
  // - stall/rdata_reg_valid: registered data during stall or miss completion
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
  assign f_start_hit = cache_rd_start && cache_rd_ready && cache_rd_hit;
  assign f_hit_completing = cache_rd_data_valid && (state == STATE_IDLE);
  assign f_wait_cache_inflight = (state == STATE_WAIT_CACHE);
  assign f_miss_inflight = (state == STATE_MISS);
  assign f_miss_returning = (state == STATE_MISS_RETURN);

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
    // cache_rd_data_valid requires a pending request OR simultaneous hit
    // (for immediate hits, request and response happen same cycle)
    if (cache_rd_data_valid) begin
      `FASSUME(a_rd_data_valid_needs_pending,
               f_rd_pending > 0 || (cache_rd_valid && cache_rd_ready));
    end

    // cache_rd_hit with valid handshake implies cache_rd_data_valid
    // in same cycle (hit returns data immediately for zero-stall hits)
    if (cache_rd_valid && cache_rd_ready && cache_rd_hit) begin
      `FASSUME(a_hit_implies_data_valid, cache_rd_data_valid);
    end
  end

  //
  // External assertions (module ports only)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cache miss stalls one cycle after detection (handshake must complete first)
      if ($past(
              cache_rd_valid && cache_rd_ready && !cache_rd_hit &&
                  !f_hit_completing
          )) begin
        `FASSERT(a_miss_stalls_next, imem_stall);
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

      if (f_miss_returning) begin
        `FASSERT(a_miss_returning_stalls, imem_stall);
      end

      if (f_wait_cache_inflight) begin
        `FASSERT(a_wait_cache_stalls, imem_stall);
      end
    end

    if (f_past_valid && !$past(rst_n)) begin
      `FASSERT(a_reset_no_wait_cache, !f_wait_cache_inflight);
      `FASSERT(a_reset_no_miss, !f_miss_inflight);
      `FASSERT(a_reset_no_returning, !f_miss_returning);
      `FASSERT(a_reset_no_data_reg, !rdata_reg_valid);
    end

    if (f_past_valid && $past(rst_n) && rst_n) begin
      // rdata_reg_valid follows f_miss_returning or wait_cache hit by one cycle
      if ($past(f_miss_returning)) begin
        `FASSERT(a_miss_data_reg_follows, rdata_reg_valid);
      end
      if ($past(
              f_wait_cache_inflight
          ) && $past(
              cache_rd_ready
          ) && $past(
              cache_rd_hit
          )) begin
        `FASSERT(a_wait_cache_hit_data_reg, rdata_reg_valid);
      end

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
      `FCOVER(c_cache_miss, cache_rd_start && cache_rd_ready && !cache_rd_hit);
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
