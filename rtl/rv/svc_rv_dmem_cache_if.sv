`ifndef SVC_RV_DMEM_CACHE_IF_SV
`define SVC_RV_DMEM_CACHE_IF_SV

`include "svc.sv"

//
// RISC-V Data Memory to Cache Interface Bridge
//
// Converts CPU dmem pulse-based signals to cache valid/ready protocol.
//
// I/O bypass: Addresses with bit 31 = 1 bypass the cache and connect
// directly to I/O. I/O has fixed 1-cycle BRAM timing.
//
// Design choices:
//   * On cache HIT:
//       - rd_valid asserted in *same* cycle as dmem_ren
//       - no dmem_stall
//       - rd_data_valid from cache next cycle -> forwarded to dmem_rdata
//   * On cache MISS:
//       - miss detected when a request is accepted and no response arrives
//         the next cycle
//       - dmem_stall asserted while miss is in-flight and for one extra
//         cycle after the miss response (to use registered rdata)
//   * Stores:
//       - write-through via cache
//       - STATE_STORE prevents new stores until cache_wr_ready pulses
//       - dmem_stall asserted while in STATE_STORE
//
module svc_rv_dmem_cache_if (
    input logic clk,
    input logic rst_n,

    // CPU dmem interface
    input  logic        dmem_ren,
    input  logic [31:0] dmem_raddr,
    output logic [31:0] dmem_rdata,

    input logic        dmem_we,
    input logic [31:0] dmem_waddr,
    input logic [31:0] dmem_wdata,
    input logic [ 3:0] dmem_wstrb,

    (* max_fanout = 16 *) output logic dmem_stall,

    // Cache interface
    output logic        cache_rd_valid,
    output logic [31:0] cache_rd_addr,
    input  logic        cache_rd_ready,

    input logic [31:0] cache_rd_data,
    input logic        cache_rd_data_valid,
    input logic        cache_rd_hit,

    output logic        cache_wr_valid,
    output logic [31:0] cache_wr_addr,
    output logic [31:0] cache_wr_data,
    output logic [ 3:0] cache_wr_strb,
    input  logic        cache_wr_ready,

    // I/O interface
    output logic        io_ren,
    output logic [31:0] io_raddr,
    input  logic [31:0] io_rdata,

    output logic        io_wen,
    output logic [31:0] io_waddr,
    output logic [31:0] io_wdata,
    output logic [ 3:0] io_wstrb
);
  //
  // State machine
  //
  typedef enum {
    STATE_IDLE,
    STATE_WAIT,
    STATE_STORE
  } state_t;

  state_t        state;
  state_t        state_next;

  //
  // Address decode
  //
  logic          io_sel_rd;
  logic          io_sel_wr;

  //
  // Decode and classify requests
  //
  logic          is_load;
  logic          is_store;
  logic          is_cache_load;
  logic          is_cache_store;

  //
  // Cache request tracking
  //
  logic          cache_rd_start;
  logic   [31:0] cache_rd_addr_reg;
  logic          cache_wr_start;
  logic   [31:0] cache_wr_addr_reg;
  logic   [31:0] cache_wr_data_reg;
  logic   [ 3:0] cache_wr_strb_reg;
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
  logic          io_sel_rd_p1;

  //
  // Address decode: bit 31 = 1 selects I/O
  //
  assign io_sel_rd = dmem_raddr[31];
  assign io_sel_wr = dmem_waddr[31];

  //
  // Decode and classify requests
  //
  assign is_load = dmem_ren && !dmem_we;
  assign is_store = dmem_we;
  assign is_cache_load = is_load && !io_sel_rd;
  assign is_cache_store = is_store && !io_sel_wr;

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

  assign cache_rd_start = ((state == STATE_IDLE) && is_cache_load &&
                           !cache_miss_inflight && !cache_miss_return_hold &&
                           !cache_miss_detected);

  assign cache_wr_start = ((state == STATE_IDLE) && is_cache_store &&
                           !cache_miss_inflight && !cache_miss_return_hold &&
                           !cache_miss_detected);

  assign cache_rd_valid = cache_rd_start || (state == STATE_WAIT);

  assign cache_wr_valid = cache_wr_start || (state == STATE_STORE);
  assign cache_wr_addr = cache_wr_start ? dmem_waddr : cache_wr_addr_reg;
  assign cache_wr_data = cache_wr_start ? dmem_wdata : cache_wr_data_reg;
  assign cache_wr_strb = cache_wr_start ? dmem_wstrb : cache_wr_strb_reg;

  assign dmem_stall = ((state != STATE_IDLE) || cache_miss_inflight ||
                       cache_miss_return_hold || cache_miss_detected);

  // Keep cache_rd_addr stable only when we must hold rd_valid high across
  // backpressure (STATE_WAIT). Do not select cache_rd_addr based on dmem_stall
  // (or other cache-driven signals), to avoid a combinational timing path from
  // cache hit/miss determination back into the cache's BRAM address inputs.
  assign cache_rd_addr = (state == STATE_WAIT) ? cache_rd_addr_reg : dmem_raddr;

  //
  // State machine for miss/store tracking
  //
  // dmem_stall is set directly here based on state.
  //
  always_comb begin
    state_next = state;

    unique case (state)
      STATE_IDLE: begin
        if (cache_wr_start) begin
          state_next = STATE_STORE;
        end else if (cache_rd_start) begin
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

      STATE_STORE: begin
        if (cache_wr_ready) begin
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
      rdata_reg_valid <= 1'b0;
      io_sel_rd_p1    <= 1'b0;
    end else begin
      rdata_reg_valid <= cache_miss_return_hold;

      if (is_load && !dmem_stall) begin
        io_sel_rd_p1 <= io_sel_rd;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      cache_rd_fire_q        <= 1'b0;
      cache_miss_inflight    <= 1'b0;
      cache_miss_return_hold <= 1'b0;
    end else begin
      cache_rd_fire_q <= cache_rd_fire;

      if (cache_miss_detected) begin
        cache_miss_inflight <= 1'b1;
      end

      if (cache_miss_inflight && cache_rd_data_valid) begin
        cache_miss_inflight    <= 1'b0;
        cache_miss_return_hold <= 1'b1;
      end else if (cache_miss_return_hold) begin
        cache_miss_return_hold <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      cache_rd_addr_reg <= 32'h0;
    end else if (cache_rd_start) begin
      cache_rd_addr_reg <= dmem_raddr;
    end

    if (cache_wr_start) begin
      cache_wr_addr_reg <= dmem_waddr;
      cache_wr_data_reg <= dmem_wdata;
      cache_wr_strb_reg <= dmem_wstrb;
    end

    if (cache_rd_data_valid) begin
      rdata_reg_data <= cache_rd_data;
    end
  end

  //
  // I/O read interface
  //
  assign io_ren   = dmem_ren && io_sel_rd;
  assign io_raddr = dmem_raddr;

  //
  // I/O write interface
  //
  assign io_wen   = dmem_we && io_sel_wr;
  assign io_waddr = dmem_waddr;
  assign io_wdata = dmem_wdata;
  assign io_wstrb = dmem_wstrb;

  //
  // Read data mux
  //
  // Priority: cache data valid > stall/miss hold > I/O > default 0
  //
  // - cache_rd_data_valid: live data from cache (hit or miss return)
  // - stall/rdata_reg_valid: registered data during stall or miss completion
  // - I/O: one-cycle BRAM timing via io_sel_rd_p1
  //
  always_comb begin
    if (cache_rd_data_valid) begin
      dmem_rdata = cache_rd_data;
    end else if ((dmem_stall || rdata_reg_valid) && !io_sel_rd_p1) begin
      dmem_rdata = rdata_reg_data;
    end else if (io_sel_rd_p1) begin
      dmem_rdata = io_rdata;
    end else begin
      dmem_rdata = 32'h0;
    end
  end

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_DMEM_CACHE_IF
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
  logic f_store_inflight;

  // cache_rd_start is defined in functional logic above
  assign f_start_hit           = cache_rd_data_valid && cache_rd_hit;
  assign f_hit_completing      = cache_rd_data_valid && cache_rd_hit;
  assign f_wait_cache_inflight = (state == STATE_WAIT);
  assign f_miss_inflight       = cache_miss_inflight;
  assign f_miss_returning      = cache_miss_return_hold;
  assign f_store_inflight      = (state == STATE_STORE);

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
    `FASSUME(a_no_simul_rd_wr, !(dmem_ren && dmem_we));
    `FASSUME(a_cache_mutex, !(cache_rd_data_valid && cache_wr_ready));

    // cache_rd_data_valid requires a pending request
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
    if (f_past_valid && rst_n) begin
      // I/O interface is combinational passthrough
      `FASSERT(a_io_ren, io_ren == (dmem_ren && dmem_raddr[31]));
      `FASSERT(a_io_wen, io_wen == (dmem_we && dmem_waddr[31]));
      `FASSERT(a_io_raddr, io_raddr == dmem_raddr);
      `FASSERT(a_io_waddr, io_waddr == dmem_waddr);
      `FASSERT(a_io_wdata, io_wdata == dmem_wdata);
      `FASSERT(a_io_wstrb, io_wstrb == dmem_wstrb);

      // Cache addresses never have I/O bit set
      if (cache_rd_valid) begin
        `FASSERT(a_rd_addr_not_io, !cache_rd_addr[31]);
      end
      if (cache_wr_valid) begin
        `FASSERT(a_wr_addr_not_io, !cache_wr_addr[31]);
      end
    end

    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cache miss stalls on detection
      if ($past(cache_rd_valid && cache_rd_ready) && !cache_rd_data_valid) begin
        `FASSERT(a_miss_stalls, dmem_stall);
      end

      // Read valid/ready stability: valid stays high until ready
      if ($past(cache_rd_valid && !cache_rd_ready)) begin
        `FASSERT(a_rd_valid_stable, cache_rd_valid);
        `FASSERT(a_rd_addr_stable, cache_rd_addr == $past(cache_rd_addr));
      end

      // Write valid/ready stability
      if ($past(cache_wr_valid && !cache_wr_ready)) begin
        `FASSERT(a_wr_valid_stable, cache_wr_valid);
        `FASSERT(a_wr_addr_stable, cache_wr_addr == $past(cache_wr_addr));
        `FASSERT(a_wr_data_stable, cache_wr_data == $past(cache_wr_data));
        `FASSERT(a_wr_strb_stable, cache_wr_strb == $past(cache_wr_strb));
      end
    end
  end

  //
  // Read data correctness (module ports only)
  //
  // Key contract: when dmem_stall drops after a cache read,
  // dmem_rdata must equal the cache_rd_data captured when
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
      // Blocked requests (e.g., during f_store_inflight) don't count.
      if (cache_rd_start) begin
        f_cache_load_pending <= 1'b1;
      end else if (!dmem_stall) begin
        f_cache_load_pending <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // When stall drops after a cache load (not I/O), data should be correct.
      // Exclude f_hit_completing case - hits write data directly without stall.
      // Exclude I/O reads which use io_rdata path.
      if ($past(
              dmem_stall
          ) && !dmem_stall && $past(
              f_cache_load_pending
          ) && !$past(
              dmem_raddr[31]
          ) && !$past(
              f_hit_completing
          ) && !cache_rd_data_valid && !io_sel_rd_p1) begin
        `FASSERT(a_rdata_correct_on_complete, dmem_rdata == f_expected_rdata);
      end
    end
  end

  //
  // Internal assertions (implementation details)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      if (f_start_hit && !f_store_inflight) begin
        `FASSERT(a_hit_no_stall, !dmem_stall);
      end

      if (f_store_inflight) begin
        `FASSERT(a_store_stalls, dmem_stall);
      end

      if (f_miss_inflight) begin
        `FASSERT(a_miss_inflight_stalls, dmem_stall);
      end

      if (f_miss_returning) begin
        `FASSERT(a_miss_returning_stalls, dmem_stall);
      end

      if (f_wait_cache_inflight) begin
        `FASSERT(a_wait_cache_stalls, dmem_stall);
      end
    end

    if (f_past_valid && !$past(rst_n)) begin
      `FASSERT(a_reset_no_wait_cache, !f_wait_cache_inflight);
      `FASSERT(a_reset_no_miss, !cache_miss_inflight);
      `FASSERT(a_reset_no_store, !f_store_inflight);
      `FASSERT(a_reset_no_returning, !f_miss_returning);
      `FASSERT(a_reset_no_data_reg, !rdata_reg_valid);
    end

    if (f_past_valid && $past(rst_n) && rst_n) begin
      // rdata_reg_valid follows miss return hold by one cycle
      if ($past(f_miss_returning)) begin
        `FASSERT(a_miss_data_reg_follows, rdata_reg_valid);
      end

      // When cache_rd_data_valid, dmem_rdata uses live data
      if (cache_rd_data_valid) begin
        `FASSERT(a_rdata_live, dmem_rdata == cache_rd_data);
      end

      // When rdata_reg_valid is active (not f_miss_returning), dmem_rdata uses
      // rdata_reg_data (unless I/O has priority)
      if (rdata_reg_valid && !cache_rd_data_valid && !io_sel_rd_p1) begin
        `FASSERT(a_rdata_miss_reg, dmem_rdata == rdata_reg_data);
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
      `FCOVER(c_cache_hit_no_stall, f_start_hit && !dmem_stall);

      // Cache miss path
      `FCOVER(c_cache_miss, cache_miss_detected);
      `FCOVER(c_wait_cache, f_wait_cache_inflight);
      `FCOVER(c_miss_inflight, f_miss_inflight);
      `FCOVER(c_miss_returning, f_miss_returning);
      `FCOVER(c_miss_complete, $past(f_miss_returning) && !f_miss_returning);

      // Store path
      `FCOVER(c_store_start, cache_wr_start);
      `FCOVER(c_store_inflight, f_store_inflight);
      `FCOVER(c_store_complete, $past(f_store_inflight) && !f_store_inflight);

      // I/O bypass
      `FCOVER(c_io_read, io_ren);
      `FCOVER(c_io_write, io_wen);

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
