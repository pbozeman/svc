`ifndef SVC_CACHE_AXI_SV
`define SVC_CACHE_AXI_SV

`include "svc.sv"
`include "svc_sticky_bit.sv"
`include "svc_unused.sv"

//
// AXI-backed cache with valid/ready CPU interface
//
// Write Policy: Write-through with no-write-allocate
//   - Write hit:  Update cache AND write to memory
//   - Write miss: Write to memory only (no cache fill)
//
// Fill Buffer:
//   On cache miss, data is captured directly from AXI as each beat arrives
//   (fill_data_reg) rather than reading from data_table after the fill.
//   This avoids the BRAM read-after-write hazard that would return stale data.
//
//   Trade-off: Extra combinational logic to track which beat contains the
//   requested word and mux between current AXI data vs captured data.
//
// Partial Write Handling:
//   Partial writes (wr_strb != 4'b1111) invalidate the cache line rather than
//   updating it. This avoids read-modify-write which would require an extra
//   read port.
//
//   Trade-off: Subsequent reads to that line will miss and refetch from memory.
//   This only affects partial writes to already-cached lines.
//
//   Potential optimization: Pipeline the RMW by reading data_table on the
//   cycle before the write, then merge and write on the next cycle. This
//   would restore single-cycle hit latency for partial writes.
//
//   Potential optimizations:
//   - If CACHE_LINE_BYTES <= AXI_DATA_WIDTH/8 (single beat), the beat
//     tracking logic could be simplified
//   - Alternatively, (optionally) accept 1-cycle latency after fill_done
//     and read from data_table (simpler logic, higher latency)
//
// TODO: Future enhancements
//   - Write-allocate: On write miss, fetch line first then update
//   - Write-back: Track dirty bits, writeback on eviction
//
// TODO: the fill buffers are more vibe coded than the rest of the
// microarchitecture. Needs deeper review.
//
module svc_cache_axi #(
    parameter int CACHE_SIZE_BYTES = 4096,
    parameter int CACHE_ADDR_WIDTH = 32,
    parameter int CACHE_LINE_BYTES = 32,
    parameter bit TWO_WAY          = 0,
    parameter int AXI_ADDR_WIDTH   = 32,
    parameter int AXI_DATA_WIDTH   = 128,
    parameter int AXI_ID_WIDTH     = 4
) (
    input logic clk,
    input logic rst_n,

    //
    // Read interface
    //
    input  logic        rd_valid,
    input  logic [31:0] rd_addr,
    output logic        rd_ready,

    output logic [31:0] rd_data,
    output logic        rd_data_valid,

    // Read is a hit and rd_data_valid will go high next cycle if rd_valid
    // is raised. Note: this is speculative and only depends on rd_addr.
    output logic rd_hit,

    //
    // Write interface
    //
    input  logic        wr_valid,
    output logic        wr_ready,
    input  logic [31:0] wr_addr,
    input  logic [31:0] wr_data,
    input  logic [ 3:0] wr_strb,

    //
    // AXI4 manager interface
    //

    // Read address channel
    output logic                      m_axi_arvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,

    // Read data channel
    input  logic                      m_axi_rvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready,

    // Write address channel
    output logic                      m_axi_awvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    output logic [               1:0] m_axi_awburst,
    input  logic                      m_axi_awready,

    // Write data channel
    output logic                        m_axi_wvalid,
    output logic [  AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] m_axi_wstrb,
    output logic                        m_axi_wlast,
    input  logic                        m_axi_wready,

    // Write response channel
    input  logic                    m_axi_bvalid,
    input  logic [AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [             1:0] m_axi_bresp,
    output logic                    m_axi_bready
);
  // ===========================================================================
  // Cache geometry
  // ===========================================================================
  localparam int NUM_WAYS = TWO_WAY ? 2 : 1;
  localparam int NUM_LINES = CACHE_SIZE_BYTES / CACHE_LINE_BYTES;
  localparam int NUM_SETS = NUM_LINES / NUM_WAYS;
  localparam int WORDS_PER_LINE = CACHE_LINE_BYTES / 4;

  localparam int OFFSET_WIDTH = $clog2(CACHE_LINE_BYTES);
  localparam int SET_WIDTH = $clog2(NUM_SETS);
  localparam int TAG_WIDTH = CACHE_ADDR_WIDTH - SET_WIDTH - OFFSET_WIDTH;

  localparam int WORD_IDX_WIDTH = $clog2(WORDS_PER_LINE);

  // Per-way data RAM dimensions (no way bit in address for BRAM inference)
  localparam int DATA_WAY_DEPTH = NUM_SETS * WORDS_PER_LINE;
  localparam int DATA_WAY_AW = $clog2(DATA_WAY_DEPTH);

  localparam logic [AXI_ID_WIDTH-1:0] AXI_ID = 0;
  localparam int AXI_DATA_BYTES = AXI_DATA_WIDTH / 8;
  localparam int AXI_ARLEN = CACHE_LINE_BYTES / AXI_DATA_BYTES - 1;
  localparam int AXI_ARSIZE = $clog2(AXI_DATA_BYTES);
  localparam int WORDS_PER_BEAT = AXI_DATA_WIDTH / 32;

  // Width for fill word counter - at least 1 bit even when WORDS_PER_BEAT=1
  localparam int FILL_WORD_CNT_W = (WORDS_PER_BEAT > 1) ? $clog2(WORDS_PER_BEAT) : 1;

  // ===========================================================================
  // Signal declarations
  // ===========================================================================

  //
  // State machine
  //
  typedef enum {
    STATE_IDLE,
    STATE_READ_SETUP,
    STATE_READ_BURST,
    STATE_WRITE
  } state_t;

  state_t state;
  state_t state_next;

  //
  // Read address fields
  //
  logic [TAG_WIDTH-1:0] addr_tag;
  logic [SET_WIDTH-1:0] addr_set;
  logic [OFFSET_WIDTH-3:0] addr_offset;

  //
  // Cache storage
  //
  logic [TAG_WIDTH-1:0] tag_table[NUM_SETS][NUM_WAYS];
  logic valid_table[NUM_SETS][NUM_WAYS];
  logic lru_table[NUM_SETS];

  // Banked data RAMs - sync read enables BRAM inference
  // Indexed by {set, word_offset} - no way bit in address
  // verilog_format: off
  (* ram_style = "block" *) logic [31:0] data_way0[DATA_WAY_DEPTH];
  (* ram_style = "block" *) logic [31:0] data_way1[DATA_WAY_DEPTH];
  // verilog_format: on

  //
  // Cache lookup
  //
  (* max_fanout = 16 *)logic hit;
  (* max_fanout = 16 *)logic way0_hit;
  logic way1_hit;
  logic [31:0] hit_data;
  logic way0_valid;
  logic [TAG_WIDTH-1:0] way0_tag;
  logic way1_valid;
  logic [TAG_WIDTH-1:0] way1_tag;

  // Registered BRAM read outputs (sync read for BRAM inference)
  logic [31:0] way0_data_r;
  logic [31:0] way1_data_r;

  // Registered hit metadata to align with BRAM output timing
  logic way1_hit_r;

  //
  // Fill tracking
  //
  logic [WORD_IDX_WIDTH-1:0] beat_word_idx;
  logic [WORD_IDX_WIDTH-1:0] beat_word_idx_next;
  logic fill_way;
  logic fill_way_next;
  logic fill_done;
  logic fill_evict_way;

  //
  // Registered address for fill operations
  //
  // Captured on miss acceptance to ensure stable addressing throughout the
  // fill, even if rd_addr changes after handshake.
  //
  logic [TAG_WIDTH-1:0] fill_addr_tag;
  logic [SET_WIDTH-1:0] fill_addr_set;
  logic [OFFSET_WIDTH-3:0] fill_addr_offset;

  //
  // AXI read channel
  //
  logic m_axi_arvalid_next;
  logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr_next;
  logic [AXI_ADDR_WIDTH-1:0] fill_addr_line_aligned;

  //
  // Write address fields
  //
  logic [TAG_WIDTH-1:0] wr_addr_tag;
  logic [SET_WIDTH-1:0] wr_addr_set;
  logic [OFFSET_WIDTH-3:0] wr_addr_offset;

  //
  // Write hit detection
  //
  logic wr_way0_hit;
  logic wr_way1_hit;
  logic wr_hit;
  logic wr_hit_way;

  //
  // AXI write channel tracking
  //
  logic wr_start;
  logic aw_complete;
  logic w_complete;
  logic m_axi_awvalid_next;
  logic m_axi_wvalid_next;

  //
  // Cache response
  //
  logic rd_data_valid_next;

  // ===========================================================================
  // Read address field extraction
  // ===========================================================================
  (* max_fanout = 64, keep = "true" *) logic [CACHE_ADDR_WIDTH-1:0] rd_addr_fanout;
  assign rd_addr_fanout = rd_addr;

  assign addr_tag = rd_addr_fanout[31:32-TAG_WIDTH];
  assign addr_set = rd_addr_fanout[OFFSET_WIDTH+SET_WIDTH-1:OFFSET_WIDTH];
  assign addr_offset = rd_addr_fanout[OFFSET_WIDTH-1:2];

  // Line-aligned address from registered fill address (for STATE_READ_SETUP)
  // Truncate to AXI_ADDR_WIDTH (tag+set+offset may exceed AXI address width)
  assign fill_addr_line_aligned =
      AXI_ADDR_WIDTH'({fill_addr_tag, fill_addr_set, {OFFSET_WIDTH{1'b0}}});

  // ===========================================================================
  // Cache lookup
  // ===========================================================================

  //
  // Way 0 lookup
  //
  assign way0_valid = valid_table[addr_set][0];
  assign way0_tag = tag_table[addr_set][0];
  assign way0_hit = way0_valid && (way0_tag == addr_tag);

  //
  // Way 1 lookup (only for 2-way)
  //
  if (TWO_WAY) begin : gen_way1
    assign way1_valid = valid_table[addr_set][1];
    assign way1_tag   = tag_table[addr_set][1];
    assign way1_hit   = way1_valid && (way1_tag == addr_tag);
  end else begin : gen_no_way1
    assign way1_valid = 1'b0;
    assign way1_tag   = '0;
    assign way1_hit   = 1'b0;
  end

  // Combinational hit for state machine (same cycle as rd_valid)
  assign hit = way0_hit || way1_hit;

  //
  // Synchronous BRAM reads - output available next cycle
  // This enables BRAM inference instead of LUTRAM
  //
  logic [DATA_WAY_AW-1:0] data_rd_addr;
  assign data_rd_addr = {addr_set, addr_offset};

  always_ff @(posedge clk) begin
    way0_data_r <= data_way0[data_rd_addr];
    way1_data_r <= data_way1[data_rd_addr];
  end

  // Register hit metadata to align with BRAM output timing
  always_ff @(posedge clk) begin
    way1_hit_r <= way1_hit;
  end

  // Hit data mux uses registered signals (available cycle N+1)
  assign hit_data = way1_hit_r ? way1_data_r : way0_data_r;

  //
  // Select way for fill eviction (computed from registered fill_addr_set):
  // - Direct-mapped: always way 0
  // - 2-way: pick invalid way if available, else use LRU
  //
  // This is computed in STATE_READ_SETUP to break the timing path:
  //   rd_addr → hit → evict_way → state_next
  //
  if (TWO_WAY) begin : gen_fill_evict_2way
    always_comb begin
      if (!valid_table[fill_addr_set][0]) begin
        fill_evict_way = 1'b0;
      end else if (!valid_table[fill_addr_set][1]) begin
        fill_evict_way = 1'b1;
      end else begin
        fill_evict_way = lru_table[fill_addr_set];
      end
    end
  end else begin : gen_fill_evict_direct
    assign fill_evict_way = 1'b0;
  end

  // ===========================================================================
  // Write address field extraction
  // ===========================================================================
  assign wr_addr_tag = wr_addr[31:32-TAG_WIDTH];
  assign wr_addr_set = wr_addr[OFFSET_WIDTH+SET_WIDTH-1:OFFSET_WIDTH];
  assign wr_addr_offset = wr_addr[OFFSET_WIDTH-1:2];

  // ===========================================================================
  // Write hit detection
  // ===========================================================================
  assign wr_way0_hit = (valid_table[wr_addr_set][0] &&
                        (tag_table[wr_addr_set][0] == wr_addr_tag));

  if (TWO_WAY) begin : gen_wr_way1_hit
    assign wr_way1_hit = (valid_table[wr_addr_set][1] &&
                          (tag_table[wr_addr_set][1] == wr_addr_tag));
  end else begin : gen_wr_no_way1_hit
    assign wr_way1_hit = 1'b0;
  end

  assign wr_hit     = wr_way0_hit || wr_way1_hit;
  assign wr_hit_way = wr_way1_hit;

  // ===========================================================================
  // State machine
  // ===========================================================================
  always_comb begin
    state_next         = state;
    m_axi_arvalid_next = m_axi_arvalid & ~m_axi_arready;
    m_axi_araddr_next  = m_axi_araddr;
    m_axi_awvalid_next = m_axi_awvalid & ~m_axi_awready;
    m_axi_wvalid_next  = m_axi_wvalid & ~m_axi_wready;

    beat_word_idx_next  = beat_word_idx;
    fill_way_next       = fill_way;
    fill_done           = 1'b0;
    last_beat_rcvd_next = last_beat_rcvd;

    case (state)
      STATE_IDLE: begin
        if (rd_valid && !hit) begin
          state_next         = STATE_READ_SETUP;
          beat_word_idx_next = '0;
        end else if (wr_valid) begin
          state_next         = STATE_WRITE;
          m_axi_awvalid_next = 1'b1;
          m_axi_wvalid_next  = 1'b1;
        end
      end

      STATE_READ_SETUP: begin
        state_next          = STATE_READ_BURST;
        m_axi_arvalid_next  = 1'b1;
        m_axi_araddr_next   = fill_addr_line_aligned;
        fill_way_next       = fill_evict_way;
        last_beat_rcvd_next = 1'b0;
      end

      STATE_READ_BURST: begin
        if (m_axi_rvalid && m_axi_rready) begin
          beat_word_idx_next = beat_word_idx + WORD_IDX_WIDTH'(WORDS_PER_BEAT);
          if (m_axi_rlast) begin
            // Check if serialization is needed for this last beat
            if (!fill_beat_pending_next) begin
              // No serialization - done immediately (WORDS_PER_BEAT == 1)
              state_next = STATE_IDLE;
              fill_done  = 1'b1;
            end else begin
              // Serialization pending - wait for it to complete
              last_beat_rcvd_next = 1'b1;
            end
          end
        end
        // Check if serialization just completed for the last beat
        if (last_beat_rcvd && !fill_beat_pending_next) begin
          state_next          = STATE_IDLE;
          fill_done           = 1'b1;
          last_beat_rcvd_next = 1'b0;
        end
      end

      STATE_WRITE: begin
        // Both channels complete, return to idle
        if (aw_complete && w_complete) begin
          state_next = STATE_IDLE;
        end
      end

      default: begin
      end
    endcase
  end

  // ===========================================================================
  // State machine registration
  // ===========================================================================
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  // ===========================================================================
  // Fill tracking registration
  // ===========================================================================
  always_ff @(posedge clk) begin
    beat_word_idx <= beat_word_idx_next;
    fill_way      <= fill_way_next;
  end

  // ===========================================================================
  // Fill address registration
  // ===========================================================================
  //
  // Capture address fields when accepting a miss. This ensures the fill
  // writes to the correct cache location even if rd_addr changes after
  // the handshake.
  //
  always_ff @(posedge clk) begin
    if (state == STATE_IDLE && rd_valid && rd_ready) begin
      fill_addr_tag    <= addr_tag;
      fill_addr_set    <= addr_set;
      fill_addr_offset <= addr_offset;
    end
  end

  // ===========================================================================
  // Extract fill data from AXI
  // ===========================================================================
  //
  // Capture the requested word when its beat arrives during the fill.
  // We can't wait until fill_done because by then m_axi_rdata may contain
  // a different beat's data.
  //
  // Check if the current beat contains the requested word. A word is in
  // the current beat if: beat_word_idx <= fill_addr_offset < beat_word_idx + WORDS_PER_BEAT
  //
  logic                      fill_beat_hit;
  logic [WORD_IDX_WIDTH-1:0] fill_word_pos;
  logic [              31:0] fill_data_reg;
  logic [              31:0] fill_data;

  // Use wider arithmetic to avoid overflow when checking beat range
  assign fill_beat_hit = (fill_addr_offset >= beat_word_idx) &&
      ({1'b0, fill_addr_offset} <
       {1'b0, beat_word_idx} + (WORD_IDX_WIDTH + 1)'(WORDS_PER_BEAT));
  assign fill_word_pos = fill_addr_offset - beat_word_idx;

  // Capture the requested word when its beat arrives (on actual handshake)
  always_ff @(posedge clk) begin
    if (m_axi_rvalid && m_axi_rready && fill_beat_hit) begin
      fill_data_reg <= m_axi_rdata[fill_word_pos*32+:32];
    end
  end

  // Use captured data, or extract from current beat if it just arrived.
  // Only use live m_axi_rdata when a beat is actually arriving (handshake).
  // After serialization completes, beat_word_idx wraps to 0 which would
  // cause fill_beat_hit to incorrectly match - using fill_data_reg avoids this.
  assign fill_data = ((m_axi_rvalid && m_axi_rready && fill_beat_hit)
                      ? m_axi_rdata[fill_word_pos*32+:32]
                      : fill_data_reg);

  // ===========================================================================
  // Data table write (single write port for bram compatibility)
  // ===========================================================================
  //
  // Merge fill and write-through paths into single always_ff to enable
  // synthesis to simple dual-port RAM (1 read + 1 write).
  //
  // For WORDS_PER_BEAT > 1, fill writes are serialized across cycles.
  // This increases fill latency but maintains single-port compatibility.
  //

  // Combinational write control signals
  logic                      data_wr_en;
  logic [    SET_WIDTH-1:0]  data_wr_set;
  logic                      data_wr_way;
  logic [WORD_IDX_WIDTH-1:0] data_wr_idx;
  logic [             31:0]  data_wr_word;
  logic [              3:0]  data_wr_strb;

  // Fill word counter for serializing multi-word beats
  logic [FILL_WORD_CNT_W-1:0] fill_word_cnt;
  logic [FILL_WORD_CNT_W-1:0] fill_word_cnt_next;
  logic                              fill_beat_pending;
  logic                              fill_beat_pending_next;

  // Track when last AXI beat received but serialization still pending
  logic last_beat_rcvd;
  logic last_beat_rcvd_next;

  // Latch AXI data and beat index when beat arrives (for multi-word serialization)
  logic [  AXI_DATA_WIDTH-1:0] fill_beat_data;
  logic [WORD_IDX_WIDTH-1:0]   fill_beat_word_idx;

  always_comb begin
    data_wr_en   = 1'b0;
    data_wr_set  = '0;
    data_wr_way  = '0;
    data_wr_idx  = '0;
    data_wr_word = '0;
    data_wr_strb = 4'b1111;

    fill_word_cnt_next     = fill_word_cnt;
    fill_beat_pending_next = fill_beat_pending;

    // Fill path (higher priority) - write one word per cycle
    if (fill_beat_pending || (m_axi_rvalid && m_axi_rready)) begin
      data_wr_en  = 1'b1;
      data_wr_set = fill_addr_set;
      data_wr_way = fill_way;

      // Select word from current or latched beat data
      if (!fill_beat_pending) begin
        // First word of new beat - use current values
        data_wr_idx  = beat_word_idx + WORD_IDX_WIDTH'(fill_word_cnt);
        data_wr_word = m_axi_rdata[fill_word_cnt*32+:32];
      end else begin
        // Subsequent words - use latched values
        data_wr_idx  = fill_beat_word_idx + WORD_IDX_WIDTH'(fill_word_cnt);
        data_wr_word = fill_beat_data[fill_word_cnt*32+:32];
      end

      // Advance word counter
      if (fill_word_cnt == FILL_WORD_CNT_W'(WORDS_PER_BEAT - 1)) begin
        fill_word_cnt_next     = '0;
        fill_beat_pending_next = 1'b0;
      end else begin
        fill_word_cnt_next     = fill_word_cnt + 1'b1;
        fill_beat_pending_next = 1'b1;
      end
    end
    // Write-through path (only when idle and not filling)
    else if ((state == STATE_IDLE) && wr_valid && wr_hit) begin
      data_wr_en   = 1'b1;
      data_wr_set  = wr_addr_set;
      data_wr_way  = wr_hit_way;
      data_wr_idx  = wr_addr_offset;
      data_wr_word = wr_data;
      data_wr_strb = wr_strb;
    end
  end

  // Fill serialization state
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      fill_word_cnt     <= '0;
      fill_beat_pending <= 1'b0;
      last_beat_rcvd    <= 1'b0;
    end else begin
      fill_word_cnt     <= fill_word_cnt_next;
      fill_beat_pending <= fill_beat_pending_next;
      last_beat_rcvd    <= last_beat_rcvd_next;
    end
  end

  // Latch beat data and index for multi-word serialization
  always_ff @(posedge clk) begin
    if (m_axi_rvalid && m_axi_rready && !fill_beat_pending) begin
      fill_beat_data     <= m_axi_rdata;
      fill_beat_word_idx <= beat_word_idx;
    end
  end

  // Write to banked data RAMs
  //
  // For partial writes (strb != 4'b1111), we skip the cache update since this
  // is a write-through cache and memory has the correct data. The cache line
  // will be refetched on the next miss. This avoids needing read-modify-write
  // which would require an extra read port that iCE40 RAM4K doesn't support.
  //
  // Write address without way bit (for banked writes)
  logic [DATA_WAY_AW-1:0] data_wr_way_addr;
  assign data_wr_way_addr = {data_wr_set, data_wr_idx};

  // Write to banked RAMs - way select determines which bank
  always_ff @(posedge clk) begin
    if (data_wr_en && (data_wr_strb == 4'b1111)) begin
      if (!data_wr_way) begin
        data_way0[data_wr_way_addr] <= data_wr_word;
      end else begin
        data_way1[data_wr_way_addr] <= data_wr_word;
      end
    end
  end

  // ===========================================================================
  // Update valid on fill completion or partial write invalidation
  // ===========================================================================
  //
  // Partial writes (strb != 4'b1111) invalidate the cache line since we can't
  // do read-modify-write without an extra read port. The line will be refetched
  // from memory on the next access.
  //
  logic partial_write_hit;
  assign partial_write_hit = (state == STATE_IDLE) && wr_valid && wr_hit &&
                             (wr_strb != 4'b1111);

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int s = 0; s < NUM_SETS; s++) begin
        for (int w = 0; w < NUM_WAYS; w++) begin
          valid_table[s][w] <= 1'b0;
        end
      end
    end else if (partial_write_hit) begin
      valid_table[wr_addr_set][wr_hit_way] <= 1'b0;
    end else if (fill_done) begin
      valid_table[fill_addr_set][fill_way] <= 1'b1;
    end
  end

  // ===========================================================================
  // Update tag on fill completion
  // ===========================================================================
  always_ff @(posedge clk) begin
    if (fill_done) begin
      tag_table[fill_addr_set][fill_way] <= fill_addr_tag;
    end
  end

  // ===========================================================================
  // Update LRU on hit or fill (2-way only) - Deferred by one cycle
  // ===========================================================================

  //
  // LRU bit indicates which way to evict next (least recently used).
  // On access, mark the OTHER way as LRU.
  //
  // The LRU update is deferred by one cycle to break the critical timing path:
  //   rd_addr → tag_lookup → hit → lru_table → state_machine → BRAM_we
  //
  // Trade-off: LRU may be off by one access for back-to-back accesses to the
  // same set. This has negligible impact on miss rate.
  //
  if (TWO_WAY) begin : gen_lru_update
    // Deferred update state
    logic                 lru_update_valid;
    logic [SET_WIDTH-1:0] lru_update_set;
    logic                 lru_update_value;

    // Stage 1: Capture update request
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        lru_update_valid <= 1'b0;
      end else begin
        // Default: no update
        lru_update_valid <= 1'b0;

        // Read hit: mark the OTHER way as LRU
        if (rd_valid && hit) begin
          lru_update_valid <= 1'b1;
          lru_update_set   <= addr_set;
          lru_update_value <= ~way1_hit;
        end
        // Write hit: same LRU update
        else if (wr_valid && wr_ready && wr_hit) begin
          lru_update_valid <= 1'b1;
          lru_update_set   <= wr_addr_set;
          lru_update_value <= ~wr_way1_hit;
        end
        // Fill complete: mark filled way as MRU
        else if (fill_done) begin
          lru_update_valid <= 1'b1;
          lru_update_set   <= fill_addr_set;
          lru_update_value <= ~fill_way;
        end
      end
    end

    // Stage 2: Apply deferred update to LRU table
    always_ff @(posedge clk) begin
      if (lru_update_valid) begin
        lru_table[lru_update_set] <= lru_update_value;
      end
    end
  end else begin : gen_lru_unused
    for (genvar s = 0; s < NUM_SETS; s++) begin : gen_lru_zero
      assign lru_table[s] = 1'b0;
    end
  end

  // ===========================================================================
  // AXI read address channel
  // ===========================================================================
  always_ff @(posedge clk) begin
    m_axi_araddr <= m_axi_araddr_next;
  end

  assign m_axi_arid    = AXI_ID;
  assign m_axi_arlen   = AXI_ARLEN[7:0];
  assign m_axi_arsize  = AXI_ARSIZE[2:0];
  assign m_axi_arburst = 2'b01;
  // Stall AXI reads while serializing multi-word beats
  assign m_axi_rready  = !fill_beat_pending;

  // ===========================================================================
  // AXI write address channel
  // ===========================================================================
  assign m_axi_awid    = AXI_ID;
  assign m_axi_awaddr  = wr_addr[AXI_ADDR_WIDTH-1:0];
  assign m_axi_awlen   = 8'h00;
  assign m_axi_awsize  = 3'b010;
  assign m_axi_awburst = 2'b01;

  // ===========================================================================
  // AXI write data channel
  // ===========================================================================
  assign m_axi_wlast   = 1'b1;

  //
  // Shift data and strobe to correct position within AXI data width
  //
  if (AXI_DATA_WIDTH == 32) begin : gen_wdata_32
    assign m_axi_wdata = wr_data;
    assign m_axi_wstrb = wr_strb;
  end else begin : gen_wdata_wide
    localparam int AXI_WORD_OFFSET_BITS = $clog2(AXI_DATA_WIDTH / 32);

    logic [AXI_WORD_OFFSET_BITS-1:0] wr_axi_word_offset;
    assign wr_axi_word_offset = wr_addr[2+:AXI_WORD_OFFSET_BITS];

    always_comb begin
      m_axi_wdata                            = '0;
      m_axi_wstrb                            = '0;
      m_axi_wdata[wr_axi_word_offset*32+:32] = wr_data;
      m_axi_wstrb[wr_axi_word_offset*4+:4]   = wr_strb;
    end
  end

  //
  // Sticky bits track channel completion. Clear when starting new write,
  // set when respective handshake completes. Output is high when set or
  // when handshake occurs this cycle.
  //
  assign wr_start = (state == STATE_IDLE) && wr_valid;

  svc_sticky_bit svc_sticky_bit_aw_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clear(wr_start),
      .in   (m_axi_awvalid && m_axi_awready),
      .out  (aw_complete)
  );

  svc_sticky_bit svc_sticky_bit_w_i (
      .clk  (clk),
      .rst_n(rst_n),
      .clear(wr_start),
      .in   (m_axi_wvalid && m_axi_wready),
      .out  (w_complete)
  );

  // ===========================================================================
  // AXI write response channel
  // ===========================================================================
  assign m_axi_bready = 1'b1;

  // ===========================================================================
  // AXI valid registration
  // ===========================================================================
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_axi_arvalid <= 1'b0;
      m_axi_awvalid <= 1'b0;
      m_axi_wvalid  <= 1'b0;
    end else begin
      m_axi_arvalid <= m_axi_arvalid_next;
      m_axi_awvalid <= m_axi_awvalid_next;
      m_axi_wvalid  <= m_axi_wvalid_next;
    end
  end

  // ===========================================================================
  // Cache responses
  // ===========================================================================
  //
  // Use captured data for fill responses (avoids read-after-write hazard)
  //
  // hit_complete is explicitly (state == STATE_IDLE) rather than rd_ready
  // to make the timing path clear to the synthesizer.
  //
  logic hit_complete;
  assign hit_complete = (state == STATE_IDLE) && rd_valid && hit;
  assign rd_data_valid_next = hit_complete || fill_done;

  //
  // rd_data generation
  //
  // For hits: hit_data is derived from registered BRAM outputs (way*_data_r).
  // These are valid on the same cycle that rd_data_valid goes high, so no
  // additional register is needed.
  //
  // For fills: fill_data may be combinational from current AXI beat, so we
  // capture it when fill_done fires.
  //
  logic [31:0] fill_data_captured;
  logic        use_fill_data;

  always_ff @(posedge clk) begin
    if (fill_done) begin
      fill_data_captured <= fill_data;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      use_fill_data <= 1'b0;
    end else begin
      use_fill_data <= fill_done;
    end
  end

  // hit_data uses registered BRAM outputs, fill_data_captured is registered
  assign rd_data = use_fill_data ? fill_data_captured : hit_data;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rd_data_valid <= 1'b0;
    end else begin
      rd_data_valid <= rd_data_valid_next;
    end
  end

  // ===========================================================================
  // Cache ready signals
  // ===========================================================================
  assign rd_ready = (state == STATE_IDLE);
  assign rd_hit   = (state == STATE_IDLE) && hit;
  assign wr_ready = (state == STATE_WRITE) && (state_next == STATE_IDLE);
  // ===========================================================================
  // Unused signals
  // ===========================================================================
  `SVC_UNUSED({m_axi_arready, m_axi_rid, m_axi_rresp, m_axi_bid, m_axi_bresp,
               m_axi_bvalid, rd_addr_fanout[1:0], wr_addr[1:0]});

  if (AXI_ADDR_WIDTH < 32) begin : gen_unused_wr_addr_hi
    `SVC_UNUSED(wr_addr[31:AXI_ADDR_WIDTH]);
  end

  if (TWO_WAY == 0) begin : gen_unused_direct
    `SVC_UNUSED({way0_tag, way1_tag, way0_valid, way1_valid, lru_table,
                 data_wr_way, way1_data_r, way1_hit_r, data_way1});
  end

  // ===========================================================================
  // Formal verification
  // ===========================================================================
`ifdef FORMAL
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE

`ifdef FORMAL_SVC_CACHE_AXI
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)
`else
  `define FASSERT(label, a) label: assume(a)
  `define FASSUME(label, a) label: assert(a)
  `define FCOVER(label, a)
`endif

  logic f_past_valid = 0;

  always_ff @(posedge clk) begin
    f_past_valid <= 1;
  end

  //
  // Assumptions
  //
  initial begin
    assume (!rst_n);
  end

  //
  // Reset is monotonic: once released, stays released
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      `FASSUME(a_rst_n_stable, rst_n);
    end
  end

  always_ff @(posedge clk) begin
    `FASSUME(a_mutex_rd_wr, !(rd_valid && wr_valid));
  end

  //
  // Addresses must be word-aligned (we use 4-byte accesses)
  //
  always_comb begin
    `FASSUME(a_rd_addr_aligned, !rd_valid || rd_addr[1:0] == 2'b00);
    `FASSUME(a_wr_addr_aligned, !wr_valid || wr_addr[1:0] == 2'b00);
  end

  // ===========================================================================
  // Golden model: shadow memory for end-to-end data verification
  // ===========================================================================
  //
  // Track writes and constrain AXI to return coherent data. This verifies
  // rd_data correctness for both hits and fills.
  //
  localparam int F_MEM_AW = 10;
  localparam int F_MEM_DEPTH = 2 ** (F_MEM_AW - 2);

  // Shadow memory - tracks write values for golden model verification
  // Only tracks written addresses (f_written bitmap tracks validity)
  logic [31:0] f_mem[F_MEM_DEPTH];

  // Track which addresses have been written
  logic [F_MEM_DEPTH-1:0] f_written;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_written <= '0;
    end else if (wr_valid && wr_ready) begin
      f_written[wr_addr[F_MEM_AW-1:2]] <= 1'b1;
    end
  end

  // Constrain addresses to shadow memory range
  always_comb begin
    `FASSUME(a_rd_addr_range, !rd_valid || rd_addr[31:F_MEM_AW] == '0);
    `FASSUME(a_wr_addr_range, !wr_valid || wr_addr[31:F_MEM_AW] == '0);
  end

  // Track writes to shadow memory (with strobe support)
  always_ff @(posedge clk) begin
    if (wr_valid && wr_ready) begin
      if (wr_strb[0]) f_mem[wr_addr[F_MEM_AW-1:2]][7:0]   <= wr_data[7:0];
      if (wr_strb[1]) f_mem[wr_addr[F_MEM_AW-1:2]][15:8]  <= wr_data[15:8];
      if (wr_strb[2]) f_mem[wr_addr[F_MEM_AW-1:2]][23:16] <= wr_data[23:16];
      if (wr_strb[3]) f_mem[wr_addr[F_MEM_AW-1:2]][31:24] <= wr_data[31:24];
    end
  end

  // FIFO to track read addresses (handles multiple outstanding reads)
  // Depth 2 is sufficient since we can have at most 1 fill + 1 hit in flight
  localparam int F_RD_FIFO_DEPTH = 2;

  logic [F_MEM_AW-1:0] f_rd_fifo      [F_RD_FIFO_DEPTH];
  logic [           0:0] f_rd_fifo_wptr;
  logic [           0:0] f_rd_fifo_rptr;
  logic [           1:0] f_rd_fifo_cnt;

  // Current read address is at the head of the FIFO
  logic [F_MEM_AW-1:0] f_rd_addr;
  assign f_rd_addr = f_rd_fifo[f_rd_fifo_rptr];

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_rd_fifo_wptr <= '0;
      f_rd_fifo_rptr <= '0;
      f_rd_fifo_cnt  <= '0;
    end else begin
      // Push on read handshake
      if (rd_valid && rd_ready) begin
        f_rd_fifo[f_rd_fifo_wptr] <= rd_addr[F_MEM_AW-1:0];
        f_rd_fifo_wptr            <= f_rd_fifo_wptr + 1'b1;
      end

      // Pop on read data valid
      if (rd_data_valid) begin
        f_rd_fifo_rptr <= f_rd_fifo_rptr + 1'b1;
      end

      // Update count
      case ({rd_valid && rd_ready, rd_data_valid})
        2'b10:   f_rd_fifo_cnt <= f_rd_fifo_cnt + 1'b1;
        2'b01:   f_rd_fifo_cnt <= f_rd_fifo_cnt - 1'b1;
        default: ;
      endcase
    end
  end

  // Constrain AXI read responses to return written values
  // For addresses that have been written, AXI must return f_mem contents.
  // This models a coherent backing store.
  //
  // Calculate word address being fetched based on current beat
  logic [F_MEM_AW-1:0] f_line_base;
  logic [F_MEM_AW-1:0] f_axi_word_addr;

  assign f_line_base = {f_rd_addr[F_MEM_AW-1:OFFSET_WIDTH], {OFFSET_WIDTH{1'b0}}};
  assign f_axi_word_addr = f_line_base + (F_MEM_AW'(beat_word_idx) << 2);

  always_comb begin
    if (m_axi_rvalid && f_rd_fifo_cnt > 0) begin
      // Constrain low word if it was written
      if (f_written[f_axi_word_addr[F_MEM_AW-1:2]]) begin
        `FASSUME(a_axi_returns_written_lo,
                 m_axi_rdata[31:0] == f_mem[f_axi_word_addr[F_MEM_AW-1:2]]);
      end
    end
  end

  if (AXI_DATA_WIDTH >= 64) begin : gen_f_axi_wide
    always_comb begin
      if (m_axi_rvalid && f_rd_fifo_cnt > 0) begin
        // Constrain high word if it was written
        if (f_written[f_axi_word_addr[F_MEM_AW-1:2] + 1]) begin
          `FASSUME(a_axi_returns_written_hi,
                   m_axi_rdata[63:32] == f_mem[f_axi_word_addr[F_MEM_AW-1:2] + 1]);
        end
      end
    end
  end

  // Assert read data correctness for written addresses
  // Only check when FIFO has entries and address was previously written
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n && rd_data_valid && f_rd_fifo_cnt > 0 &&
        f_written[f_rd_addr[F_MEM_AW-1:2]]) begin
      `FASSERT(a_rd_data_golden, rd_data == f_mem[f_rd_addr[F_MEM_AW-1:2]]);
    end
  end

  //
  // When backpressured, inputs must be stable
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(rd_valid && !rd_ready)) begin
        `FASSUME(a_rd_valid_stable, rd_valid);
        `FASSUME(a_rd_addr_stable, $stable(rd_addr));
      end

      if ($past(wr_valid && !wr_ready)) begin
        `FASSUME(a_wr_valid_stable, wr_valid);
        `FASSUME(a_wr_addr_stable, $stable(wr_addr));
        `FASSUME(a_wr_data_stable, $stable(wr_data));
        `FASSUME(a_wr_strb_stable, $stable(wr_strb));
      end
    end
  end

  //
  // Request/response counting: responses should never exceed requests
  //
  logic [3:0] f_req_count;
  logic [3:0] f_resp_count;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_req_count  <= '0;
      f_resp_count <= '0;
    end else begin
      if (rd_valid && rd_ready) begin
        f_req_count <= f_req_count + 1'b1;
      end
      if (rd_data_valid) begin
        f_resp_count <= f_resp_count + 1'b1;
      end
    end
  end

  //
  // Internal state assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      `FASSERT(a_araddr_aligned,
               !m_axi_arvalid || m_axi_araddr[OFFSET_WIDTH-1:0] == '0);
      `FASSERT(a_resp_le_req, f_resp_count <= f_req_count);

      // rd_data_valid requires prior handshake or fill completion
      if (rd_data_valid && !$past(rd_data_valid)) begin
        `FASSERT(a_rd_data_valid_after_handshake, $past(
                 rd_valid && rd_ready && hit) || $past(fill_done));
      end

      // rd_valid && rd_hit implies rd_data_valid next cycle
      if ($past(rst_n) && $past(rd_valid && rd_hit)) begin
        `FASSERT(a_rd_hit_implies_rd_data_valid, rd_data_valid);
      end
    end
  end

  //
  // Address stability during fill
  //
  // Track the address that was accepted on a miss. The cache must use this
  // registered address (not the current rd_addr) for all fill operations.
  //
  logic [   TAG_WIDTH-1:0] f_req_tag;
  logic [   SET_WIDTH-1:0] f_req_set;
  logic [OFFSET_WIDTH-3:0] f_req_offset;
  logic                    f_req_pending;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_req_pending <= 1'b0;
    end else begin
      if (rd_valid && rd_ready && !hit) begin
        // Capture address on miss acceptance
        f_req_tag     <= addr_tag;
        f_req_set     <= addr_set;
        f_req_offset  <= addr_offset;
        f_req_pending <= 1'b1;
      end else if (fill_done) begin
        f_req_pending <= 1'b0;
      end
    end
  end

  //
  // During STATE_READ_BURST, the RTL's registered address fields must
  // match the originally accepted request
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n && f_req_pending) begin
      // The registered set used for data_table writes must be stable
      if (state == STATE_READ_BURST) begin
        `FASSERT(a_fill_set_stable, fill_addr_set == f_req_set);
        `FASSERT(a_fill_tag_stable, fill_addr_tag == f_req_tag);
      end

      // On fill completion, verify we're updating the correct location
      if (fill_done) begin
        `FASSERT(a_fill_done_set, fill_addr_set == f_req_set);
        `FASSERT(a_fill_done_tag, fill_addr_tag == f_req_tag);
        `FASSERT(a_fill_done_offset, fill_addr_offset == f_req_offset);
      end
    end
  end

  //
  // Fill data correctness verification
  //
  // Track data from each AXI beat and verify the correct word is returned.
  // This catches bugs where the wrong beat's data is used (e.g., due to
  // arithmetic overflow in beat range calculations).
  //
  localparam int F_BEATS_PER_LINE = CACHE_LINE_BYTES / (AXI_DATA_WIDTH / 8);

  // Capture data from each beat during fill
  logic [        AXI_DATA_WIDTH-1:0] f_beat_data[F_BEATS_PER_LINE];
  logic [$clog2(F_BEATS_PER_LINE):0] f_beat_idx;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_beat_idx <= '0;
    end else if (state == STATE_IDLE && state_next == STATE_READ_BURST) begin
      f_beat_idx <= '0;
    end else if (m_axi_rvalid && m_axi_rready) begin
      f_beat_data[f_beat_idx[$clog2(F_BEATS_PER_LINE)-1:0]] <= m_axi_rdata;
      f_beat_idx <= f_beat_idx + 1'b1;
    end
  end

  // Calculate which beat contains the requested word and its position
  logic [$clog2(F_BEATS_PER_LINE)-1:0] f_target_beat;
  logic [       FILL_WORD_CNT_W-1:0] f_word_in_target_beat;
  logic [                        31:0] f_expected_word;

  // When WORDS_PER_BEAT=1, each word is its own beat, so all offset bits
  // select the beat and there's no word-within-beat selection needed
  if (WORDS_PER_BEAT > 1) begin : gen_f_multi_word_beat
    assign f_target_beat = f_req_offset[WORD_IDX_WIDTH-1:$clog2(WORDS_PER_BEAT)];
    assign f_word_in_target_beat = f_req_offset[$clog2(WORDS_PER_BEAT)-1:0];
  end else begin : gen_f_single_word_beat
    assign f_target_beat         = f_req_offset;
    assign f_word_in_target_beat = '0;
  end
  assign f_expected_word =
      f_beat_data[f_target_beat][f_word_in_target_beat*32+:32];

  // When fill completes and rd_data_valid goes high, verify data correctness
  //
  // Check against what was actually stored in data RAMs. This catches bugs
  // where rd_data comes from the wrong source (e.g., stale fill_data
  // instead of the AXI data that was written to the table).
  //
  logic [31:0] f_stored_word;
  logic [DATA_WAY_AW-1:0] f_stored_way_addr;
  assign f_stored_way_addr = {f_req_set, f_req_offset};

  if (TWO_WAY) begin : gen_f_stored_2way
    assign f_stored_word = fill_way ? data_way1[f_stored_way_addr]
                                    : data_way0[f_stored_way_addr];
  end else begin : gen_f_stored_direct
    assign f_stored_word = data_way0[f_stored_way_addr];
  end

  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n && $past(rst_n)) begin
      // Check only when no new miss is being accepted (which would corrupt f_req_*)
      if (rd_data_valid && $past(fill_done) && !$past(rd_valid && rd_ready && !hit)) begin
        // rd_data must match what we stored in the cache
        // Skip when serialization is pending - data_table may not be fully updated
        // because fill_done fires before all words are written
        if (!fill_beat_pending) begin
          `FASSERT(a_fill_data_matches_table, rd_data == f_stored_word);
        end
        // And that should match what AXI delivered
        `FASSERT(a_fill_data_correct, rd_data == f_expected_word);
      end
    end
  end

  //
  // Covers
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      // Golden model: cover read and write paths
      `FCOVER(c_rd_data_valid, rd_data_valid);
      `FCOVER(c_wr_accepted, wr_valid && wr_ready);
      `FCOVER(c_read_written_addr,
              rd_data_valid && f_rd_fifo_cnt > 0 &&
              f_written[f_rd_addr[F_MEM_AW-1:2]]);

      `FCOVER(c_read_burst_start, $past(state
              ) == STATE_READ_SETUP && state == STATE_READ_BURST);
      `FCOVER(c_fill_done, fill_done);
      `FCOVER(c_hit_after_fill, $past(fill_done) && rd_valid && hit);

      // Cover fills where requested word is in different beats
      // These catches bugs in beat range calculations
      if (F_BEATS_PER_LINE > 1) begin
        // Word in first beat (beat 0)
        `FCOVER(c_fill_word_in_first_beat, fill_done && f_target_beat == 0);
        // Word in last beat
        `FCOVER(c_fill_word_in_last_beat,
                fill_done &&
                f_target_beat == $clog2(F_BEATS_PER_LINE)'(F_BEATS_PER_LINE - 1));
      end

      // Cover serialization path (WORDS_PER_BEAT > 1)
      if (WORDS_PER_BEAT > 1) begin
        // Serialization in progress (stalling AXI rready)
        `FCOVER(c_fill_beat_pending, fill_beat_pending);
        // Complete fill with serialization
        // fill_beat_pending is still high on the cycle fill_done fires
        // because we're finishing the last serialized word
        `FCOVER(c_fill_done_after_serialization,
                fill_done && fill_beat_pending);
      end
    end
  end

  //
  // AXI protocol verification
  //
  // verilator lint_off PINMISSING
  faxi_master #(
      .C_AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .C_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .F_OPT_INITIAL   (1'b0),
      .OPT_EXCLUSIVE   (1'b0),
      .OPT_NARROW_BURST(1'b1),
      .F_LGDEPTH       (9),
      .F_AXI_MAXSTALL  (2),
      .F_AXI_MAXRSTALL (2),
      .F_AXI_MAXDELAY  (2)
  ) faxi_manager_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      // Write address
      .i_axi_awvalid(m_axi_awvalid),
      .i_axi_awready(m_axi_awready),
      .i_axi_awid   (m_axi_awid),
      .i_axi_awaddr (m_axi_awaddr),
      .i_axi_awlen  (m_axi_awlen),
      .i_axi_awsize (m_axi_awsize),
      .i_axi_awburst(m_axi_awburst),
      .i_axi_awlock (1'b0),
      .i_axi_awcache(4'b0),
      .i_axi_awprot (3'b0),
      .i_axi_awqos  (4'b0),

      // Write data
      .i_axi_wvalid(m_axi_wvalid),
      .i_axi_wready(m_axi_wready),
      .i_axi_wdata (m_axi_wdata),
      .i_axi_wstrb (m_axi_wstrb),
      .i_axi_wlast (m_axi_wlast),

      // Write response
      .i_axi_bvalid(m_axi_bvalid),
      .i_axi_bready(m_axi_bready),
      .i_axi_bid   (m_axi_bid),
      .i_axi_bresp (m_axi_bresp),

      // Read address
      .i_axi_arvalid(m_axi_arvalid),
      .i_axi_arready(m_axi_arready),
      .i_axi_arid   (m_axi_arid),
      .i_axi_araddr (m_axi_araddr),
      .i_axi_arlen  (m_axi_arlen),
      .i_axi_arsize (m_axi_arsize),
      .i_axi_arburst(m_axi_arburst),
      .i_axi_arlock (1'b0),
      .i_axi_arcache(4'b0),
      .i_axi_arprot (3'b0),
      .i_axi_arqos  (4'b0),

      // Read data
      .i_axi_rvalid(m_axi_rvalid),
      .i_axi_rready(m_axi_rready),
      .i_axi_rdata (m_axi_rdata),
      .i_axi_rid   (m_axi_rid),
      .i_axi_rlast (m_axi_rlast),
      .i_axi_rresp (m_axi_rresp)
  );
  // verilator lint_on PINMISSING

  // Low bits unused since we word-address f_mem
  if (1) begin : gen_f_unused
    `SVC_UNUSED({f_rd_addr[1:0], f_axi_word_addr[1:0]});
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER

`endif
`endif

endmodule

`endif
