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
// TODO: Future enhancements
//   - Write-allocate: On write miss, fetch line first then update
//   - Write-back: Track dirty bits, writeback on eviction
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

  localparam logic [AXI_ID_WIDTH-1:0] AXI_ID = 0;
  localparam int AXI_DATA_BYTES = AXI_DATA_WIDTH / 8;
  localparam int AXI_ARLEN = CACHE_LINE_BYTES / AXI_DATA_BYTES - 1;
  localparam int AXI_ARSIZE = $clog2(AXI_DATA_BYTES);
  localparam int WORDS_PER_BEAT = AXI_DATA_WIDTH / 32;

  // ===========================================================================
  // Signal declarations
  // ===========================================================================

  //
  // State machine
  //
  typedef enum {
    STATE_IDLE,
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

  (* ram_style = "block" *)
  logic [31:0] data_table[NUM_SETS][NUM_WAYS][WORDS_PER_LINE];

  //
  // Cache lookup
  //
  logic hit;
  logic way0_hit;
  logic way1_hit;
  logic [31:0] hit_data;
  logic way0_valid;
  logic [TAG_WIDTH-1:0] way0_tag;
  logic [31:0] way0_data;
  logic way1_valid;
  logic [TAG_WIDTH-1:0] way1_tag;
  logic [31:0] way1_data;

  //
  // Fill tracking
  //
  logic [WORD_IDX_WIDTH-1:0] beat_word_idx;
  logic [WORD_IDX_WIDTH-1:0] beat_word_idx_next;
  logic fill_way;
  logic fill_way_next;
  logic fill_done;
  logic evict_way;
  logic [31:0] fill_data;

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
  logic [AXI_ADDR_WIDTH-1:0] addr_line_aligned;

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
  assign addr_tag = rd_addr[31:32-TAG_WIDTH];
  assign addr_set = rd_addr[OFFSET_WIDTH+SET_WIDTH-1:OFFSET_WIDTH];
  assign addr_offset = rd_addr[OFFSET_WIDTH-1:2];

  assign addr_line_aligned = {
    rd_addr[AXI_ADDR_WIDTH-1:OFFSET_WIDTH], {OFFSET_WIDTH{1'b0}}
  };

  // ===========================================================================
  // Cache lookup
  // ===========================================================================

  //
  // Way 0 lookup
  //
  assign way0_valid = valid_table[addr_set][0];
  assign way0_tag = tag_table[addr_set][0];
  assign way0_data = data_table[addr_set][0][addr_offset];
  assign way0_hit = way0_valid && (way0_tag == addr_tag);

  //
  // Way 1 lookup (only for 2-way)
  //
  if (TWO_WAY) begin : gen_way1
    assign way1_valid = valid_table[addr_set][1];
    assign way1_tag   = tag_table[addr_set][1];
    assign way1_data  = data_table[addr_set][1][addr_offset];
    assign way1_hit   = way1_valid && (way1_tag == addr_tag);
  end else begin : gen_no_way1
    assign way1_valid = 1'b0;
    assign way1_tag   = '0;
    assign way1_data  = '0;
    assign way1_hit   = 1'b0;
  end

  assign hit      = way0_hit || way1_hit;
  assign hit_data = way1_hit ? way1_data : way0_data;

  //
  // Select way for eviction:
  // - Direct-mapped: always way 0
  // - 2-way: pick invalid way if available, else use LRU
  //
  if (TWO_WAY) begin : gen_evict_2way
    always_comb begin
      if (!way0_valid) begin
        evict_way = 1'b0;
      end else if (!way1_valid) begin
        evict_way = 1'b1;
      end else begin
        evict_way = lru_table[addr_set];
      end
    end
  end else begin : gen_evict_direct
    assign evict_way = 1'b0;
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

    beat_word_idx_next = beat_word_idx;
    fill_way_next      = fill_way;
    fill_done          = 1'b0;

    case (state)
      STATE_IDLE: begin
        if (rd_valid && !hit) begin
          state_next         = STATE_READ_BURST;
          m_axi_arvalid_next = 1'b1;

          // Align read to cache line and capture fill target
          m_axi_araddr_next  = addr_line_aligned;
          beat_word_idx_next = '0;
          fill_way_next      = evict_way;
        end else if (wr_valid) begin
          state_next         = STATE_WRITE;
          m_axi_awvalid_next = 1'b1;
          m_axi_wvalid_next  = 1'b1;
        end
      end

      STATE_READ_BURST: begin
        // m_axi_rready is always true, so we accept data every cycle
        if (m_axi_rvalid) begin
          beat_word_idx_next = beat_word_idx + WORD_IDX_WIDTH'(WORDS_PER_BEAT);
          if (m_axi_rlast) begin
            state_next = STATE_IDLE;
            fill_done  = 1'b1;
          end
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
    if (state == STATE_IDLE && rd_valid && !hit) begin
      fill_addr_tag    <= addr_tag;
      fill_addr_set    <= addr_set;
      fill_addr_offset <= addr_offset;
    end
  end

  // ===========================================================================
  // Cache update on write hit
  // ===========================================================================

  //
  // Write-through: update cache when we accept the write (before STATE_WRITE)
  //
  always_ff @(posedge clk) begin
    if ((state == STATE_IDLE) && wr_valid && wr_hit) begin
      if (wr_strb[0])
        data_table[wr_addr_set][wr_hit_way][wr_addr_offset][7:0] <=
            wr_data[7:0];
      if (wr_strb[1])
        data_table[wr_addr_set][wr_hit_way][wr_addr_offset][15:8] <=
            wr_data[15:8];
      if (wr_strb[2])
        data_table[wr_addr_set][wr_hit_way][wr_addr_offset][23:16] <=
            wr_data[23:16];
      if (wr_strb[3])
        data_table[wr_addr_set][wr_hit_way][wr_addr_offset][31:24] <=
            wr_data[31:24];
    end
  end

  // ===========================================================================
  // Data table write on each AXI beat
  // ===========================================================================

  //
  // With 128-bit AXI, this writes 4 words (128 bits) per cycle. This exceeds
  // single BRAM write width (72 bits max on Xilinx), so synthesizer will
  // bank multiple BRAMs in parallel. Prioritizes fill latency over BRAM count.
  //
  always_ff @(posedge clk) begin
    if (state == STATE_READ_BURST && m_axi_rvalid) begin
      for (int i = 0; i < WORDS_PER_BEAT; i++) begin
        data_table[fill_addr_set][fill_way][beat_word_idx+WORD_IDX_WIDTH'(i)] <=
            m_axi_rdata[i*32+:32];
      end
    end
  end

  // ===========================================================================
  // Update valid on fill completion
  // ===========================================================================
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int s = 0; s < NUM_SETS; s++) begin
        for (int w = 0; w < NUM_WAYS; w++) begin
          valid_table[s][w] <= 1'b0;
        end
      end
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
  // Update LRU on hit or fill (2-way only)
  // ===========================================================================

  //
  // LRU bit indicates which way to evict next (least recently used).
  // On access, mark the OTHER way as LRU.
  //
  if (TWO_WAY) begin : gen_lru_update
    always_ff @(posedge clk) begin
      if (rd_valid && hit) begin
        lru_table[addr_set] <= ~way1_hit;
      end else if (wr_valid && wr_ready && wr_hit) begin
        lru_table[wr_addr_set] <= ~wr_way1_hit;
      end else if (fill_done) begin
        lru_table[fill_addr_set] <= ~fill_way;
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
  assign m_axi_rready  = 1'b1;

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
  assign fill_data = data_table[fill_addr_set][fill_way][fill_addr_offset];
  assign rd_data_valid_next = (rd_valid && rd_ready && hit) || fill_done;

  //
  // rd_data registration
  //
  // Register rd_data when rd_data_valid_next is high. This ensures rd_data
  // is stable and correct when rd_data_valid goes high on the next cycle.
  // Without this, fill responses would use hit_data (derived from current
  // rd_addr) instead of the registered fill address.
  //
  logic [31:0] rd_data_reg;

  always_ff @(posedge clk) begin
    if (rd_data_valid_next) begin
      rd_data_reg <= fill_done ? fill_data : hit_data;
    end
  end

  assign rd_data = rd_data_reg;

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
  assign rd_ready = (state == STATE_IDLE) || (state != STATE_READ_BURST && hit);
  assign wr_ready = (state == STATE_WRITE) && (state_next == STATE_IDLE);

  // ===========================================================================
  // Unused signals
  // ===========================================================================
  `SVC_UNUSED({m_axi_arready, m_axi_rid, m_axi_rresp, m_axi_bid, m_axi_bresp,
               m_axi_bvalid, rd_addr[1:0], wr_addr[1:0]});

  if (AXI_ADDR_WIDTH < 32) begin : gen_unused_wr_addr_hi
    `SVC_UNUSED(wr_addr[31:AXI_ADDR_WIDTH]);
  end

  if (TWO_WAY == 0) begin : gen_unused_direct
    `SVC_UNUSED({way0_tag, way1_tag, way0_valid, way1_valid, lru_table});
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
  // Covers
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      `FCOVER(c_read_burst_start, $past(state
              ) == STATE_IDLE && state == STATE_READ_BURST);
      `FCOVER(c_fill_done, fill_done);
      `FCOVER(c_hit_after_fill, $past(fill_done) && rd_valid && hit);
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
      .F_AXI_MAXSTALL  (3),
      .F_AXI_MAXRSTALL (3),
      .F_AXI_MAXDELAY  (3)
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

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER

`endif
`endif

endmodule

`endif
