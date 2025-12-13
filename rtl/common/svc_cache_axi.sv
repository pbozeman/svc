`ifndef SVC_CACHE_AXI_SV
`define SVC_CACHE_AXI_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// AXI-backed cache with simple BRAM-like CPU interface
//
// Cache organization:
// - Direct-mapped (1-way) or 2-way set associative
// - LRU replacement for 2-way
// - Write-through policy
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
    // Cache interface
    //
    input logic ren,
    input logic wen,

    // verilator lint_off UNUSEDSIGNAL
    // addr[1:0] is byte offset within 32-bit word, not used for word-aligned access
    input logic [31:0] addr,
    // verilator lint_on UNUSEDSIGNAL

    output logic [31:0] rd_data,
    output logic        rd_valid,

    input logic [31:0] wr_data,
    input logic [ 3:0] wr_strb,

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

  // AXI cache params
  localparam logic [AXI_ID_WIDTH-1:0] AXI_ID = 0;
  localparam int AXI_DATA_BYTES = AXI_DATA_WIDTH / 8;
  localparam int AXI_ARLEN = CACHE_LINE_BYTES / AXI_DATA_BYTES - 1;
  localparam int AXI_ARSIZE = $clog2(AXI_DATA_BYTES);
  localparam int WORDS_PER_BEAT = AXI_DATA_WIDTH / 32;

  // Addr fields
  logic [   TAG_WIDTH-1:0] addr_tag;
  logic [   SET_WIDTH-1:0] addr_set;
  logic [OFFSET_WIDTH-3:0] addr_offset;

  // Cache storage
  // verilator lint_off UNUSEDSIGNAL
  // verilator lint_off UNDRIVEN
  logic [   TAG_WIDTH-1:0] tag_table   [NUM_SETS][NUM_WAYS];
  logic                    valid_table [NUM_SETS][NUM_WAYS];

  (* ram_style = "block" *)
  logic [            31:0] data_table  [NUM_SETS][NUM_WAYS] [WORDS_PER_LINE];
  // verilator lint_on UNDRIVEN
  // verilator lint_on UNUSEDSIGNAL


  assign addr_tag    = addr[31:32-TAG_WIDTH];
  assign addr_set    = addr[OFFSET_WIDTH+SET_WIDTH-1:OFFSET_WIDTH];
  assign addr_offset = addr[OFFSET_WIDTH-1:2];

  // LRU tracking for 2-way (1 bit per set: 0 = way0 is LRU, 1 = way1 is LRU)
  // verilator lint_off UNUSEDSIGNAL
  logic                 lru_table  [NUM_SETS];
  // verilator lint_on UNUSEDSIGNAL

  // ===========================================================================
  // Cache lookup
  // ===========================================================================
  logic                 hit;
  logic                 way0_hit;
  logic                 way1_hit;
  logic [         31:0] hit_data;

  //
  // Way 0 lookup
  //
  logic                 way0_valid;
  logic [TAG_WIDTH-1:0] way0_tag;
  logic [         31:0] way0_data;

  assign way0_valid = valid_table[addr_set][0];
  assign way0_tag   = tag_table[addr_set][0];
  assign way0_data  = data_table[addr_set][0][addr_offset];
  assign way0_hit   = way0_valid && (way0_tag == addr_tag);

  //
  // Way 1 lookup (only for 2-way)
  //
  logic                 way1_valid;
  logic [TAG_WIDTH-1:0] way1_tag;
  logic [         31:0] way1_data;

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

    `SVC_UNUSED({way0_tag, way1_tag, way0_valid, way1_valid});
  end

  assign hit      = way0_hit || way1_hit;
  assign hit_data = way1_hit ? way1_data : way0_data;

  // ===========================================================================
  // Reads
  // ===========================================================================
  typedef enum {
    STATE_IDLE,
    STATE_READ_BURST
  } state_t;

  state_t                      state;
  state_t                      state_next;

  logic                        rd_valid_next;
  logic                        m_axi_arvalid_next;
  logic   [AXI_ADDR_WIDTH-1:0] m_axi_araddr_next;
  logic   [AXI_ADDR_WIDTH-1:0] addr_line_aligned;

  assign addr_line_aligned = {
    addr[AXI_ADDR_WIDTH-1:OFFSET_WIDTH], {OFFSET_WIDTH{1'b0}}
  };

  logic [WORD_IDX_WIDTH-1:0] beat_word_idx;
  logic [WORD_IDX_WIDTH-1:0] beat_word_idx_next;

  logic [     SET_WIDTH-1:0] fill_set;
  logic [     SET_WIDTH-1:0] fill_set_next;
  logic [     TAG_WIDTH-1:0] fill_tag;
  logic [     TAG_WIDTH-1:0] fill_tag_next;
  logic                      fill_way;
  logic                      fill_way_next;
  logic [WORD_IDX_WIDTH-1:0] fill_offset;
  logic [WORD_IDX_WIDTH-1:0] fill_offset_next;
  logic                      fill_done;

  logic                      evict_way;

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

  always_comb begin
    state_next         = state;
    m_axi_arvalid_next = m_axi_arvalid & ~m_axi_arready;
    m_axi_araddr_next  = m_axi_araddr;

    beat_word_idx_next = beat_word_idx;
    fill_set_next      = fill_set;
    fill_tag_next      = fill_tag;
    fill_way_next      = fill_way;
    fill_offset_next   = fill_offset;
    fill_done          = 1'b0;

    case (state)
      STATE_IDLE: begin
        if (ren && !hit) begin
          state_next         = STATE_READ_BURST;
          m_axi_arvalid_next = 1'b1;

          // Align read to cache line and capture fill target
          m_axi_araddr_next  = addr_line_aligned;
          beat_word_idx_next = '0;
          fill_set_next      = addr_set;
          fill_tag_next      = addr_tag;
          fill_way_next      = evict_way;
          fill_offset_next   = WORD_IDX_WIDTH'(addr_offset);
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

      default: begin
      end
    endcase
  end

  //
  // Data table write on each AXI beat
  //
  // With 128-bit AXI, this writes 4 words (128 bits) per cycle. This exceeds
  // single BRAM write width (72 bits max on Xilinx), so synthesizer will
  // bank multiple BRAMs in parallel. Prioritizes fill latency over BRAM count.
  //
  always_ff @(posedge clk) begin
    if (state == STATE_READ_BURST && m_axi_rvalid) begin
      for (int i = 0; i < WORDS_PER_BEAT; i++) begin
        data_table[fill_set][fill_way][beat_word_idx+WORD_IDX_WIDTH'(i)] <=
            m_axi_rdata[i*32+:32];
      end
    end
  end

  //
  // Update valid on fill completion
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      for (int s = 0; s < NUM_SETS; s++) begin
        for (int w = 0; w < NUM_WAYS; w++) begin
          valid_table[s][w] <= 1'b0;
        end
      end
    end else if (fill_done) begin
      valid_table[fill_set][fill_way] <= 1'b1;
    end
  end

  //
  // Update tag on fill completion
  //
  always_ff @(posedge clk) begin
    if (fill_done) begin
      tag_table[fill_set][fill_way] <= fill_tag;
    end
  end

  //
  // Update LRU on hit or fill (2-way only)
  //
  // LRU bit indicates which way to evict next (least recently used).
  // On access, mark the OTHER way as LRU.
  //
  if (TWO_WAY) begin : gen_lru_update
    always_ff @(posedge clk) begin
      if (ren && hit) begin
        lru_table[addr_set] <= ~way1_hit;
      end else if (fill_done) begin
        lru_table[fill_set] <= ~fill_way;
      end
    end
  end

  //
  // State machine registration
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  //
  // Fill tracking registration
  //
  always_ff @(posedge clk) begin
    beat_word_idx <= beat_word_idx_next;
    fill_set      <= fill_set_next;
    fill_tag      <= fill_tag_next;
    fill_way      <= fill_way_next;
    fill_offset   <= fill_offset_next;
  end

  //
  // m_axi registration
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_axi_arvalid <= 1'b0;
    end else begin
      m_axi_arvalid <= m_axi_arvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    m_axi_araddr <= m_axi_araddr_next;
  end

  assign m_axi_arid    = AXI_ID;
  assign m_axi_arlen   = AXI_ARLEN[7:0];
  assign m_axi_arsize  = AXI_ARSIZE[2:0];
  assign m_axi_arburst = 2'b01;
  assign m_axi_rready  = 1'b1;

  //
  // Cache responses
  //
  logic [31:0] fill_data;
  assign fill_data     = data_table[fill_set][fill_way][fill_offset];

  assign rd_valid_next = (ren && hit) || fill_done;
  assign rd_data       = fill_done ? fill_data : hit_data;

  always_ff @(posedge clk) begin
    rd_valid <= rd_valid_next;
  end

  assign m_axi_awvalid = 1'b0;
  assign m_axi_awid    = '0;
  assign m_axi_awaddr  = '0;
  assign m_axi_awlen   = '0;
  assign m_axi_awsize  = '0;
  assign m_axi_awburst = '0;

  assign m_axi_wvalid  = 1'b0;
  assign m_axi_wdata   = '0;
  assign m_axi_wstrb   = '0;
  assign m_axi_wlast   = 1'b0;

  assign m_axi_bready  = 1'b0;

  // ===========================================================================
  // Unused signals
  // ===========================================================================
  `SVC_UNUSED(
      {wen, wr_data, wr_strb, m_axi_arready, m_axi_rid, m_axi_rresp,
       m_axi_awready, m_axi_wready, m_axi_bvalid, m_axi_bid, m_axi_bresp});

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

  always_ff @(posedge clk) begin
    `FASSUME(a_mutex_ren_wen, !(ren && wen));
  end

  //
  // Internal state assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      `FASSERT(a_araddr_aligned,
               !m_axi_arvalid || m_axi_araddr[OFFSET_WIDTH-1:0] == '0);
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
      `FCOVER(c_hit_after_fill, $past(fill_done) && ren && hit);
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
      .OPT_NARROW_BURST(1'b0),
      .F_LGDEPTH       (9),
      .F_AXI_MAXSTALL  (3),
      .F_AXI_MAXRSTALL (3),
      .F_AXI_MAXDELAY  (3)
  ) faxi_manager_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      // Write address - not used
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

      // Write data - not used
      .i_axi_wvalid(m_axi_wvalid),
      .i_axi_wready(m_axi_wready),
      .i_axi_wdata (m_axi_wdata),
      .i_axi_wstrb (m_axi_wstrb),
      .i_axi_wlast (m_axi_wlast),

      // Write response - not used
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
