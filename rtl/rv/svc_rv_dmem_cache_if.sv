`ifndef SVC_RV_DMEM_CACHE_IF_SV
`define SVC_RV_DMEM_CACHE_IF_SV

`include "svc.sv"

//
// RISC-V Data Memory to Cache Interface Bridge
//
// Converts CPU dmem pulse-based signals to cache valid/ready protocol.
// Handles address/data registration since CPU may change values while
// cache handles a miss.
//
// I/O bypass: Addresses with bit 31 = 1 bypass the cache and connect
// directly to I/O. I/O has fixed 1-cycle BRAM timing.
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

    // max_fanout to reduce routing delay on timing-critical signal
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
  logic cache_rd_valid_next;

  //
  // State machine
  //
  typedef enum logic [2:0] {
    STATE_IDLE,
    STATE_READING,
    STATE_READ_STALLED,
    STATE_READ_COMPLETE,
    STATE_WRITE,
    STATE_WRITE_COMPLETE
  } state_t;

  state_t state;
  state_t state_next;

  //
  // Address decode: bit 31 = 1 selects I/O
  //
  logic   io_sel_rd;
  logic   io_sel_wr;

  assign io_sel_rd = dmem_raddr[31];
  assign io_sel_wr = dmem_waddr[31];

  //
  // I/O select tracking for read response mux
  //
  logic io_sel_rd_p1;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      io_sel_rd_p1 <= 1'b0;
    end else if (state == STATE_IDLE && dmem_ren) begin
      io_sel_rd_p1 <= io_sel_rd;
    end
  end

  //
  // Registered address for cache reads
  //
  // CPU may change address while we're handling a cache miss,
  // so we register the address when the read starts.
  //
  logic [31:0] rd_addr_reg;

  //
  // Registered read data for CPU
  //
  // The pipelined CPU may hold a load in WB while we start processing the next
  // read. If we change dmem_rdata when the new read completes, the old load
  // in WB would pick up the wrong value. So we capture the data when the read
  // completes and hold it until the pipeline has advanced (stall=0).
  //
  logic [31:0] rd_data_reg;
  logic        rd_data_valid;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rd_data_reg   <= 32'h0;
      rd_data_valid <= 1'b0;
    end else begin
      // Clear rd_data_valid when pipeline can advance (stall is low)
      if (rd_data_valid && !dmem_stall) begin
        rd_data_valid <= 1'b0;
      end
      // Capture new data when read completes (overrides clear)
      if ((state == STATE_READING || state == STATE_READ_STALLED) &&
          cache_rd_data_valid) begin
        rd_data_reg   <= cache_rd_data;
        rd_data_valid <= 1'b1;
      end
    end
  end

  //
  // Registered write data for cache
  //
  logic [31:0] wr_addr_reg;
  logic [31:0] wr_data_reg;
  logic [ 3:0] wr_strb_reg;

  //
  // Starting flags for immediate stall when initiating operations
  //
  logic        rd_starting_miss;
  logic        wr_starting;

  //
  // State machine next-state logic
  //
  always_comb begin
    state_next          = state;
    cache_rd_valid_next = cache_rd_valid && !cache_rd_ready;

    case (state)
      STATE_IDLE: begin
        if (!cache_rd_valid || cache_rd_ready) begin
          if (dmem_ren && !io_sel_rd) begin
            cache_rd_valid_next = 1'b1;
            // On hit, stay in IDLE.
            if (!cache_rd_hit) begin
              state_next = STATE_READING;
            end
          end else if (dmem_we && !io_sel_wr) begin
            state_next = STATE_WRITE;
          end
        end
      end

      STATE_READING: begin
        if (cache_rd_data_valid) begin
          state_next = STATE_READ_COMPLETE;
        end else begin
          state_next = STATE_READ_STALLED;
        end
      end

      STATE_READ_STALLED: begin
        if (cache_rd_data_valid) begin
          state_next = STATE_READ_COMPLETE;
        end
      end

      STATE_READ_COMPLETE: begin
        state_next = STATE_IDLE;
      end

      STATE_WRITE: begin
        if (cache_wr_ready) begin
          state_next = STATE_WRITE_COMPLETE;
        end
      end

      STATE_WRITE_COMPLETE: begin
        state_next = STATE_IDLE;
      end

      default: begin
        state_next = STATE_IDLE;
      end
    endcase
  end

  //
  // State registration
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state          <= STATE_IDLE;
      cache_rd_valid <= 1'b0;
    end else begin
      state          <= state_next;
      cache_rd_valid <= cache_rd_valid_next;
    end
  end

  //
  // Register read address when starting any cache read (hit or miss)
  //
  logic capture_rd_addr;
  assign capture_rd_addr = ((state == STATE_IDLE) && dmem_ren && !io_sel_rd &&
                            (!cache_rd_valid || cache_rd_ready));

  always_ff @(posedge clk) begin
    if (capture_rd_addr) begin
      rd_addr_reg <= dmem_raddr;
    end
  end

  //
  // Register write data on state transition to WRITE
  //
  // Capture data when transitioning from IDLE to WRITE.
  //
  always_ff @(posedge clk) begin
    if (state_next == STATE_WRITE && state == STATE_IDLE) begin
      wr_addr_reg <= dmem_waddr;
      wr_data_reg <= dmem_wdata;
      wr_strb_reg <= dmem_wstrb;
    end
  end

  //
  // Cache read interface
  //
  // Use rd_addr_reg only during active transaction (valid && !ready).
  // Use dmem_raddr otherwise to enable hit detection for new requests.
  assign cache_rd_addr = ((cache_rd_valid && !cache_rd_ready) ? rd_addr_reg :
                          dmem_raddr);

  //
  // Cache write interface
  //
  // Valid only in WRITE state. Unlike reads, we don't drop valid when ready
  // arrives - the handshake requires valid && ready at clock edge.
  //
  assign cache_wr_valid = (state == STATE_WRITE);
  assign cache_wr_addr = wr_addr_reg;
  assign cache_wr_data = wr_data_reg;
  assign cache_wr_strb = wr_strb_reg;

  //
  // I/O read interface
  //
  assign io_ren = dmem_ren && io_sel_rd;
  assign io_raddr = dmem_raddr;

  //
  // I/O write interface
  //
  assign io_wen = dmem_we && io_sel_wr;
  assign io_waddr = dmem_waddr;
  assign io_wdata = dmem_wdata;
  assign io_wstrb = dmem_wstrb;

  //
  // Read data mux
  //
  // Select between I/O (BRAM timing) and cache data.
  // Use registered cache data when valid to hold value through pipeline stalls.
  //
  always_comb begin
    if (io_sel_rd_p1) begin
      dmem_rdata = io_rdata;
    end else if (rd_data_valid) begin
      dmem_rdata = rd_data_reg;
    end else begin
      dmem_rdata = cache_rd_data;
    end
  end

  //
  // Stall generation
  //
  // Only stall on MISS, not all reads
  assign rd_starting_miss = ((state == STATE_IDLE) && dmem_ren && !io_sel_rd &&
                             !cache_rd_hit);
  assign wr_starting = (state == STATE_IDLE) && dmem_we && !io_sel_wr;

  assign dmem_stall = rd_starting_miss || wr_starting ||
      (state == STATE_READING && !cache_rd_data_valid) ||
      (state == STATE_READ_STALLED && !cache_rd_data_valid) ||
      (state == STATE_READ_COMPLETE) || (state == STATE_WRITE && !cache_wr_ready
      ) || (state == STATE_WRITE_COMPLETE);


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

  always_ff @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  // States that will return to IDLE next cycle
  logic completing;
  assign completing = (state == STATE_READ_COMPLETE) ||
      (state == STATE_WRITE_COMPLETE);

  initial begin
    assume (!rst_n);
  end

  //
  // Input assumptions
  //
  always_ff @(posedge clk) begin
    `FASSUME(a_no_simul_rd_wr, !(dmem_ren && dmem_we));
    `FASSUME(a_cache_mutex, !(cache_rd_data_valid && cache_wr_ready));

    // cache_rd_hit implies cache_rd_data_valid next cycle
    if (f_past_valid && $past(rst_n) && rst_n && $past(cache_rd_hit)) begin
      `FASSUME(a_hit_implies_data_valid, cache_rd_data_valid);
    end
  end

  //
  // Assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      `FASSERT(a_cache_wr_valid, cache_wr_valid == (state == STATE_WRITE));

      // I/O interface is combinational passthrough
      `FASSERT(a_io_ren, io_ren == (dmem_ren && io_sel_rd));
      `FASSERT(a_io_wen, io_wen == (dmem_we && io_sel_wr));
      `FASSERT(a_io_raddr, io_raddr == dmem_raddr);
      `FASSERT(a_io_waddr, io_waddr == dmem_waddr);
      `FASSERT(a_io_wdata, io_wdata == dmem_wdata);
      `FASSERT(a_io_wstrb, io_wstrb == dmem_wstrb);
    end

    if (f_past_valid && !$past(rst_n)) begin
      `FASSERT(a_reset_to_idle, state == STATE_IDLE);
    end

    if (f_past_valid && $past(rst_n) && rst_n) begin
      // I/O bypass: I/O requests don't change state from IDLE
      if ($past(
              dmem_ren && io_sel_rd && state == STATE_IDLE && !completing
          )) begin
        `FASSERT(a_io_rd_stays_idle, state == STATE_IDLE);
      end
      if ($past(
              dmem_we && io_sel_wr && state == STATE_IDLE && !completing
          )) begin
        `FASSERT(a_io_wr_stays_idle, state == STATE_IDLE);
      end

      // Cache hit: stays in IDLE (speculative path)
      if ($past(
              dmem_ren && !io_sel_rd && cache_rd_hit && state == STATE_IDLE &&
                  !completing && !cache_rd_valid
          )) begin
        `FASSERT(a_cache_hit_stays_idle, state == STATE_IDLE);
      end

      // Cache hit: no stall
      if ($past(cache_rd_hit && state == STATE_IDLE)) begin
        `FASSERT(a_cache_hit_no_stall, !$past(dmem_stall) || $past(wr_starting
                 ));
      end

      // Valid/ready protocol for reads: valid and addr stable until ready
      if ($past(cache_rd_valid && !cache_rd_ready)) begin
        `FASSERT(a_rd_valid_stable, cache_rd_valid);
        `FASSERT(a_rd_addr_until_ready, cache_rd_addr == $past(cache_rd_addr));
      end

      // Valid/ready protocol for writes: valid and data stable until ready
      if ($past(cache_wr_valid && !cache_wr_ready)) begin
        `FASSERT(a_wr_valid_stable, cache_wr_valid);
        `FASSERT(a_wr_addr_until_ready, cache_wr_addr == $past(cache_wr_addr));
        `FASSERT(a_wr_data_until_ready, cache_wr_data == $past(cache_wr_data));
        `FASSERT(a_wr_strb_until_ready, cache_wr_strb == $past(cache_wr_strb));
      end

      // Address/data stability during write state
      if ($past(state == STATE_WRITE) && (state == STATE_WRITE)) begin
        `FASSERT(a_wr_addr_stable, cache_wr_addr == $past(cache_wr_addr));
        `FASSERT(a_wr_data_stable, cache_wr_data == $past(cache_wr_data));
        `FASSERT(a_wr_strb_stable, cache_wr_strb == $past(cache_wr_strb));
      end
    end
  end

  //
  // Cover properties - read state machine paths
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Read hit path: IDLE → READING → WB → IDLE
      `FCOVER(c_idle_to_reading, $past(state == STATE_IDLE
              ) && state == STATE_READING);
      `FCOVER(c_reading_to_wb, $past(state == STATE_READING
              ) && state == STATE_READ_COMPLETE);
      `FCOVER(c_wb_to_idle, $past(state == STATE_READ_COMPLETE
              ) && state == STATE_IDLE);

      // Read miss path: READING → STALLED → WB → IDLE
      `FCOVER(c_reading_to_stalled, $past(state == STATE_READING
              ) && state == STATE_READ_STALLED);
      `FCOVER(c_stalled_to_wb, $past(state == STATE_READ_STALLED
              ) && state == STATE_READ_COMPLETE);

      // Write path: IDLE → WRITE → WRITE_COMPLETE → IDLE
      `FCOVER(c_idle_to_write, $past(state == STATE_IDLE
              ) && state == STATE_WRITE);
      `FCOVER(c_write_to_complete, $past(state == STATE_WRITE
              ) && state == STATE_WRITE_COMPLETE);
      `FCOVER(c_write_complete_to_idle, $past(state == STATE_WRITE_COMPLETE
              ) && state == STATE_IDLE);

      // Multi-cycle miss
      `FCOVER(c_multi_cycle_stall, $past(state == STATE_READ_STALLED
              ) && state == STATE_READ_STALLED);

      // I/O bypass
      `FCOVER(c_io_read, $past(io_ren));
      `FCOVER(c_io_write, $past(io_wen));

      // Stall scenarios
      `FCOVER(c_stall_on_rd_start, dmem_stall && rd_starting_miss);
      `FCOVER(c_stall_on_wr_start, dmem_stall && wr_starting);
      `FCOVER(c_stall_in_stalled, dmem_stall && state == STATE_READ_STALLED);
      `FCOVER(c_no_stall_idle, !dmem_stall && state == STATE_IDLE);

      // Zero-stall cache hit path
      `FCOVER(c_cache_hit_no_stall, $past(
              dmem_ren && !io_sel_rd && cache_rd_hit && state == STATE_IDLE
              ) && state == STATE_IDLE && !dmem_stall);
      `FCOVER(c_back_to_back_hits, $past(cache_rd_hit) && cache_rd_hit);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
