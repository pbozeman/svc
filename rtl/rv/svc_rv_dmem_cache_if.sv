`ifndef SVC_RV_DMEM_CACHE_IF_SV
`define SVC_RV_DMEM_CACHE_IF_SV

`include "svc.sv"
`include "svc_unused.sv"

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

    output logic dmem_stall,

    // Cache interface
    output logic        cache_rd_valid,
    input  logic        cache_rd_ready,
    output logic [31:0] cache_rd_addr,

    input logic [31:0] cache_rd_data,
    input logic        cache_rd_data_valid,

    output logic        cache_wr_valid,
    input  logic        cache_wr_ready,
    output logic [31:0] cache_wr_addr,
    output logic [31:0] cache_wr_data,
    output logic [ 3:0] cache_wr_strb,

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
  typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_READ,
    STATE_WRITE
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
  // Capture io_sel_rd when a read request is accepted (in IDLE, not during
  // cooldown). This works for both IO reads (immediate) and cache reads
  // (which transition to STATE_READ). We can't use dmem_stall because it
  // goes high immediately when a cache read starts, before we can capture.
  //
  logic io_sel_rd_p1;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      io_sel_rd_p1 <= 1'b0;
    end else if (state == STATE_IDLE && !completing && dmem_ren) begin
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
      if (state == STATE_READ && cache_rd_data_valid) begin
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
  // Cooldown after cache operation completes
  //
  // When a cache operation completes, we need to stay in IDLE for one cycle
  // before accepting a new request. This gives the pipelined CPU time to
  // complete its write-back stage before a new stall is asserted.
  //
  logic        completing;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      completing <= 1'b0;
    end else begin
      completing <= (state == STATE_READ && cache_rd_data_valid) ||
          (state == STATE_WRITE && cache_wr_ready);
    end
  end

  //
  // State machine next-state logic
  //
  always_comb begin
    state_next = state;

    case (state)
      STATE_IDLE: begin
        // Don't accept new cache requests during cooldown cycle after completing
        // a previous request. This gives the CPU time to advance.
        if (!completing) begin
          if (dmem_ren && !io_sel_rd) begin
            state_next = STATE_READ;
          end else if (dmem_we && !io_sel_wr) begin
            state_next = STATE_WRITE;
          end
        end
      end

      STATE_READ: begin
        if (cache_rd_data_valid) begin
          // Always go to IDLE when read completes. The CPU needs stall to
          // drop so it can advance and capture the data. Back-to-back
          // transitions don't work because the CPU holds dmem_ren high
          // while stalled, making it impossible to distinguish "holding
          // current request" from "issuing new request".
          state_next = STATE_IDLE;
        end
      end

      STATE_WRITE: begin
        if (cache_wr_ready) begin
          // Always go to IDLE when write completes.
          state_next = STATE_IDLE;
        end
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
      state <= STATE_IDLE;
    end else begin
      state <= state_next;
    end
  end

  //
  // Register read address on state transition to READ
  //
  // Capture address when transitioning from IDLE to READ.
  //
  always_ff @(posedge clk) begin
    if (state_next == STATE_READ && state == STATE_IDLE) begin
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
  // Valid only in READ state, and drop immediately when data arrives
  // to prevent spurious second handshake.
  //
  assign cache_rd_valid = (state == STATE_READ) && !cache_rd_data_valid;
  assign cache_rd_addr = rd_addr_reg;

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
  assign dmem_rdata = io_sel_rd_p1 ?
      io_rdata : (rd_data_valid ? rd_data_reg : cache_rd_data);

  //
  // Stall generation
  //
  // Stall CPU when a cache operation is pending. Use state_next so stall
  // goes high immediately when a request is issued, preventing the CPU from
  // advancing before the response arrives.
  //
  // Also stall during cooldown cycle to prevent CPU from advancing again
  // before the new cache request can be accepted.
  //
  assign dmem_stall = (state_next != STATE_IDLE) || completing;

  `SVC_UNUSED(cache_rd_ready);

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

  // Reset is low initially
  initial begin
    assume (!rst_n);
  end

  //
  // Input assumptions
  //
  always_ff @(posedge clk) begin
    // CPU does not issue simultaneous read and write
    `FASSUME(a_no_simul_rd_wr, !(dmem_ren && dmem_we));

    // Cache does not assert both rd_data_valid and wr_ready simultaneously
    `FASSUME(a_cache_mutex, !(cache_rd_data_valid && cache_wr_ready));
  end

  //
  // Assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      // Stall logic correctness: stall when not idle or completing
      `FASSERT(a_stall_eq_not_idle,
               dmem_stall == ((state_next != STATE_IDLE) || completing));

      // Cache valid tracks state
      `FASSERT(
          a_cache_rd_valid_eq_read,
          cache_rd_valid == ((state == STATE_READ) && !cache_rd_data_valid));
      `FASSERT(a_cache_wr_valid_eq_write,
               cache_wr_valid == (state == STATE_WRITE));

      // I/O interface is passthrough
      `FASSERT(a_io_ren_comb, io_ren == (dmem_ren && io_sel_rd));
      `FASSERT(a_io_wen_comb, io_wen == (dmem_we && io_sel_wr));
      `FASSERT(a_io_raddr_comb, io_raddr == dmem_raddr);
      `FASSERT(a_io_waddr_comb, io_waddr == dmem_waddr);
      `FASSERT(a_io_wdata_comb, io_wdata == dmem_wdata);
      `FASSERT(a_io_wstrb_comb, io_wstrb == dmem_wstrb);
    end

    //
    // Reset clears state to IDLE
    //
    if (f_past_valid && !$past(rst_n)) begin
      `FASSERT(a_reset_to_idle, state == STATE_IDLE);
    end

    //
    // I/O bypass: I/O requests don't change state from IDLE
    //
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(dmem_ren && io_sel_rd && state == STATE_IDLE)) begin
        `FASSERT(a_io_rd_stays_idle, state == STATE_IDLE);
      end
      if ($past(dmem_we && io_sel_wr && state == STATE_IDLE)) begin
        `FASSERT(a_io_wr_stays_idle, state == STATE_IDLE);
      end
    end

    //
    // Address stability: registered address stable while in READ/WRITE state
    //
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(state == STATE_READ) && (state == STATE_READ)) begin
        `FASSERT(a_rd_addr_stable, cache_rd_addr == $past(cache_rd_addr));
        `FASSERT(a_io_sel_stable_during_read, io_sel_rd_p1 == $past(io_sel_rd_p1
                 ));
      end
      if ($past(state == STATE_WRITE) && (state == STATE_WRITE)) begin
        `FASSERT(a_wr_addr_stable, cache_wr_addr == $past(cache_wr_addr));
        `FASSERT(a_wr_data_stable, cache_wr_data == $past(cache_wr_data));
        `FASSERT(a_wr_strb_stable, cache_wr_strb == $past(cache_wr_strb));
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // State transitions
      `FCOVER(c_idle_to_read, $past(state == STATE_IDLE
              ) && (state == STATE_READ));
      `FCOVER(c_read_to_idle, $past(state == STATE_READ
              ) && (state == STATE_IDLE));
      `FCOVER(c_idle_to_write, $past(state == STATE_IDLE
              ) && (state == STATE_WRITE));
      `FCOVER(c_write_to_idle, $past(state == STATE_WRITE
              ) && (state == STATE_IDLE));

      // Multi-cycle operations
      `FCOVER(c_multi_cycle_read, $past(state == STATE_READ, 2) && $past(
              state == STATE_READ) && (state == STATE_IDLE));
      `FCOVER(c_multi_cycle_write, $past(state == STATE_WRITE, 2) && $past(
              state == STATE_WRITE) && (state == STATE_IDLE));

      // I/O bypass scenarios
      `FCOVER(c_io_read, $past(io_ren));
      `FCOVER(c_io_write, $past(io_wen));

      // Stall scenarios
      `FCOVER(c_stall_read, dmem_stall && (state == STATE_READ));
      `FCOVER(c_stall_write, dmem_stall && (state == STATE_WRITE));
      `FCOVER(c_no_stall, !dmem_stall && (state == STATE_IDLE));
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
