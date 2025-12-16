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
  // Address decode: bit 31 = 1 selects I/O
  //
  logic io_sel_rd;
  logic io_sel_wr;

  assign io_sel_rd = dmem_raddr[31];
  assign io_sel_wr = dmem_waddr[31];

  //
  // I/O select tracking for read response mux
  //
  logic io_sel_rd_p1;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      io_sel_rd_p1 <= 1'b0;
    end else if (dmem_ren) begin
      io_sel_rd_p1 <= io_sel_rd;
    end
  end

  //
  // Read pending state
  //
  // Set when we start a cache read, clear when data is valid.
  // This tracks whether we're waiting for cache read data.
  //
  logic        rd_pending;
  logic        rd_pending_next;

  //
  // Registered address for cache reads
  //
  // CPU may change address while we're handling a cache miss,
  // so we register the address when the read starts.
  //
  logic [31:0] rd_addr_reg;

  //
  // Write pending state
  //
  // Set when we start a cache write, clear when cache accepts it.
  //
  logic        wr_pending;
  logic        wr_pending_next;

  //
  // Registered write data for cache
  //
  logic [31:0] wr_addr_reg;
  logic [31:0] wr_data_reg;
  logic [ 3:0] wr_strb_reg;

  //
  // Read pending logic
  //
  // Start pending on cache read request (not I/O), clear on data valid.
  //
  always_comb begin
    rd_pending_next = rd_pending;

    if (dmem_ren && !io_sel_rd && !rd_pending) begin
      rd_pending_next = 1'b1;
    end else if (cache_rd_data_valid) begin
      rd_pending_next = 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rd_pending <= 1'b0;
    end else begin
      rd_pending <= rd_pending_next;
    end
  end

  //
  // Register read address on new request
  //
  always_ff @(posedge clk) begin
    if (dmem_ren && !io_sel_rd && !rd_pending) begin
      rd_addr_reg <= dmem_raddr;
    end
  end

  //
  // Write pending logic
  //
  // Start pending on cache write request (not I/O), clear on cache ready.
  //
  always_comb begin
    wr_pending_next = wr_pending;

    if (dmem_we && !io_sel_wr && !wr_pending) begin
      wr_pending_next = 1'b1;
    end else if (cache_wr_ready) begin
      wr_pending_next = 1'b0;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      wr_pending <= 1'b0;
    end else begin
      wr_pending <= wr_pending_next;
    end
  end

  //
  // Register write data on new request
  //
  always_ff @(posedge clk) begin
    if (dmem_we && !io_sel_wr && !wr_pending) begin
      wr_addr_reg <= dmem_waddr;
      wr_data_reg <= dmem_wdata;
      wr_strb_reg <= dmem_wstrb;
    end
  end

  //
  // Cache read interface
  //
  // Valid when pending (held until ready)
  //
  assign cache_rd_valid = rd_pending;
  assign cache_rd_addr = rd_addr_reg;

  //
  // Cache write interface
  //
  // Valid when pending (held until ready)
  //
  assign cache_wr_valid = wr_pending;
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
  // Select between I/O (BRAM timing) and cache data
  //
  assign dmem_rdata = io_sel_rd_p1 ? io_rdata : cache_rd_data;

  //
  // Stall generation
  //
  // Stall CPU when:
  // 1. Read pending and data not yet valid (cache miss in progress)
  // 2. Write pending and cache not ready (write in progress)
  //
  assign dmem_stall = ((rd_pending && !cache_rd_data_valid) ||
                       (wr_pending && !cache_wr_ready));

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

    // CPU does not issue read while write pending, or vice versa
    //
    // This prevents both rd_pending and wr_pending from being set
    // simultaneously, which would violate the mutual exclusion invariant.
    //
    `FASSUME(a_no_rd_while_wr_pending, !wr_pending || !dmem_ren);
    `FASSUME(a_no_wr_while_rd_pending, !rd_pending || !dmem_we);

    // Cache does not assert both rd_data_valid and wr_ready simultaneously
    `FASSUME(a_cache_mutex, !(cache_rd_data_valid && cache_wr_ready));

    // Cache only asserts rd_data_valid when we have a pending read
    `FASSUME(a_rd_data_valid_requires_pending,
             !cache_rd_data_valid || rd_pending);

    // Cache only asserts wr_ready when we have a pending write
    `FASSUME(a_wr_ready_requires_pending, !cache_wr_ready || wr_pending);
  end

  //
  // Assertions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && rst_n) begin
      //
      // Stall logic correctness
      //
      `FASSERT(a_stall_on_rd_pending,
               !(rd_pending && !cache_rd_data_valid) || dmem_stall);
      `FASSERT(a_stall_on_wr_pending,
               !(wr_pending && !cache_wr_ready) || dmem_stall);
      `FASSERT(a_no_stall_when_idle,
               !(!rd_pending && !wr_pending) || !dmem_stall);

      //
      // Mutual exclusion: rd_pending and wr_pending never both active
      //
      `FASSERT(a_pending_mutex, !(rd_pending && wr_pending));

      //
      // Cache valid tracks pending state
      //
      `FASSERT(a_cache_rd_valid_eq_pending, cache_rd_valid == rd_pending);
      `FASSERT(a_cache_wr_valid_eq_pending, cache_wr_valid == wr_pending);

      //
      // I/O interface is passthrough
      //
      `FASSERT(a_io_ren_comb, io_ren == (dmem_ren && io_sel_rd));
      `FASSERT(a_io_wen_comb, io_wen == (dmem_we && io_sel_wr));
      `FASSERT(a_io_raddr_comb, io_raddr == dmem_raddr);
      `FASSERT(a_io_waddr_comb, io_waddr == dmem_waddr);
      `FASSERT(a_io_wdata_comb, io_wdata == dmem_wdata);
      `FASSERT(a_io_wstrb_comb, io_wstrb == dmem_wstrb);
    end

    //
    // Reset clears pending states
    //
    if (f_past_valid && !$past(rst_n)) begin
      `FASSERT(a_reset_clears_rd_pending, !rd_pending);
      `FASSERT(a_reset_clears_wr_pending, !wr_pending);
    end

    //
    // I/O bypass: I/O requests don't set pending
    //
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(dmem_ren && io_sel_rd && !rd_pending)) begin
        `FASSERT(a_io_rd_no_pending, !rd_pending || $past(rd_pending));
      end
      if ($past(dmem_we && io_sel_wr && !wr_pending)) begin
        `FASSERT(a_io_wr_no_pending, !wr_pending || $past(wr_pending));
      end
    end

    //
    // Address stability: registered address stable while pending
    //
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(rd_pending) && rd_pending) begin
        `FASSERT(a_rd_addr_stable, cache_rd_addr == $past(cache_rd_addr));
      end
      if ($past(wr_pending) && wr_pending) begin
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
      // Read scenarios
      `FCOVER(c_cache_read_start, $past(!rd_pending) && rd_pending);
      `FCOVER(c_cache_read_complete, $past(rd_pending) && !rd_pending && $past(
              cache_rd_data_valid));
      `FCOVER(c_cache_read_multi_cycle, $past(rd_pending, 2) && $past(rd_pending
              ) && !rd_pending);

      // Write scenarios
      `FCOVER(c_cache_write_start, $past(!wr_pending) && wr_pending);
      `FCOVER(c_cache_write_complete, $past(wr_pending) && !wr_pending && $past(
              cache_wr_ready));

      // I/O bypass scenarios
      `FCOVER(c_io_read, $past(io_ren));
      `FCOVER(c_io_write, $past(io_wen));

      // Stall scenarios
      `FCOVER(c_stall_rd, dmem_stall && rd_pending);
      `FCOVER(c_stall_wr, dmem_stall && wr_pending);
      `FCOVER(c_no_stall, !dmem_stall && !rd_pending && !wr_pending);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
