`include "svc_unit.sv"

`include "svc_rv_dmem_cache_if.sv"

//
// Testbench for RISC-V dmem to cache interface bridge
//

module svc_rv_dmem_cache_if_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  //
  // CPU dmem interface
  //
  logic        dmem_ren;
  logic [31:0] dmem_raddr;
  logic [31:0] dmem_rdata;

  logic        dmem_we;
  logic [31:0] dmem_waddr;
  logic [31:0] dmem_wdata;
  logic [ 3:0] dmem_wstrb;

  logic        dmem_stall;

  //
  // Cache interface
  //
  logic        cache_rd_valid;
  logic        cache_rd_ready;
  logic [31:0] cache_rd_addr;

  logic [31:0] cache_rd_data;
  logic        cache_rd_data_valid;
  logic        cache_rd_hit;

  logic        cache_wr_valid;
  logic        cache_wr_ready;
  logic [31:0] cache_wr_addr;
  logic [31:0] cache_wr_data;
  logic [ 3:0] cache_wr_strb;

  //
  // I/O interface
  //
  logic        io_ren;
  logic [31:0] io_raddr;
  logic [31:0] io_rdata;

  logic        io_wen;
  logic [31:0] io_waddr;
  logic [31:0] io_wdata;
  logic [ 3:0] io_wstrb;

  svc_rv_dmem_cache_if uut (
      .clk  (clk),
      .rst_n(rst_n),

      .dmem_ren  (dmem_ren),
      .dmem_raddr(dmem_raddr),
      .dmem_rdata(dmem_rdata),

      .dmem_we   (dmem_we),
      .dmem_waddr(dmem_waddr),
      .dmem_wdata(dmem_wdata),
      .dmem_wstrb(dmem_wstrb),

      .dmem_stall(dmem_stall),

      .cache_rd_valid     (cache_rd_valid),
      .cache_rd_ready     (cache_rd_ready),
      .cache_rd_addr      (cache_rd_addr),
      .cache_rd_data      (cache_rd_data),
      .cache_rd_data_valid(cache_rd_data_valid),
      .cache_rd_hit       (cache_rd_hit),

      .cache_wr_valid(cache_wr_valid),
      .cache_wr_ready(cache_wr_ready),
      .cache_wr_addr (cache_wr_addr),
      .cache_wr_data (cache_wr_data),
      .cache_wr_strb (cache_wr_strb),

      .io_ren  (io_ren),
      .io_raddr(io_raddr),
      .io_rdata(io_rdata),

      .io_wen  (io_wen),
      .io_waddr(io_waddr),
      .io_wdata(io_wdata),
      .io_wstrb(io_wstrb)
  );

  //
  // Initialize test inputs
  //
  initial begin
    dmem_ren            = 1'b0;
    dmem_raddr          = 32'h0;
    dmem_we             = 1'b0;
    dmem_waddr          = 32'h0;
    dmem_wdata          = 32'h0;
    dmem_wstrb          = 4'h0;

    cache_rd_ready      = 1'b1;
    cache_rd_data       = 32'h0;
    cache_rd_data_valid = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_wr_ready      = 1'b0;

    io_rdata            = 32'h0;
  end

  //
  // Test: Reset state
  //
  task automatic test_reset;
    `CHECK_FALSE(dmem_stall);
    `CHECK_FALSE(cache_rd_valid);
    `CHECK_FALSE(cache_wr_valid);
    `CHECK_FALSE(io_ren);
    `CHECK_FALSE(io_wen);
  endtask

  //
  // Test: Cache read with immediate hit (data valid next cycle)
  //
  task automatic test_cache_read_hit;
    dmem_ren   = 1'b1;
    dmem_raddr = 32'h0000_1000;
    `TICK(clk);

    //
    // Read request captured, pending starts
    //
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_1000);
    `CHECK_TRUE(dmem_stall);

    //
    // CPU may change address while pending
    //
    dmem_ren            = 1'b0;
    dmem_raddr          = 32'hDEAD_BEEF;

    //
    // Simulate cache hit - data valid next cycle
    //
    cache_rd_data       = 32'hCAFE_BABE;
    cache_rd_data_valid = 1'b1;
    `TICK(clk);

    //
    // Data available, but stall held for cooldown cycle
    //
    `CHECK_TRUE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'hCAFE_BABE);

    cache_rd_data_valid = 1'b0;
    `TICK(clk);

    //
    // Cooldown complete, stall released
    //
    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: Cache read miss (stalls for multiple cycles)
  //
  task automatic test_cache_read_miss;
    // Cache not ready initially (busy)
    cache_rd_ready = 1'b0;

    dmem_ren       = 1'b1;
    dmem_raddr     = 32'h0000_2000;
    `TICK(clk);

    dmem_ren = 1'b0;

    //
    // Stalls while waiting for handshake
    //
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_TRUE(dmem_stall);

    //
    // Simulate multiple cycles waiting for ready (cache busy)
    //
    repeat (3) begin
      `TICK(clk);
      `CHECK_TRUE(dmem_stall);
      `CHECK_TRUE(cache_rd_valid);
    end

    //
    // Cache accepts request (handshake completes)
    //
    cache_rd_ready = 1'b1;
    `TICK(clk);

    //
    // Valid drops after handshake, but stall continues waiting for data
    //
    `CHECK_FALSE(cache_rd_valid);
    `CHECK_TRUE(dmem_stall);

    //
    // More cycles waiting for data
    //
    repeat (2) begin
      `TICK(clk);
      `CHECK_TRUE(dmem_stall);
    end

    //
    // Finally data arrives
    //
    cache_rd_data       = 32'hDEAD_BEEF;
    cache_rd_data_valid = 1'b1;
    `TICK(clk);

    //
    // Data available, but stall held for cooldown cycle
    //
    `CHECK_TRUE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'hDEAD_BEEF);

    cache_rd_data_valid = 1'b0;
    cache_rd_ready      = 1'b1;
    `TICK(clk);

    //
    // Cooldown complete, stall released
    //
    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: Cache write
  //
  task automatic test_cache_write;
    dmem_we    = 1'b1;
    dmem_waddr = 32'h0000_3000;
    dmem_wdata = 32'h1234_5678;
    dmem_wstrb = 4'hF;
    `TICK(clk);

    dmem_we = 1'b0;

    //
    // Write pending, stalls until cache ready
    //
    `CHECK_TRUE(cache_wr_valid);
    `CHECK_EQ(cache_wr_addr, 32'h0000_3000);
    `CHECK_EQ(cache_wr_data, 32'h1234_5678);
    `CHECK_EQ(cache_wr_strb, 4'hF);
    `CHECK_TRUE(dmem_stall);

    //
    // Simulate cache busy for multiple cycles - valid must stay high (AXI protocol)
    //
    repeat (3) begin
      `TICK(clk);
      `CHECK_TRUE(dmem_stall);
      `CHECK_TRUE(cache_wr_valid);
    end

    //
    // Cache accepts write (handshake completes)
    //
    cache_wr_ready = 1'b1;
    `TICK(clk);

    //
    // Write complete, stall held for cooldown cycle (STATE_WRITE_COMPLETE)
    //
    `CHECK_TRUE(dmem_stall);
    `CHECK_FALSE(cache_wr_valid);

    cache_wr_ready = 1'b0;
    `TICK(clk);

    //
    // Cooldown complete, stall released
    //
    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: I/O read bypass (bit 31 = 1)
  //
  task automatic test_io_read_bypass;
    dmem_ren   = 1'b1;
    dmem_raddr = 32'h8000_0100;
    io_rdata   = 32'h1010_DA7A;

    //
    // Should not go to cache
    //
    `CHECK_TRUE(io_ren);
    `CHECK_EQ(io_raddr, 32'h8000_0100);
    `CHECK_FALSE(cache_rd_valid);

    `TICK(clk);

    //
    // I/O has 1-cycle latency, no stall
    //
    `CHECK_FALSE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'h1010_DA7A);

    dmem_ren = 1'b0;
    `TICK(clk);
  endtask

  //
  // Test: I/O write bypass (bit 31 = 1)
  //
  task automatic test_io_write_bypass;
    dmem_we    = 1'b1;
    dmem_waddr = 32'h8000_0200;
    dmem_wdata = 32'hFEED_FACE;
    dmem_wstrb = 4'hF;

    //
    // Should not go to cache
    //
    `CHECK_TRUE(io_wen);
    `CHECK_EQ(io_waddr, 32'h8000_0200);
    `CHECK_EQ(io_wdata, 32'hFEED_FACE);
    `CHECK_EQ(io_wstrb, 4'hF);
    `CHECK_FALSE(cache_wr_valid);

    `TICK(clk);

    //
    // I/O write is immediate, no stall
    //
    `CHECK_FALSE(dmem_stall);

    dmem_we = 1'b0;
    `TICK(clk);
  endtask

  //
  // Test: cache_rd_addr uses mux for protocol compliance
  //
  // Before transaction starts (cache_rd_valid=0): combinational for hit lookup
  // During active transaction (valid && !ready): stable from registered address
  // When transaction completes (valid && ready): combinational for new request
  //
  task automatic test_address_registration;
    dmem_ren       = 1'b1;
    dmem_raddr     = 32'h0000_4000;
    cache_rd_ready = 1'b0;

    // Before TICK: cache_rd_valid=0, so cache_rd_addr = dmem_raddr (combinational)
    `CHECK_EQ(cache_rd_addr, 32'h0000_4000);

    `TICK(clk);

    // After TICK: cache_rd_valid=1, cache_rd_ready=0 (no data yet)
    // Address is stable during active transaction
    dmem_raddr = 32'h0000_5000;
    `CHECK_EQ(cache_rd_addr, 32'h0000_4000);

    // Complete the request - ready goes high
    cache_rd_ready      = 1'b1;
    cache_rd_data       = 32'hAAAA_BBBB;
    cache_rd_data_valid = 1'b1;

    // Now valid && ready, so mux switches to dmem_raddr for new request
    `CHECK_EQ(cache_rd_addr, 32'h0000_5000);

    `TICK(clk);

    dmem_ren            = 1'b0;
    cache_rd_data_valid = 1'b0;
    `TICK(clk);
  endtask

  //
  // Test: Speculative cache hit (zero-stall path)
  //
  task automatic test_speculative_hit;
    // Simulate cache hit signal
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b1;

    // No stall on hit (combinational)
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    // cache_rd_valid now high (registered), cache returns data
    `CHECK_TRUE(cache_rd_valid);
    dmem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'hDEAD_BEEF;
    cache_rd_data_valid = 1'b1;

    // Still no stall, data available
    `CHECK_FALSE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'hDEAD_BEEF);

    cache_rd_data_valid = 1'b0;
    `TICK(clk);
  endtask

  //
  // Test: Back-to-back speculative hits
  //
  task automatic test_back_to_back_hits;
    // First hit
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b1;

    `CHECK_FALSE(dmem_stall);
    `TICK(clk);

    // Second hit while first data arrives
    dmem_raddr          = 32'h0000_1004;
    cache_rd_data       = 32'h1111_1111;
    cache_rd_data_valid = 1'b1;
    cache_rd_hit        = 1'b1;

    `CHECK_FALSE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'h1111_1111);

    `TICK(clk);

    // Third hit while second data arrives
    dmem_raddr    = 32'h0000_1008;
    cache_rd_data = 32'h2222_2222;
    cache_rd_hit  = 1'b1;

    `CHECK_FALSE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'h2222_2222);

    `TICK(clk);

    // End sequence
    dmem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'h3333_3333;
    cache_rd_data_valid = 1'b1;

    `CHECK_EQ(dmem_rdata, 32'h3333_3333);

    cache_rd_data_valid = 1'b0;
    `TICK(clk);
  endtask

  //
  // Test: Miss after hit
  //
  task automatic test_miss_after_hit;
    // First: speculative hit
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b1;

    `CHECK_FALSE(dmem_stall);
    `TICK(clk);

    // Second: miss (cache_rd_hit goes low)
    dmem_raddr          = 32'h0000_2000;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'hAAAA_AAAA;
    cache_rd_data_valid = 1'b1;

    // Now we stall on the miss
    `CHECK_TRUE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'hAAAA_AAAA);

    cache_rd_data_valid = 1'b0;
    `TICK(clk);

    // In READING state, waiting for data
    dmem_ren = 1'b0;
    `CHECK_TRUE(dmem_stall);

    // Miss data arrives
    cache_rd_data       = 32'hBBBB_BBBB;
    cache_rd_data_valid = 1'b1;
    `TICK(clk);

    `CHECK_TRUE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'hBBBB_BBBB);

    cache_rd_data_valid = 1'b0;
    `TICK(clk);

    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: Hit after miss
  //
  task automatic test_hit_after_miss;
    // First: miss
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b0;

    `CHECK_TRUE(dmem_stall);
    `TICK(clk);

    dmem_ren = 1'b0;
    `CHECK_TRUE(dmem_stall);

    // Miss data arrives
    cache_rd_data       = 32'hCCCC_CCCC;
    cache_rd_data_valid = 1'b1;
    `TICK(clk);

    `CHECK_EQ(dmem_rdata, 32'hCCCC_CCCC);

    cache_rd_data_valid = 1'b0;
    `TICK(clk);

    `CHECK_FALSE(dmem_stall);

    // Now: speculative hit
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_2000;
    cache_rd_hit = 1'b1;

    `CHECK_FALSE(dmem_stall);
    `TICK(clk);

    dmem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'hDDDD_DDDD;
    cache_rd_data_valid = 1'b1;

    `CHECK_FALSE(dmem_stall);
    `CHECK_EQ(dmem_rdata, 32'hDDDD_DDDD);

    cache_rd_data_valid = 1'b0;
    `TICK(clk);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_dmem_cache_if_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_cache_read_hit);
  `TEST_CASE(test_cache_read_miss);
  `TEST_CASE(test_cache_write);
  `TEST_CASE(test_io_read_bypass);
  `TEST_CASE(test_io_write_bypass);
  `TEST_CASE(test_address_registration);
  `TEST_CASE(test_speculative_hit);
  `TEST_CASE(test_back_to_back_hits);
  `TEST_CASE(test_miss_after_hit);
  `TEST_CASE(test_hit_after_miss);
  `TEST_SUITE_END();

endmodule
