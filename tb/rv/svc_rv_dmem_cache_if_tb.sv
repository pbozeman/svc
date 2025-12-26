`include "svc_unit.sv"

`include "svc_rv_dmem_cache_if.sv"

//
// Testbench for RISC-V dmem to cache interface bridge
//
// Tests the new simplified design:
// - cache_rd_valid is combinational (same cycle as dmem_ren)
// - Hits don't stall (no cooldown cycle)
// - miss_inflight / store_inflight flags instead of FSM
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
  // Test: Cache read hit (zero stall)
  //
  // New design: cache_rd_valid is combinational, so it appears
  // in the same cycle as dmem_ren. Hits don't stall.
  //
  task automatic test_cache_read_hit;
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b1;

    // Combinational: cache_rd_valid appears immediately
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_1000);

    // Hits don't stall
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    // Data arrives from cache (cache_rd_data_valid next cycle after hit)
    dmem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'hCAFE_BABE;
    cache_rd_data_valid = 1'b1;

    // Still no stall for hits
    `CHECK_FALSE(dmem_stall);

    // dmem_rdata is combinational passthrough - check while data_valid is high
    `CHECK_EQ(dmem_rdata, 32'hCAFE_BABE);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: Cache read miss (stalls while miss_inflight)
  //
  task automatic test_cache_read_miss;
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_2000;
    cache_rd_hit = 1'b0;

    // Miss: combinational cache_rd_valid, stall comes the following cycle
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_2000);
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    // miss_start_d1/miss_inflight are now set, cache is no longer idle
    dmem_ren       = 1'b0;
    cache_rd_ready = 1'b0;

    `CHECK_FALSE(cache_rd_valid);
    `CHECK_TRUE(dmem_stall);

    // Simulate multiple cycles waiting for fill
    repeat (3) begin
      `TICK(clk);
      `CHECK_TRUE(dmem_stall);
    end

    // Data arrives from cache fill
    cache_rd_data       = 32'hDEAD_BEEF;
    cache_rd_data_valid = 1'b1;
    cache_rd_ready      = 1'b1;

    // dmem_rdata is combinational passthrough - check while data_valid is high
    `CHECK_EQ(dmem_rdata, 32'hDEAD_BEEF);

    // Still stalled - miss_returning will be set next cycle
    `CHECK_TRUE(dmem_stall);

    `TICK(clk);

    // miss_returning is now set, stall held for one extra cycle
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(dmem_stall);

    `TICK(clk);

    // miss_returning clears, stall finally drops
    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: Cache write
  //
  // start_store doesn't stall - data is captured immediately.
  // store_inflight stalls subsequent ops until AXI completes.
  //
  task automatic test_cache_write;
    dmem_we    = 1'b1;
    dmem_waddr = 32'h0000_3000;
    dmem_wdata = 32'h1234_5678;
    dmem_wstrb = 4'hF;

    // Store starts: cache_wr_valid with direct CPU values, no stall yet
    `CHECK_TRUE(cache_wr_valid);
    `CHECK_EQ(cache_wr_addr, 32'h0000_3000);
    `CHECK_EQ(cache_wr_data, 32'h1234_5678);
    `CHECK_EQ(cache_wr_strb, 4'hF);
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    dmem_we = 1'b0;

    // store_inflight is now set, stall blocks subsequent ops
    `CHECK_TRUE(cache_wr_valid);
    `CHECK_EQ(cache_wr_addr, 32'h0000_3000);
    `CHECK_EQ(cache_wr_data, 32'h1234_5678);
    `CHECK_EQ(cache_wr_strb, 4'hF);
    `CHECK_TRUE(dmem_stall);

    // Simulate cache busy
    repeat (2) begin
      `TICK(clk);
      `CHECK_TRUE(dmem_stall);
      `CHECK_TRUE(cache_wr_valid);
    end

    // Cache completes write
    cache_wr_ready = 1'b1;
    `TICK(clk);

    cache_wr_ready = 1'b0;
    `CHECK_FALSE(cache_wr_valid);
    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: I/O read bypass (bit 31 = 1)
  //
  task automatic test_io_read_bypass;
    dmem_ren   = 1'b1;
    dmem_raddr = 32'h8000_0100;
    io_rdata   = 32'h1010_DA7A;

    // Should not go to cache
    `CHECK_TRUE(io_ren);
    `CHECK_EQ(io_raddr, 32'h8000_0100);
    `CHECK_FALSE(cache_rd_valid);

    // No stall for I/O
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    // I/O has 1-cycle latency
    dmem_ren = 1'b0;
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    // Data captured after 1 cycle
    `CHECK_EQ(dmem_rdata, 32'h1010_DA7A);
  endtask

  //
  // Test: I/O write bypass (bit 31 = 1)
  //
  task automatic test_io_write_bypass;
    dmem_we    = 1'b1;
    dmem_waddr = 32'h8000_0200;
    dmem_wdata = 32'hFEED_FACE;
    dmem_wstrb = 4'hF;

    // Should not go to cache
    `CHECK_TRUE(io_wen);
    `CHECK_EQ(io_waddr, 32'h8000_0200);
    `CHECK_EQ(io_wdata, 32'hFEED_FACE);
    `CHECK_EQ(io_wstrb, 4'hF);
    `CHECK_FALSE(cache_wr_valid);

    // No stall for I/O writes
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    dmem_we = 1'b0;
    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: cache_rd_addr is always dmem_raddr (no mux)
  //
  // Test address stability during handshake (proper valid/ready protocol)
  //
  // For immediate handshakes (ready high), address is combinational passthrough.
  // For delayed handshakes, address is registered to maintain stability.
  //
  task automatic test_address_passthrough;
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_4000;
    cache_rd_hit = 1'b0;

    // Combinational passthrough on start
    `CHECK_EQ(cache_rd_addr, 32'h0000_4000);

    `TICK(clk);

    // miss_inflight set, cache_rd_valid goes low
    cache_rd_ready = 1'b0;
    dmem_ren       = 1'b0;

    // Address is registered - maintains original request address for stability
    // (proper valid/ready protocol requires stable address during handshake)
    dmem_raddr     = 32'h0000_5000;
    `CHECK_EQ(cache_rd_addr, 32'h0000_4000);  // still original address

    // Complete the miss
    cache_rd_data       = 32'hAAAA_BBBB;
    cache_rd_data_valid = 1'b1;
    cache_rd_ready      = 1'b1;
    `TICK(clk);

    // miss_returning holds stall for one extra cycle
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(dmem_stall);
    `TICK(clk);

    `CHECK_FALSE(dmem_stall);
  endtask

  //
  // Test: Speculative cache hit (zero-stall path)
  //
  // This is the key improvement: cache_rd_valid is combinational,
  // so hit detection uses the same address as the rd_valid.
  //
  task automatic test_speculative_hit;
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b1;

    // Combinational: valid and hit use same address
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_1000);
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    // Cache returns data
    dmem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'hDEAD_BEEF;
    cache_rd_data_valid = 1'b1;

    `CHECK_FALSE(dmem_stall);
    // dmem_rdata is combinational passthrough - check while data_valid is high
    `CHECK_EQ(dmem_rdata, 32'hDEAD_BEEF);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
  endtask

  //
  // Test: Back-to-back speculative hits
  //
  task automatic test_back_to_back_hits;
    // First hit
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b1;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(dmem_stall);

    `TICK(clk);

    // Second hit while first data arrives
    dmem_raddr          = 32'h0000_1004;
    cache_rd_data       = 32'h1111_1111;
    cache_rd_data_valid = 1'b1;
    cache_rd_hit        = 1'b1;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(dmem_stall);
    // dmem_rdata is combinational - first data visible now
    `CHECK_EQ(dmem_rdata, 32'h1111_1111);

    `TICK(clk);

    // Third hit while second data arrives
    dmem_raddr    = 32'h0000_1008;
    cache_rd_data = 32'h2222_2222;
    cache_rd_hit  = 1'b1;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(dmem_stall);
    // dmem_rdata is combinational - second data visible now
    `CHECK_EQ(dmem_rdata, 32'h2222_2222);

    `TICK(clk);

    // End sequence
    dmem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'h3333_3333;
    cache_rd_data_valid = 1'b1;

    // dmem_rdata is combinational - third data visible now
    `CHECK_EQ(dmem_rdata, 32'h3333_3333);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
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
    // First hit's data arrives same cycle
    dmem_raddr          = 32'h0000_2000;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'hAAAA_AAAA;
    cache_rd_data_valid = 1'b1;

    // Hit data valid suppresses stall to allow WB write
    // (miss_inflight not set yet - happens on posedge)
    `CHECK_FALSE(dmem_stall);
    // dmem_rdata is combinational - first hit's data visible now
    `CHECK_EQ(dmem_rdata, 32'hAAAA_AAAA);

    `TICK(clk);

    // miss_inflight now set, stall asserted
    dmem_ren            = 1'b0;
    cache_rd_ready      = 1'b0;
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(dmem_stall);

    // Miss data arrives
    cache_rd_data       = 32'hBBBB_BBBB;
    cache_rd_data_valid = 1'b1;
    cache_rd_ready      = 1'b1;

    // dmem_rdata is combinational - miss data visible now
    `CHECK_EQ(dmem_rdata, 32'hBBBB_BBBB);

    `TICK(clk);

    // miss_returning holds stall for one extra cycle
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(dmem_stall);
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

    `CHECK_FALSE(dmem_stall);
    `TICK(clk);

    dmem_ren       = 1'b0;
    cache_rd_ready = 1'b0;
    `CHECK_TRUE(dmem_stall);

    // Miss data arrives
    cache_rd_data       = 32'hCCCC_CCCC;
    cache_rd_data_valid = 1'b1;
    cache_rd_ready      = 1'b1;

    // dmem_rdata is combinational - miss data visible now
    `CHECK_EQ(dmem_rdata, 32'hCCCC_CCCC);

    `TICK(clk);

    // miss_returning holds stall for one extra cycle
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(dmem_stall);
    `TICK(clk);

    `CHECK_FALSE(dmem_stall);

    // Now: speculative hit
    dmem_ren     = 1'b1;
    dmem_raddr   = 32'h0000_2000;
    cache_rd_hit = 1'b1;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(dmem_stall);
    `TICK(clk);

    dmem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'hDDDD_DDDD;
    cache_rd_data_valid = 1'b1;

    `CHECK_FALSE(dmem_stall);
    // dmem_rdata is combinational - hit data visible now
    `CHECK_EQ(dmem_rdata, 32'hDDDD_DDDD);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
  endtask

  //
  // Test: Write data stability during store_inflight
  //
  task automatic test_write_data_stability;
    dmem_we    = 1'b1;
    dmem_waddr = 32'h0000_5000;
    dmem_wdata = 32'hABCD_EF01;
    dmem_wstrb = 4'hF;

    `TICK(clk);

    // store_inflight set
    dmem_we    = 1'b0;

    // CPU may change waddr/wdata, but registered values are stable
    dmem_waddr = 32'hFFFF_FFFF;
    dmem_wdata = 32'h0000_0000;

    `CHECK_EQ(cache_wr_addr, 32'h0000_5000);
    `CHECK_EQ(cache_wr_data, 32'hABCD_EF01);
    `CHECK_EQ(cache_wr_strb, 4'hF);

    // Wait for completion
    cache_wr_ready = 1'b1;
    `TICK(clk);

    cache_wr_ready = 1'b0;
    `CHECK_FALSE(dmem_stall);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_dmem_cache_if_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_cache_read_hit);
  `TEST_CASE(test_cache_read_miss);
  `TEST_CASE(test_cache_write);
  `TEST_CASE(test_io_read_bypass);
  `TEST_CASE(test_io_write_bypass);
  `TEST_CASE(test_address_passthrough);
  `TEST_CASE(test_speculative_hit);
  `TEST_CASE(test_back_to_back_hits);
  `TEST_CASE(test_miss_after_hit);
  `TEST_CASE(test_hit_after_miss);
  `TEST_CASE(test_write_data_stability);
  `TEST_SUITE_END();

endmodule
