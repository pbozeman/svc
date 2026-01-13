`include "svc_unit.sv"

`include "svc_rv_imem_cache_if.sv"

//
// Testbench for RISC-V imem to cache interface bridge
//
// Read-only interface for instruction fetch:
// - cache_rd_valid is combinational (same cycle as imem_ren)
// - Hits don't stall (no cooldown cycle)
// - No write support, no I/O bypass
//

module svc_rv_imem_cache_if_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  //
  // CPU imem interface
  //
  logic        imem_ren;
  logic [31:0] imem_raddr;
  logic [31:0] imem_rdata;

  logic        imem_stall;

  //
  // Cache interface
  //
  logic        cache_rd_valid;
  logic        cache_rd_ready;
  logic [31:0] cache_rd_addr;

  logic [31:0] cache_rd_data;
  logic        cache_rd_data_valid;
  logic        cache_rd_hit;

  svc_rv_imem_cache_if uut (
      .clk  (clk),
      .rst_n(rst_n),

      .imem_ren  (imem_ren),
      .imem_raddr(imem_raddr),
      .imem_rdata(imem_rdata),

      .imem_stall(imem_stall),

      .cache_rd_valid     (cache_rd_valid),
      .cache_rd_ready     (cache_rd_ready),
      .cache_rd_addr      (cache_rd_addr),
      .cache_rd_data      (cache_rd_data),
      .cache_rd_data_valid(cache_rd_data_valid),
      .cache_rd_hit       (cache_rd_hit)
  );

  //
  // Initialize test inputs
  //
  initial begin
    imem_ren            = 1'b0;
    imem_raddr          = 32'h0;

    cache_rd_ready      = 1'b1;
    cache_rd_data       = 32'h0;
    cache_rd_data_valid = 1'b0;
    cache_rd_hit        = 1'b0;
  end

  //
  // Test: Reset state
  //
  task automatic test_reset;
    `CHECK_FALSE(imem_stall);
    `CHECK_FALSE(cache_rd_valid);
  endtask

  //
  // Test: Cache read hit (zero stall)
  //
  // cache_rd_valid is combinational, so it appears
  // in the same cycle as imem_ren. Hits don't stall.
  //
  // Note: cache_rd_hit is a *response* qualifier (aligned with
  // cache_rd_data_valid), not a speculative/combinational "will hit" signal.
  //
  task automatic test_cache_read_hit;
    imem_ren     = 1'b1;
    imem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b0;

    // Combinational: cache_rd_valid appears immediately
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_1000);

    // Hits don't stall
    `CHECK_FALSE(imem_stall);

    `TICK(clk);

    // Data arrives from cache (cache_rd_data_valid next cycle after hit)
    imem_ren            = 1'b0;
    cache_rd_hit        = 1'b1;
    cache_rd_data       = 32'hCAFE_BABE;
    cache_rd_data_valid = 1'b1;

    // Still no stall for hits
    `CHECK_FALSE(imem_stall);

    // imem_rdata is combinational passthrough - check while data_valid is high
    `CHECK_EQ(imem_rdata, 32'hCAFE_BABE);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
    `CHECK_FALSE(imem_stall);
  endtask

  //
  // Test: Cache read miss (stalls while miss_inflight)
  //
  task automatic test_cache_read_miss;
    imem_ren     = 1'b1;
    imem_raddr   = 32'h0000_2000;
    cache_rd_hit = 1'b0;

    // Miss: combinational cache_rd_valid, stall comes the following cycle
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_2000);
    `CHECK_FALSE(imem_stall);

    `TICK(clk);

    // miss_start_d1/miss_inflight are now set, cache is no longer idle
    imem_ren       = 1'b0;
    cache_rd_ready = 1'b0;

    `CHECK_FALSE(cache_rd_valid);
    `CHECK_TRUE(imem_stall);

    // Simulate multiple cycles waiting for fill
    repeat (3) begin
      `TICK(clk);
      `CHECK_TRUE(imem_stall);
    end

    // Data arrives from cache fill
    cache_rd_data       = 32'hDEAD_BEEF;
    cache_rd_data_valid = 1'b1;
    cache_rd_ready      = 1'b1;

    // imem_rdata is combinational passthrough - check while data_valid is high
    `CHECK_EQ(imem_rdata, 32'hDEAD_BEEF);

    // Still stalled - miss_returning will be set next cycle
    `CHECK_TRUE(imem_stall);

    `TICK(clk);

    // miss_returning is now set, stall held for one extra cycle
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(imem_stall);

    `TICK(clk);

    // miss_returning clears, stall finally drops
    `CHECK_FALSE(imem_stall);
  endtask

  //
  // Test: cache_rd_addr stability during handshake (proper valid/ready protocol)
  //
  // For immediate handshakes (ready high), address is combinational passthrough.
  // For delayed handshakes (ready low), address is registered to maintain
  // stability while cache_rd_valid is held high.
  //
  task automatic test_address_passthrough;
    imem_ren       = 1'b1;
    imem_raddr     = 32'h0000_4000;
    cache_rd_hit   = 1'b0;
    cache_rd_ready = 1'b0;

    // Combinational passthrough on start
    `CHECK_EQ(cache_rd_addr, 32'h0000_4000);

    `TICK(clk);

    // Hold valid high across backpressure and keep address stable.
    imem_ren   = 1'b0;

    // Address is registered - maintains original request address for stability
    // (proper valid/ready protocol requires stable address during handshake)
    imem_raddr = 32'h0000_5000;
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_4000);  // still original address

    // Release backpressure and allow handshake to complete.
    cache_rd_ready = 1'b1;
    `TICK(clk);

    cache_rd_ready = 1'b1;
  endtask

  //
  // Test: Speculative cache hit (zero-stall path)
  //
  // cache_rd_valid is combinational, so hit detection uses the
  // same address as the rd_valid.
  //
  task automatic test_speculative_hit;
    imem_ren     = 1'b1;
    imem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b0;

    // Combinational: valid and hit use same address
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_1000);
    `CHECK_FALSE(imem_stall);

    `TICK(clk);

    // Cache returns data
    imem_ren            = 1'b0;
    cache_rd_hit        = 1'b1;
    cache_rd_data       = 32'hDEAD_BEEF;
    cache_rd_data_valid = 1'b1;

    `CHECK_FALSE(imem_stall);
    // imem_rdata is combinational passthrough - check while data_valid is high
    `CHECK_EQ(imem_rdata, 32'hDEAD_BEEF);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
  endtask

  //
  // Test: Back-to-back speculative hits
  //
  task automatic test_back_to_back_hits;
    // First hit
    imem_ren     = 1'b1;
    imem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b0;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(imem_stall);

    `TICK(clk);

    // Second hit while first data arrives
    imem_raddr          = 32'h0000_1004;
    cache_rd_data       = 32'h1111_1111;
    cache_rd_data_valid = 1'b1;
    cache_rd_hit        = 1'b1;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(imem_stall);
    // imem_rdata is combinational - first data visible now
    `CHECK_EQ(imem_rdata, 32'h1111_1111);

    `TICK(clk);

    // Third hit while second data arrives
    imem_raddr    = 32'h0000_1008;
    cache_rd_data = 32'h2222_2222;
    cache_rd_hit  = 1'b1;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(imem_stall);
    // imem_rdata is combinational - second data visible now
    `CHECK_EQ(imem_rdata, 32'h2222_2222);

    `TICK(clk);

    // End sequence
    imem_ren            = 1'b0;
    cache_rd_hit        = 1'b0;
    cache_rd_data       = 32'h3333_3333;
    cache_rd_data_valid = 1'b1;

    // imem_rdata is combinational - third data visible now
    `CHECK_EQ(imem_rdata, 32'h3333_3333);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
  endtask

  //
  // Test: Miss after hit
  //
  task automatic test_miss_after_hit;
    // First: speculative hit
    imem_ren     = 1'b1;
    imem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b0;

    `CHECK_FALSE(imem_stall);
    `TICK(clk);

    // Second: miss (cache_rd_hit goes low)
    // First hit's data arrives same cycle
    imem_raddr          = 32'h0000_2000;
    cache_rd_hit        = 1'b1;
    cache_rd_data       = 32'hAAAA_AAAA;
    cache_rd_data_valid = 1'b1;

    // Hit data valid suppresses stall to allow WB write
    // (miss_inflight not set yet - happens on posedge)
    `CHECK_FALSE(imem_stall);
    // imem_rdata is combinational - first hit's data visible now
    `CHECK_EQ(imem_rdata, 32'hAAAA_AAAA);

    `TICK(clk);

    // miss_inflight now set, stall asserted
    imem_ren            = 1'b0;
    cache_rd_ready      = 1'b0;
    cache_rd_data_valid = 1'b0;
    cache_rd_hit        = 1'b0;
    `CHECK_TRUE(imem_stall);

    // Simulate fill latency
    repeat (2) begin
      `TICK(clk);
      `CHECK_TRUE(imem_stall);
    end

    // Miss data arrives
    cache_rd_data       = 32'hBBBB_BBBB;
    cache_rd_data_valid = 1'b1;
    cache_rd_ready      = 1'b1;

    // imem_rdata is combinational - miss data visible now
    `CHECK_EQ(imem_rdata, 32'hBBBB_BBBB);

    `TICK(clk);

    // miss_returning holds stall for one extra cycle
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(imem_stall);
    `TICK(clk);

    `CHECK_FALSE(imem_stall);
  endtask

  //
  // Test: Hit after miss
  //
  task automatic test_hit_after_miss;
    // First: miss
    imem_ren     = 1'b1;
    imem_raddr   = 32'h0000_1000;
    cache_rd_hit = 1'b0;

    `CHECK_FALSE(imem_stall);
    `TICK(clk);

    imem_ren       = 1'b0;
    cache_rd_ready = 1'b0;
    `CHECK_TRUE(imem_stall);

    // Simulate fill latency
    repeat (2) begin
      `TICK(clk);
      `CHECK_TRUE(imem_stall);
    end

    // Miss data arrives
    cache_rd_data       = 32'hCCCC_CCCC;
    cache_rd_data_valid = 1'b1;
    cache_rd_ready      = 1'b1;

    // imem_rdata is combinational - miss data visible now
    `CHECK_EQ(imem_rdata, 32'hCCCC_CCCC);

    `TICK(clk);

    // miss_returning holds stall for one extra cycle
    cache_rd_data_valid = 1'b0;
    `CHECK_TRUE(imem_stall);
    `TICK(clk);

    `CHECK_FALSE(imem_stall);

    // Now: speculative hit
    imem_ren     = 1'b1;
    imem_raddr   = 32'h0000_2000;
    cache_rd_hit = 1'b0;

    `CHECK_TRUE(cache_rd_valid);
    `CHECK_FALSE(imem_stall);
    `TICK(clk);

    imem_ren            = 1'b0;
    cache_rd_hit        = 1'b1;
    cache_rd_data       = 32'hDDDD_DDDD;
    cache_rd_data_valid = 1'b1;

    `CHECK_FALSE(imem_stall);
    // imem_rdata is combinational - hit data visible now
    `CHECK_EQ(imem_rdata, 32'hDDDD_DDDD);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
  endtask

  //
  // Test: Wait for cache ready
  //
  // When cache_rd_ready is low, the interface waits in STATE_WAIT_CACHE
  //
  task automatic test_wait_cache_ready;
    imem_ren       = 1'b1;
    imem_raddr     = 32'h0000_6000;
    cache_rd_ready = 1'b0;  // Cache not ready
    cache_rd_hit   = 1'b0;

    // Request issued, but cache not ready
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_EQ(cache_rd_addr, 32'h0000_6000);
    `CHECK_FALSE(imem_stall);  // No stall on first cycle

    `TICK(clk);

    // Now in STATE_WAIT_CACHE, stall asserted
    imem_ren = 1'b0;
    `CHECK_TRUE(cache_rd_valid);  // Valid held until ready
    `CHECK_TRUE(imem_stall);

    // Wait a few cycles
    repeat (2) begin
      `TICK(clk);
      `CHECK_TRUE(cache_rd_valid);
      `CHECK_TRUE(imem_stall);
    end

    // Cache becomes ready
    cache_rd_ready      = 1'b1;
    cache_rd_hit        = 1'b0;
    cache_rd_data_valid = 1'b0;

    `TICK(clk);

    // Hit response arrives next cycle
    cache_rd_hit        = 1'b1;
    cache_rd_data       = 32'hFEED_CAFE;
    cache_rd_data_valid = 1'b1;

    `CHECK_FALSE(imem_stall);
    `CHECK_EQ(imem_rdata, 32'hFEED_CAFE);

    `TICK(clk);

    cache_rd_data_valid = 1'b0;
    cache_rd_hit        = 1'b0;
    `CHECK_FALSE(imem_stall);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_imem_cache_if_tbi);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_cache_read_hit);
  `TEST_CASE(test_cache_read_miss);
  `TEST_CASE(test_address_passthrough);
  `TEST_CASE(test_speculative_hit);
  `TEST_CASE(test_back_to_back_hits);
  `TEST_CASE(test_miss_after_hit);
  `TEST_CASE(test_hit_after_miss);
  `TEST_CASE(test_wait_cache_ready);
  `TEST_SUITE_END();

endmodule
