//
// Common test definitions for svc_cache_axi testbenches
//

//
// Mirror of svc_cache_axi state enum for testbench access
//
typedef enum {
  STATE_IDLE,
  STATE_READ_BURST
} state_t;

//
// Reset and memory initialization
//
always_ff @(posedge clk) begin
  if (!rst_n) begin
    ren                   <= 0;
    wen                   <= 0;
    addr                  <= 0;
    wr_data               <= 0;
    wr_strb               <= 0;

    axi_mem.mem['h200>>2] <= 32'hDEADBEEF;
    axi_mem.mem['h300>>2] <= 32'hCAC4ED00;
    axi_mem.mem['h400>>2] <= 32'h12345678;
    axi_mem.mem['h480>>2] <= 32'hFEEDFACE;
    axi_mem.mem['h500>>2] <= 32'hABCDEF00;
    axi_mem.mem['h800>>2] <= 32'h0E71C7ED;

    // Stress test data: mem[addr] = addr
    for (int i = 0; i < 64; i++) begin
      axi_mem.mem[i] <= i;
    end
  end
end

//
// Test: Reset state
//
task automatic test_reset;
  `CHECK_FALSE(rd_valid);
  `CHECK_FALSE(axi_arvalid);
  `CHECK_FALSE(axi_awvalid);
  `CHECK_FALSE(axi_wvalid);
endtask

//
// Test: Read miss transitions to STATE_READ_BURST
//
task automatic test_read_miss;
  addr = 32'h100;
  ren  = 1;

  `TICK(clk);
  `CHECK_EQ(uut.state, STATE_READ_BURST);
endtask

//
// Test: Read miss fetches data correctly
//
task automatic test_read_miss_data;
  addr = 32'h200;
  ren  = 1;

  `CHECK_WAIT_FOR(clk, rd_valid, 8);
  `CHECK_EQ(rd_data, 32'hDEADBEEF);
endtask

//
// Test: Cache hit returns data immediately
//
task automatic test_cache_hit;
  // First read - cache miss
  addr = 32'h300;
  ren  = 1;
  `TICK(clk);
  ren = 0;

  `CHECK_WAIT_FOR(clk, rd_valid, 8);
  `CHECK_EQ(rd_data, 32'hCAC4ED00);

  // Second read - should hit cache
  ren = 1;
  `TICK(clk);
  `CHECK_TRUE(rd_valid);
  `CHECK_EQ(rd_data, 32'hCAC4ED00);
endtask

//
// Test: Stress test - read sequence of addresses, verify data
//
task automatic test_stress;
  // Read 32 words, verify each returns correct data
  for (int i = 0; i < 32; i++) begin
    addr = i << 2;
    ren  = 1;
    `CHECK_WAIT_FOR(clk, rd_valid, 10);
    `CHECK_EQ(rd_data, 32'(i));
    ren = 0;
    `TICK(clk);
  end

  // Re-read in reverse to exercise cache
  for (int i = 31; i >= 0; i--) begin
    addr = i << 2;
    ren  = 1;
    `CHECK_WAIT_FOR(clk, rd_valid, 10);
    `CHECK_EQ(rd_data, 32'(i));
    ren = 0;
    `TICK(clk);
  end
endtask
