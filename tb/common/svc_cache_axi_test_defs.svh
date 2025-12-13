//
// Common test definitions for svc_cache_axi testbenches
//

//
// Mirror of svc_cache_axi state enum for testbench access
//
typedef enum {
  STATE_IDLE,
  STATE_READ_BURST,
  STATE_WRITE,
  STATE_WRITE_RESP
} state_t;

//
// Reset and memory initialization
//
always_ff @(posedge clk) begin
  if (!rst_n) begin
    rd_valid_in           <= 0;
    rd_addr               <= 0;
    wr_valid_in           <= 0;
    wr_addr               <= 0;
    wr_data               <= 0;
    wr_strb               <= 0;

    axi_mem.mem['h200>>2] <= 32'hDEADBEEF;
    axi_mem.mem['h300>>2] <= 32'hCAC4ED00;
    axi_mem.mem['h400>>2] <= 32'h12345678;
    axi_mem.mem['h480>>2] <= 32'hFEEDFACE;
    axi_mem.mem['h500>>2] <= 32'hABCDEF00;
    axi_mem.mem['h800>>2] <= 32'h0E71C7ED;
    axi_mem.mem['hC00>>2] <= 32'hAABBCCDD;
    axi_mem.mem['hC40>>2] <= 32'h11223344;

    // Stress test data: mem[addr] = addr
    for (int i = 0; i < 64; i++) begin
      axi_mem.mem[i] <= i;
    end
  end
end

//
// Auto-clear valid signals on handshake
//
always_ff @(posedge clk) begin
  if (rd_valid_in && rd_ready) begin
    rd_valid_in <= 1'b0;
  end
  if (wr_valid_in && wr_ready) begin
    wr_valid_in <= 1'b0;
  end
end

//
// Test: Reset state
//
task automatic test_reset;
  `CHECK_FALSE(rd_data_valid);
  `CHECK_FALSE(axi_arvalid);
  `CHECK_FALSE(axi_awvalid);
  `CHECK_FALSE(axi_wvalid);
endtask

//
// Test: Read miss transitions to STATE_READ_BURST
//
task automatic test_read_miss;
  rd_addr     = 32'h100;
  rd_valid_in = 1;

  `TICK(clk);
  `CHECK_EQ(uut.state, STATE_READ_BURST);
endtask

//
// Test: Read miss fetches data correctly
//
task automatic test_read_miss_data;
  rd_addr     = 32'h200;
  rd_valid_in = 1;

  `CHECK_WAIT_FOR(clk, rd_data_valid, 8);
  `CHECK_EQ(rd_data, 32'hDEADBEEF);
endtask

//
// Test: Cache hit returns data immediately
//
task automatic test_cache_hit;
  // First read - cache miss
  rd_addr     = 32'h300;
  rd_valid_in = 1;

  `CHECK_WAIT_FOR(clk, rd_data_valid, 8);
  `CHECK_EQ(rd_data, 32'hCAC4ED00);

  // Second read - should hit cache
  rd_valid_in = 1;
  `TICK(clk);
  `CHECK_TRUE(rd_data_valid);
  `CHECK_EQ(rd_data, 32'hCAC4ED00);
endtask

//
// Test: Stress test - read sequence of addresses, verify data
//
task automatic test_stress;
  // Read 32 words, verify each returns correct data
  for (int i = 0; i < 32; i++) begin
    rd_addr     = i << 2;
    rd_valid_in = 1;
    `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
    `CHECK_EQ(rd_data, 32'(i));
    `TICK(clk);
  end

  // Re-read in reverse to exercise cache
  for (int i = 31; i >= 0; i--) begin
    rd_addr     = i << 2;
    rd_valid_in = 1;
    `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
    `CHECK_EQ(rd_data, 32'(i));
    `TICK(clk);
  end
endtask

//
// Test: Write miss - write to uncached address goes to memory
//
task automatic test_write_miss;
  // Write to address not in cache
  wr_addr     = 32'h800;
  wr_data     = 32'hBEEFCAFE;
  wr_strb     = 4'hF;
  wr_valid_in = 1;

  // Wait for write to complete (return to IDLE)
  `TICK(clk);
  `CHECK_EQ(uut.state, STATE_WRITE);
  `CHECK_WAIT_FOR(clk, uut.state == STATE_IDLE, 10);

  // Verify data was written to memory
  `CHECK_EQ(axi_mem.mem['h800>>2], 32'hBEEFCAFE);
endtask

//
// Test: Write hit - write to cached address updates cache
//
task automatic test_write_hit;
  // First, read to bring line into cache
  rd_addr     = 32'h400;
  rd_valid_in = 1;
  `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
  `CHECK_EQ(rd_data, 32'h12345678);
  `TICK(clk);

  // Now write to same address (cache hit)
  wr_addr     = 32'h400;
  wr_data     = 32'hAAAABBBB;
  wr_strb     = 4'hF;
  wr_valid_in = 1;

  `TICK(clk);
  `CHECK_WAIT_FOR(clk, uut.state == STATE_IDLE, 10);

  // Verify memory was updated
  `CHECK_EQ(axi_mem.mem['h400>>2], 32'hAAAABBBB);
endtask

//
// Test: Write strobe - partial writes work correctly
//
task automatic test_write_strobe;
  // First, read to bring line into cache
  rd_addr     = 32'h500;
  rd_valid_in = 1;
  `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
  `CHECK_EQ(rd_data, 32'hABCDEF00);
  `TICK(clk);

  // Write only low byte (strobe = 0001)
  wr_addr     = 32'h500;
  wr_data     = 32'hFFFFFFAA;
  wr_strb     = 4'b0001;
  wr_valid_in = 1;

  `TICK(clk);
  `CHECK_WAIT_FOR(clk, uut.state == STATE_IDLE, 10);

  // Read back - should have only low byte changed
  rd_addr     = 32'h500;
  rd_valid_in = 1;
  `TICK(clk);
  `CHECK_TRUE(rd_data_valid);
  `CHECK_EQ(rd_data, 32'hABCDEFAA);
endtask

//
// Test: Read after write hit returns written data from cache
//
task automatic test_read_after_write_hit;
  // First, read to bring line into cache
  rd_addr     = 32'h480;
  rd_valid_in = 1;
  `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
  `CHECK_EQ(rd_data, 32'hFEEDFACE);
  `TICK(clk);

  // Write new data (cache hit)
  wr_addr     = 32'h480;
  wr_data     = 32'h11223344;
  wr_strb     = 4'hF;
  wr_valid_in = 1;

  `TICK(clk);
  `CHECK_WAIT_FOR(clk, uut.state == STATE_IDLE, 10);

  // Read same address - should return written data from cache
  rd_addr     = 32'h480;
  rd_valid_in = 1;
  `TICK(clk);
  `CHECK_TRUE(rd_data_valid);
  `CHECK_EQ(rd_data, 32'h11223344);
endtask

//
// Test: Read after write miss - verify write went to memory correctly
//
task automatic test_read_after_write_miss;
  // Write to uncached address with partial strobe
  // Initial memory at 0xC40 is 0x11223344
  // Write high byte only -> expect 0xEE223344
  wr_addr     = 32'hC40;
  wr_data     = 32'hEEFFFFFF;
  wr_strb     = 4'b1000;
  wr_valid_in = 1;

  `TICK(clk);
  `CHECK_WAIT_FOR(clk, uut.state == STATE_IDLE, 10);

  // Read back and verify
  rd_addr     = 32'hC40;
  rd_valid_in = 1;
  `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
  `CHECK_EQ(rd_data, 32'hEE223344);
endtask

//
// Test: Read during write - read different cache line
//
task automatic test_read_during_write_diff_line;
  // Pre-fill cache line at 0xC00
  rd_addr     = 32'hC00;
  rd_valid_in = 1;
  `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
  `CHECK_EQ(rd_data, 32'hAABBCCDD);
  `TICK(clk);

  // Start write to different address (0x800)
  wr_addr     = 32'h800;
  wr_data     = 32'h55667788;
  wr_strb     = 4'hF;
  wr_valid_in = 1;

  `TICK(clk);
  `CHECK_EQ(uut.state, STATE_WRITE);

  // Read from pre-filled cache line while write in progress
  rd_addr     = 32'hC00;
  rd_valid_in = 1;

  // Read hit should be accepted during write
  `CHECK_TRUE(rd_ready);

  // Data should be available next cycle
  `TICK(clk);
  `CHECK_TRUE(rd_data_valid);
  `CHECK_EQ(rd_data, 32'hAABBCCDD);

  // Wait for write to complete
  `CHECK_WAIT_FOR(clk, uut.state == STATE_IDLE, 10);
endtask

//
// Test: Read during write - read same cache line being written
//
task automatic test_read_during_write_same_line;
  // Pre-fill cache line at 0xC00
  rd_addr     = 32'hC00;
  rd_valid_in = 1;
  `CHECK_WAIT_FOR(clk, rd_data_valid, 10);
  `CHECK_EQ(rd_data, 32'hAABBCCDD);
  `TICK(clk);

  // Write to same address (cache updates before STATE_WRITE)
  wr_addr     = 32'hC00;
  wr_data     = 32'h99887766;
  wr_strb     = 4'hF;
  wr_valid_in = 1;

  `TICK(clk);
  `CHECK_EQ(uut.state, STATE_WRITE);

  // Read from same cache line while write in progress
  rd_addr     = 32'hC00;
  rd_valid_in = 1;

  // Read hit should be accepted during write
  `CHECK_TRUE(rd_ready);

  // Data should be the NEW written value
  `TICK(clk);
  `CHECK_TRUE(rd_data_valid);
  `CHECK_EQ(rd_data, 32'h99887766);

  // Wait for write to complete
  `CHECK_WAIT_FOR(clk, uut.state == STATE_IDLE, 10);
endtask
