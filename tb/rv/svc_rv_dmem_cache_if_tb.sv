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
    dmem_ren   = 1'b1;
    dmem_raddr = 32'h0000_2000;
    `TICK(clk);

    dmem_ren = 1'b0;

    //
    // Stalls while waiting for data
    //
    `CHECK_TRUE(cache_rd_valid);
    `CHECK_TRUE(dmem_stall);

    //
    // Simulate multiple cycles of cache miss
    //
    repeat (5) begin
      `TICK(clk);
      `CHECK_TRUE(dmem_stall);
      `CHECK_TRUE(cache_rd_valid);
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
    // Simulate cache accepting write after some cycles
    //
    repeat (3) begin
      `TICK(clk);
      `CHECK_TRUE(dmem_stall);
    end

    cache_wr_ready = 1'b1;
    `TICK(clk);

    //
    // Write complete, but stall held for cooldown cycle
    //
    `CHECK_TRUE(dmem_stall);

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
  // Test: Address registration persists during stall
  //
  task automatic test_address_registration;
    dmem_ren   = 1'b1;
    dmem_raddr = 32'h0000_4000;
    `TICK(clk);

    //
    // Change address while pending
    //
    dmem_ren   = 1'b1;
    dmem_raddr = 32'h0000_5000;
    `TICK(clk);

    //
    // Original address should be registered
    //
    `CHECK_EQ(cache_rd_addr, 32'h0000_4000);

    //
    // Complete the request
    //
    dmem_ren            = 1'b0;
    cache_rd_data       = 32'hAAAA_BBBB;
    cache_rd_data_valid = 1'b1;
    `TICK(clk);

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
  `TEST_SUITE_END();

endmodule
