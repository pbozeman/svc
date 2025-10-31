`include "svc_unit.sv"

`include "svc_rv_dmem.sv"

module svc_rv_dmem_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int DW = 32;
  localparam int AW = 10;

  logic [  AW-1:0] addr;
  logic [  DW-1:0] wdata;
  logic            we;
  logic [DW/8-1:0] wstrb;
  logic [  DW-1:0] rdata_reg;
  logic [  DW-1:0] rdata_unreg;

  //
  // Registered DMEM (1 cycle latency for BRAM inference)
  //
  svc_rv_dmem #(
      .DW        (DW),
      .AW        (AW),
      .REGISTERED(1)
  ) uut_reg (
      .clk  (clk),
      .rst_n(rst_n),
      .addr (addr),
      .wdata(wdata),
      .we   (we),
      .wstrb(wstrb),
      .rdata(rdata_reg)
  );

  //
  // Unregistered DMEM (combinational, for single-cycle designs)
  //
  svc_rv_dmem #(
      .DW        (DW),
      .AW        (AW),
      .REGISTERED(0)
  ) uut_unreg (
      .clk  (clk),
      .rst_n(rst_n),
      .addr (addr),
      .wdata(wdata),
      .we   (we),
      .wstrb(wstrb),
      .rdata(rdata_unreg)
  );

  task automatic test_initial_zero;
    //
    // Memory should initialize to zero
    //
    addr = 0;
    we   = 0;
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h0000_0000);
    `CHECK_EQ(rdata_unreg, 32'h0000_0000);

    addr = 100;
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h0000_0000);
    `CHECK_EQ(rdata_unreg, 32'h0000_0000);
  endtask

  task automatic test_word_write_read;
    //
    // Test full word writes with all byte write strobes
    //
    addr  = 0;
    wdata = 32'hDEAD_BEEF;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Disable write, read back
    // Registered version has 1-cycle latency
    //
    we   = 0;
    addr = 0;
    `CHECK_EQ(rdata_unreg, 32'hDEAD_BEEF);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'hDEAD_BEEF);
    `CHECK_EQ(rdata_unreg, 32'hDEAD_BEEF);

    //
    // Write to different address
    //
    addr  = 10;
    wdata = 32'h1234_5678;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Read back
    //
    we   = 0;
    addr = 10;
    `CHECK_EQ(rdata_unreg, 32'h1234_5678);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h1234_5678);
    `CHECK_EQ(rdata_unreg, 32'h1234_5678);

    //
    // Verify first location unchanged
    //
    addr = 0;
    `CHECK_EQ(rdata_unreg, 32'hDEAD_BEEF);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'hDEAD_BEEF);
    `CHECK_EQ(rdata_unreg, 32'hDEAD_BEEF);
  endtask

  task automatic test_byte_enable_byte0;
    //
    // Write initial value
    //
    addr  = 5;
    wdata = 32'hAAAA_AAAA;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Write only byte 0, others should remain unchanged
    //
    wdata = 32'h0000_00FF;
    we    = 1;
    wstrb = 4'b0001;
    `TICK(clk);

    we   = 0;
    addr = 5;
    `CHECK_EQ(rdata_unreg, 32'hAAAA_AAFF);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'hAAAA_AAFF);
    `CHECK_EQ(rdata_unreg, 32'hAAAA_AAFF);
  endtask

  task automatic test_byte_enable_byte1;
    //
    // Write initial value
    //
    addr  = 6;
    wdata = 32'hBBBB_BBBB;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Write only byte 1
    //
    wdata = 32'h0000_EE00;
    we    = 1;
    wstrb = 4'b0010;
    `TICK(clk);

    we   = 0;
    addr = 6;
    `CHECK_EQ(rdata_unreg, 32'hBBBB_EEBB);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'hBBBB_EEBB);
    `CHECK_EQ(rdata_unreg, 32'hBBBB_EEBB);
  endtask

  task automatic test_byte_enable_byte2;
    //
    // Write initial value
    //
    addr  = 7;
    wdata = 32'hCCCC_CCCC;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Write only byte 2
    //
    wdata = 32'h00DD_0000;
    we    = 1;
    wstrb = 4'b0100;
    `TICK(clk);

    we   = 0;
    addr = 7;
    `CHECK_EQ(rdata_unreg, 32'hCCDD_CCCC);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'hCCDD_CCCC);
    `CHECK_EQ(rdata_unreg, 32'hCCDD_CCCC);
  endtask

  task automatic test_byte_enable_byte3;
    //
    // Write initial value
    //
    addr  = 8;
    wdata = 32'hDDDD_DDDD;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Write only byte 3
    //
    wdata = 32'h11_0000_00;
    we    = 1;
    wstrb = 4'b1000;
    `TICK(clk);

    we   = 0;
    addr = 8;
    `CHECK_EQ(rdata_unreg, 32'h11DD_DDDD);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h11DD_DDDD);
    `CHECK_EQ(rdata_unreg, 32'h11DD_DDDD);
  endtask

  task automatic test_byte_enable_halfword_low;
    //
    // Write initial value
    //
    addr  = 9;
    wdata = 32'hFFFF_FFFF;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Write lower halfword (bytes 0-1)
    //
    wdata = 32'h0000_1234;
    we    = 1;
    wstrb = 4'b0011;
    `TICK(clk);

    we   = 0;
    addr = 9;
    `CHECK_EQ(rdata_unreg, 32'hFFFF_1234);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'hFFFF_1234);
    `CHECK_EQ(rdata_unreg, 32'hFFFF_1234);
  endtask

  task automatic test_byte_enable_halfword_high;
    //
    // Write initial value
    //
    addr  = 10;
    wdata = 32'h0000_0000;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Write upper halfword (bytes 2-3)
    //
    wdata = 32'h5678_0000;
    we    = 1;
    wstrb = 4'b1100;
    `TICK(clk);

    we   = 0;
    addr = 10;
    `CHECK_EQ(rdata_unreg, 32'h5678_0000);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h5678_0000);
    `CHECK_EQ(rdata_unreg, 32'h5678_0000);
  endtask

  task automatic test_read_during_write;
    //
    // Initialize memory location via hierarchical access
    //
    uut_reg.mem[15]   = 32'h01DD_DA7A;
    uut_unreg.mem[15] = 32'h01DD_DA7A;

    //
    // Read returns OLD data during write (standard BRAM behavior)
    //
    addr              = 15;
    wdata             = 32'hFE4_DA7A;
    we                = 1;
    wstrb             = 4'b1111;

    //
    // On same cycle as write, read should return OLD data
    // Note: This tests read-during-write to SAME address
    // Registered version: old data shows up after clock
    // Unregistered version: old data shows up immediately
    //
    `CHECK_EQ(rdata_unreg, 32'h01DD_DA7A);
    `TICK(clk);
    //
    // The read register was updated with OLD data on this clock
    //
    `CHECK_EQ(rdata_reg, 32'h01DD_DA7A);
    `CHECK_EQ(rdata_unreg, 32'h0FE4_DA7A);

    //
    // Next read should see NEW data
    //
    we   = 0;
    addr = 15;
    `CHECK_EQ(rdata_unreg, 32'h0FE4_DA7A);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h0FE4_DA7A);
    `CHECK_EQ(rdata_unreg, 32'h0FE4_DA7A);
  endtask

  task automatic test_write_enable_gating;
    //
    // Write a value
    //
    addr  = 20;
    wdata = 32'h1111_1111;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Try to write with we=0, should not modify memory
    //
    wdata = 32'h2222_2222;
    we    = 0;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Read back, should still be 0x1111_1111
    //
    addr = 20;
    `CHECK_EQ(rdata_unreg, 32'h1111_1111);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h1111_1111);
    `CHECK_EQ(rdata_unreg, 32'h1111_1111);
  endtask

  task automatic test_multiple_byte_write;
    //
    // Write initial pattern
    //
    addr  = 25;
    wdata = 32'h0000_0000;
    we    = 1;
    wstrb = 4'b1111;
    `TICK(clk);

    //
    // Write bytes 0 and 2 only (non-contiguous)
    //
    wdata = 32'hAA_00_BB;
    we    = 1;
    wstrb = 4'b0101;
    `TICK(clk);

    we   = 0;
    addr = 25;
    `CHECK_EQ(rdata_unreg, 32'h00AA_00BB);
    `TICK(clk);
    `CHECK_EQ(rdata_reg, 32'h00AA_00BB);
    `CHECK_EQ(rdata_unreg, 32'h00AA_00BB);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_dmem_tb);
  `TEST_CASE(test_initial_zero);
  `TEST_CASE(test_word_write_read);
  `TEST_CASE(test_byte_enable_byte0);
  `TEST_CASE(test_byte_enable_byte1);
  `TEST_CASE(test_byte_enable_byte2);
  `TEST_CASE(test_byte_enable_byte3);
  `TEST_CASE(test_byte_enable_halfword_low);
  `TEST_CASE(test_byte_enable_halfword_high);
  `TEST_CASE(test_read_during_write);
  `TEST_CASE(test_write_enable_gating);
  `TEST_CASE(test_multiple_byte_write);
  `TEST_SUITE_END();

endmodule
