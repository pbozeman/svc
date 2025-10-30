`include "svc_unit.sv"

`include "svc_rv_imem.sv"

module svc_rv_imem_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int AW = 10;

  logic          en;
  logic [AW-1:0] addr;
  logic [  31:0] data_reg;
  logic [  31:0] data_unreg;

  //
  // Registered IMEM (1 cycle latency for BRAM inference)
  //
  svc_rv_imem #(
      .AW        (AW),
      .REGISTERED(1)
  ) uut_reg (
      .clk  (clk),
      .rst_n(rst_n),
      .en   (en),
      .addr (addr),
      .data (data_reg)
  );

  //
  // Unregistered IMEM (combinational, for single-cycle designs)
  //
  svc_rv_imem #(
      .AW        (AW),
      .REGISTERED(0)
  ) uut_unreg (
      .clk  (clk),
      .rst_n(rst_n),
      .en   (en),
      .addr (addr),
      .data (data_unreg)
  );

  // Default enable to 1 for all tests
  initial en = 1;

  task automatic test_reset;
    uut_reg.mem[0]   = 32'hDEAD_BEEF;
    uut_unreg.mem[0] = 32'hDEAD_BEEF;
    addr             = 0;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hDEAD_BEEF);

    rst_n = 0;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'h0000_0000);

    rst_n = 1;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hDEAD_BEEF);

    uut_reg.mem[0]   = 32'h0000_0000;
    uut_unreg.mem[0] = 32'h0000_0000;
  endtask

  task automatic test_initial_zero;
    addr = 0;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'h0000_0000);
    `CHECK_EQ(data_unreg, 32'h0000_0000);

    addr = 100;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'h0000_0000);
    `CHECK_EQ(data_unreg, 32'h0000_0000);
  endtask

  task automatic test_write_read;
    uut_reg.mem[0]      = 32'hDEAD_BEEF;
    uut_reg.mem[1]      = 32'hCAFE_BABE;
    uut_reg.mem[10]     = 32'h1234_5678;
    uut_reg.mem[1023]   = 32'hAAAA_AAAA;
    uut_unreg.mem[0]    = 32'hDEAD_BEEF;
    uut_unreg.mem[1]    = 32'hCAFE_BABE;
    uut_unreg.mem[10]   = 32'h1234_5678;
    uut_unreg.mem[1023] = 32'hAAAA_AAAA;

    addr                = 0;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hDEAD_BEEF);
    `CHECK_EQ(data_unreg, 32'hDEAD_BEEF);

    addr = 1;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hCAFE_BABE);
    `CHECK_EQ(data_unreg, 32'hCAFE_BABE);

    addr = 10;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'h1234_5678);
    `CHECK_EQ(data_unreg, 32'h1234_5678);

    addr = 1023;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hAAAA_AAAA);
    `CHECK_EQ(data_unreg, 32'hAAAA_AAAA);
  endtask

  task automatic test_sequential_read;
    int i;

    for (i = 0; i < 16; i++) begin
      uut_reg.mem[i]   = i * 4;
      uut_unreg.mem[i] = i * 4;
    end

    for (i = 0; i < 16; i++) begin
      addr = i[AW-1:0];
      `TICK(clk);
      `CHECK_EQ(data_reg, i * 4);
      `CHECK_EQ(data_unreg, i * 4);
    end
  endtask

  //
  // Test: Registered output latency
  //
  // Verifies registered IMEM has 1 cycle latency while unregistered is
  // combinational.
  //
  task automatic test_registered_output;
    uut_reg.mem[5]   = 32'h1111_1111;
    uut_reg.mem[6]   = 32'h2222_2222;
    uut_unreg.mem[5] = 32'h1111_1111;
    uut_unreg.mem[6] = 32'h2222_2222;

    addr             = 5;
    `CHECK_TRUE(data_reg != 32'h1111_1111);

    `TICK(clk);
    `CHECK_EQ(data_reg, 32'h1111_1111);
    `CHECK_EQ(data_unreg, 32'h1111_1111);

    addr = 6;
    `CHECK_EQ(data_reg, 32'h1111_1111);
    `CHECK_EQ(data_unreg, 32'h2222_2222);

    `TICK(clk);
    `CHECK_EQ(data_reg, 32'h2222_2222);
    `CHECK_EQ(data_unreg, 32'h2222_2222);
  endtask

  //
  // Test: Enable hold for registered memory
  //
  // Verifies registered IMEM holds output when enable is low.
  // Unregistered IMEM ignores enable (always combinational).
  //
  task automatic test_enable_hold;
    uut_reg.mem[10]   = 32'hAAAA_AAAA;
    uut_reg.mem[11]   = 32'hBBBB_BBBB;
    uut_unreg.mem[10] = 32'hAAAA_AAAA;
    uut_unreg.mem[11] = 32'hBBBB_BBBB;

    en                = 1;
    addr              = 10;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hAAAA_AAAA);
    `CHECK_EQ(data_unreg, 32'hAAAA_AAAA);

    en   = 0;
    addr = 11;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hAAAA_AAAA);
    `CHECK_EQ(data_unreg, 32'hBBBB_BBBB);

    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hAAAA_AAAA);
    `CHECK_EQ(data_unreg, 32'hBBBB_BBBB);

    en = 1;
    `TICK(clk);
    `CHECK_EQ(data_reg, 32'hBBBB_BBBB);
    `CHECK_EQ(data_unreg, 32'hBBBB_BBBB);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_imem_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_initial_zero);
  `TEST_CASE(test_write_read);
  `TEST_CASE(test_sequential_read);
  `TEST_CASE(test_registered_output);
  `TEST_CASE(test_enable_hold);
  `TEST_SUITE_END();

endmodule

