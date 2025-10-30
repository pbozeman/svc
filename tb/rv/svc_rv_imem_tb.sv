`include "svc_unit.sv"

`include "svc_rv_imem.sv"

module svc_rv_imem_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int AW = 10;

  logic          en;
  logic [AW-1:0] addr;
  logic [  31:0] data;

  svc_rv_imem #(
      .AW(AW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),
      .en   (en),
      .addr (addr),
      .data (data)
  );

  // Default enable to 1 for all tests
  initial en = 1;

  task automatic test_reset;
    // Verify reset clears the output register
    uut.mem[0] = 32'hDEAD_BEEF;
    addr       = 0;
    `TICK(clk);
    `CHECK_EQ(data, 32'hDEAD_BEEF);

    // Assert reset
    rst_n = 0;
    `TICK(clk);
    `CHECK_EQ(data, 32'h0000_0000);

    // Deassert reset
    rst_n = 1;
    `TICK(clk);
    `CHECK_EQ(data, 32'hDEAD_BEEF);

    // Clean up - clear memory for next test
    uut.mem[0] = 32'h0000_0000;
  endtask

  task automatic test_initial_zero;
    // Memory should initialize to zero
    addr = 0;
    `TICK(clk);
    `CHECK_EQ(data, 32'h0000_0000);

    addr = 100;
    `TICK(clk);
    `CHECK_EQ(data, 32'h0000_0000);
  endtask

  task automatic test_write_read;
    // Write test patterns via hierarchical access
    uut.mem[0]    = 32'hDEAD_BEEF;
    uut.mem[1]    = 32'hCAFE_BABE;
    uut.mem[10]   = 32'h1234_5678;
    uut.mem[1023] = 32'hAAAA_AAAA;

    // Read back - should see data after one clock cycle
    addr          = 0;
    `TICK(clk);
    `CHECK_EQ(data, 32'hDEAD_BEEF);

    addr = 1;
    `TICK(clk);
    `CHECK_EQ(data, 32'hCAFE_BABE);

    addr = 10;
    `TICK(clk);
    `CHECK_EQ(data, 32'h1234_5678);

    addr = 1023;
    `TICK(clk);
    `CHECK_EQ(data, 32'hAAAA_AAAA);
  endtask

  task automatic test_sequential_read;
    int i;

    for (i = 0; i < 16; i++) begin
      uut.mem[i] = i * 4;
    end

    for (i = 0; i < 16; i++) begin
      addr = i[AW-1:0];
      `TICK(clk);
      `CHECK_EQ(data, i * 4);
    end
  endtask

  task automatic test_registered_output;
    uut.mem[5] = 32'h1111_1111;
    uut.mem[6] = 32'h2222_2222;

    addr       = 5;
    `CHECK_TRUE(data != 32'h1111_1111);

    `TICK(clk);
    `CHECK_EQ(data, 32'h1111_1111);

    addr = 6;
    `CHECK_EQ(data, 32'h1111_1111);

    `TICK(clk);
    `CHECK_EQ(data, 32'h2222_2222);
  endtask

  task automatic test_enable_hold;
    // Test that when enable is 0, data output holds its value
    uut.mem[10] = 32'hAAAA_AAAA;
    uut.mem[11] = 32'hBBBB_BBBB;

    en          = 1;
    addr        = 10;
    `TICK(clk);
    `CHECK_EQ(data, 32'hAAAA_AAAA);

    // Change address but disable enable - data should hold
    en   = 0;
    addr = 11;
    `TICK(clk);
    `CHECK_EQ(data, 32'hAAAA_AAAA);

    `TICK(clk);
    `CHECK_EQ(data, 32'hAAAA_AAAA);

    // Re-enable - should see new address
    en = 1;
    `TICK(clk);
    `CHECK_EQ(data, 32'hBBBB_BBBB);
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

