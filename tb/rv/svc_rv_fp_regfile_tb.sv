`include "svc_unit.sv"
`include "svc_rv_fp_regfile.sv"

module svc_rv_fp_regfile_tb;
  parameter int XLEN = 32;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [     4:0] frs1_addr;
  logic [XLEN-1:0] frs1_data;

  logic [     4:0] frs2_addr;
  logic [XLEN-1:0] frs2_data;

  logic [     4:0] frs3_addr;
  logic [XLEN-1:0] frs3_data;

  logic            frd_en;
  logic [     4:0] frd_addr;
  logic [XLEN-1:0] frd_data;

  //
  // DUT instantiation
  //
  svc_rv_fp_regfile #(
      .XLEN       (XLEN),
      .FWD_REGFILE(1)
  ) uut (
      .clk      (clk),
      .frs1_addr(frs1_addr),
      .frs1_data(frs1_data),
      .frs2_addr(frs2_addr),
      .frs2_data(frs2_data),
      .frs3_addr(frs3_addr),
      .frs3_data(frs3_data),
      .frd_en   (frd_en),
      .frd_addr (frd_addr),
      .frd_data (frd_data)
  );

  //
  // Initialize signals in reset
  //
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      frs1_addr <= '0;
      frs2_addr <= '0;
      frs3_addr <= '0;
      frd_en    <= '0;
      frd_addr  <= '0;
      frd_data  <= '0;
    end
  end

  //
  // Test: f0 is NOT hardwired (unlike x0)
  //
  task automatic test_f0_writable();
    frd_en   = 1'b1;
    frd_addr = 5'h0;
    frd_data = 32'hDEADBEEF;
    `TICK(clk);
    frd_en = 1'b0;
    `TICK(clk);

    frs1_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(frs1_data, 32'hDEADBEEF);

    frs2_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(frs2_data, 32'hDEADBEEF);

    frs3_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(frs3_data, 32'hDEADBEEF);
  endtask

  //
  // Test: Write and read back
  //
  task automatic test_write_read();
    for (int i = 0; i < 32; i++) begin
      frd_en   = 1'b1;
      frd_addr = 5'(i);
      frd_data = 32'hA0000000 | i;
      `TICK(clk);
      frd_en = 1'b0;
      `TICK(clk);

      frs1_addr = 5'(i);
      `TICK(clk);
      `CHECK_EQ(frs1_data, 32'hA0000000 | i);
    end
  endtask

  //
  // Test: Triple read ports
  //
  task automatic test_triple_read();
    frd_en   = 1'b1;
    frd_addr = 5'd5;
    frd_data = 32'h12345678;
    `TICK(clk);
    frd_addr = 5'd10;
    frd_data = 32'h9ABCDEF0;
    `TICK(clk);
    frd_addr = 5'd15;
    frd_data = 32'hFEDCBA98;
    `TICK(clk);
    frd_en = 1'b0;
    `TICK(clk);

    frs1_addr = 5'd5;
    frs2_addr = 5'd10;
    frs3_addr = 5'd15;
    `TICK(clk);
    `CHECK_EQ(frs1_data, 32'h12345678);
    `CHECK_EQ(frs2_data, 32'h9ABCDEF0);
    `CHECK_EQ(frs3_data, 32'hFEDCBA98);
  endtask

  //
  // Test: Read same register on all three ports
  //
  task automatic test_triple_read_same();
    frd_en   = 1'b1;
    frd_addr = 5'd20;
    frd_data = 32'hCAFEBABE;
    `TICK(clk);
    frd_en = 1'b0;
    `TICK(clk);

    frs1_addr = 5'd20;
    frs2_addr = 5'd20;
    frs3_addr = 5'd20;
    `TICK(clk);
    `CHECK_EQ(frs1_data, 32'hCAFEBABE);
    `CHECK_EQ(frs2_data, 32'hCAFEBABE);
    `CHECK_EQ(frs3_data, 32'hCAFEBABE);
  endtask

  //
  // Test: Write disabled
  //
  task automatic test_write_disabled();
    frd_en   = 1'b1;
    frd_addr = 5'd7;
    frd_data = 32'h11111111;
    `TICK(clk);
    frd_en = 1'b0;
    `TICK(clk);

    frs1_addr = 5'd7;
    `TICK(clk);
    `CHECK_EQ(frs1_data, 32'h11111111);

    frd_en   = 1'b0;
    frd_addr = 5'd7;
    frd_data = 32'h22222222;
    `TICK(clk);
    `TICK(clk);

    frs1_addr = 5'd7;
    `TICK(clk);
    `CHECK_EQ(frs1_data, 32'h11111111);
  endtask

  //
  // Test: All registers independent
  //
  task automatic test_all_independent();
    for (int i = 0; i < 32; i++) begin
      frd_en   = 1'b1;
      frd_addr = 5'(i);
      frd_data = 32'hB0000000 | (i << 16) | i;
      `TICK(clk);
    end
    frd_en = 1'b0;
    `TICK(clk);

    for (int i = 0; i < 32; i++) begin
      frs1_addr = 5'(i);
      `TICK(clk);
      `CHECK_EQ(frs1_data, 32'hB0000000 | (i << 16) | i);
    end
  endtask

  //
  // Test: Internal forwarding (write and read same cycle)
  //
  task automatic test_forwarding();
    frd_en    = 1'b1;
    frd_addr  = 5'd25;
    frd_data  = 32'hFACEFACE;
    frs1_addr = 5'd25;
    frs2_addr = 5'd25;
    frs3_addr = 5'd25;

    // With FWD_REGFILE=1, read should see write data same cycle
    `TICK(clk);
    `CHECK_EQ(frs1_data, 32'hFACEFACE);
    `CHECK_EQ(frs2_data, 32'hFACEFACE);
    `CHECK_EQ(frs3_data, 32'hFACEFACE);

    frd_en = 1'b0;
    `TICK(clk);

    // Value should persist after write disabled
    `CHECK_EQ(frs1_data, 32'hFACEFACE);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_fp_regfile_tb);
  `TEST_CASE(test_f0_writable);
  `TEST_CASE(test_write_read);
  `TEST_CASE(test_triple_read);
  `TEST_CASE(test_triple_read_same);
  `TEST_CASE(test_write_disabled);
  `TEST_CASE(test_all_independent);
  `TEST_CASE(test_forwarding);
  `TEST_SUITE_END();

endmodule
