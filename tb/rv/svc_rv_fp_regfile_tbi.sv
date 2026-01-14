`include "svc_unit.sv"
`include "svc_rv_fp_regfile.sv"

module svc_rv_fp_regfile_tbi;
  parameter int XLEN = 32;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [     4:0] fp_rs1_addr;
  logic [XLEN-1:0] fp_rs1_data;

  logic [     4:0] fp_rs2_addr;
  logic [XLEN-1:0] fp_rs2_data;

  logic [     4:0] fp_rs3_addr;
  logic [XLEN-1:0] fp_rs3_data;

  logic            fp_rd_en;
  logic [     4:0] fp_rd_addr;
  logic [XLEN-1:0] fp_rd_data;

  //
  // DUT instantiation
  //
  svc_rv_fp_regfile #(
      .XLEN       (XLEN),
      .FWD_REGFILE(1)
  ) uut (
      .clk        (clk),
      .fp_rs1_addr(fp_rs1_addr),
      .fp_rs1_data(fp_rs1_data),
      .fp_rs2_addr(fp_rs2_addr),
      .fp_rs2_data(fp_rs2_data),
      .fp_rs3_addr(fp_rs3_addr),
      .fp_rs3_data(fp_rs3_data),
      .fp_rd_en   (fp_rd_en),
      .fp_rd_addr (fp_rd_addr),
      .fp_rd_data (fp_rd_data)
  );

  //
  // Initialize signals in reset
  //
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      fp_rs1_addr <= '0;
      fp_rs2_addr <= '0;
      fp_rs3_addr <= '0;
      fp_rd_en    <= '0;
      fp_rd_addr  <= '0;
      fp_rd_data  <= '0;
    end
  end

  //
  // Test: f0 is NOT hardwired (unlike x0)
  //
  task automatic test_f0_writable();
    fp_rd_en   = 1'b1;
    fp_rd_addr = 5'h0;
    fp_rd_data = 32'hDEADBEEF;
    `TICK(clk);
    fp_rd_en = 1'b0;
    `TICK(clk);

    fp_rs1_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(fp_rs1_data, 32'hDEADBEEF);

    fp_rs2_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(fp_rs2_data, 32'hDEADBEEF);

    fp_rs3_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(fp_rs3_data, 32'hDEADBEEF);
  endtask

  //
  // Test: Write and read back
  //
  task automatic test_write_read();
    for (int i = 0; i < 32; i++) begin
      fp_rd_en   = 1'b1;
      fp_rd_addr = 5'(i);
      fp_rd_data = 32'hA0000000 | i;
      `TICK(clk);
      fp_rd_en = 1'b0;
      `TICK(clk);

      fp_rs1_addr = 5'(i);
      `TICK(clk);
      `CHECK_EQ(fp_rs1_data, 32'hA0000000 | i);
    end
  endtask

  //
  // Test: Triple read ports
  //
  task automatic test_triple_read();
    fp_rd_en   = 1'b1;
    fp_rd_addr = 5'd5;
    fp_rd_data = 32'h12345678;
    `TICK(clk);
    fp_rd_addr = 5'd10;
    fp_rd_data = 32'h9ABCDEF0;
    `TICK(clk);
    fp_rd_addr = 5'd15;
    fp_rd_data = 32'hFEDCBA98;
    `TICK(clk);
    fp_rd_en = 1'b0;
    `TICK(clk);

    fp_rs1_addr = 5'd5;
    fp_rs2_addr = 5'd10;
    fp_rs3_addr = 5'd15;
    `TICK(clk);
    `CHECK_EQ(fp_rs1_data, 32'h12345678);
    `CHECK_EQ(fp_rs2_data, 32'h9ABCDEF0);
    `CHECK_EQ(fp_rs3_data, 32'hFEDCBA98);
  endtask

  //
  // Test: Read same register on all three ports
  //
  task automatic test_triple_read_same();
    fp_rd_en   = 1'b1;
    fp_rd_addr = 5'd20;
    fp_rd_data = 32'hCAFEBABE;
    `TICK(clk);
    fp_rd_en = 1'b0;
    `TICK(clk);

    fp_rs1_addr = 5'd20;
    fp_rs2_addr = 5'd20;
    fp_rs3_addr = 5'd20;
    `TICK(clk);
    `CHECK_EQ(fp_rs1_data, 32'hCAFEBABE);
    `CHECK_EQ(fp_rs2_data, 32'hCAFEBABE);
    `CHECK_EQ(fp_rs3_data, 32'hCAFEBABE);
  endtask

  //
  // Test: Write disabled
  //
  task automatic test_write_disabled();
    fp_rd_en   = 1'b1;
    fp_rd_addr = 5'd7;
    fp_rd_data = 32'h11111111;
    `TICK(clk);
    fp_rd_en = 1'b0;
    `TICK(clk);

    fp_rs1_addr = 5'd7;
    `TICK(clk);
    `CHECK_EQ(fp_rs1_data, 32'h11111111);

    fp_rd_en   = 1'b0;
    fp_rd_addr = 5'd7;
    fp_rd_data = 32'h22222222;
    `TICK(clk);
    `TICK(clk);

    fp_rs1_addr = 5'd7;
    `TICK(clk);
    `CHECK_EQ(fp_rs1_data, 32'h11111111);
  endtask

  //
  // Test: All registers independent
  //
  task automatic test_all_independent();
    for (int i = 0; i < 32; i++) begin
      fp_rd_en   = 1'b1;
      fp_rd_addr = 5'(i);
      fp_rd_data = 32'hB0000000 | (i << 16) | i;
      `TICK(clk);
    end
    fp_rd_en = 1'b0;
    `TICK(clk);

    for (int i = 0; i < 32; i++) begin
      fp_rs1_addr = 5'(i);
      `TICK(clk);
      `CHECK_EQ(fp_rs1_data, 32'hB0000000 | (i << 16) | i);
    end
  endtask

  //
  // Test: Internal forwarding (write and read same cycle)
  //
  task automatic test_forwarding();
    fp_rd_en    = 1'b1;
    fp_rd_addr  = 5'd25;
    fp_rd_data  = 32'hFACEFACE;
    fp_rs1_addr = 5'd25;
    fp_rs2_addr = 5'd25;
    fp_rs3_addr = 5'd25;

    // With FWD_REGFILE=1, read should see write data same cycle
    `TICK(clk);
    `CHECK_EQ(fp_rs1_data, 32'hFACEFACE);
    `CHECK_EQ(fp_rs2_data, 32'hFACEFACE);
    `CHECK_EQ(fp_rs3_data, 32'hFACEFACE);

    fp_rd_en = 1'b0;
    `TICK(clk);

    // Value should persist after write disabled
    `CHECK_EQ(fp_rs1_data, 32'hFACEFACE);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_fp_regfile_tbi);
  `TEST_CASE(test_f0_writable);
  `TEST_CASE(test_write_read);
  `TEST_CASE(test_triple_read);
  `TEST_CASE(test_triple_read_same);
  `TEST_CASE(test_write_disabled);
  `TEST_CASE(test_all_independent);
  `TEST_CASE(test_forwarding);
  `TEST_SUITE_END();

endmodule
