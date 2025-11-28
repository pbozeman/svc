`include "svc_unit.sv"
`include "svc_rv_regfile.sv"

module svc_rv_regfile_tb;
  parameter int XLEN = 32;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [     4:0] rs1_addr;
  logic [XLEN-1:0] rs1_data;

  logic [     4:0] rs2_addr;
  logic [XLEN-1:0] rs2_data;

  logic            rd_en;
  logic [     4:0] rd_addr;
  logic [XLEN-1:0] rd_data;

  //
  // DUT instantiation
  //
  svc_rv_regfile #(
      .XLEN       (XLEN),
      .FWD_REGFILE(1)
  ) uut (
      .clk     (clk),
      .rst_n   (rst_n),
      .rs1_addr(rs1_addr),
      .rs1_data(rs1_data),
      .rs2_addr(rs2_addr),
      .rs2_data(rs2_data),
      .rd_en   (rd_en),
      .rd_addr (rd_addr),
      .rd_data (rd_data)
  );

  //
  // Initialize signals in reset
  //
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      rs1_addr <= '0;
      rs2_addr <= '0;
      rd_en    <= '0;
      rd_addr  <= '0;
      rd_data  <= '0;
    end
  end

  //
  // Test: Reset state
  //
  task automatic test_reset();
    for (int i = 0; i < 32; i++) begin
      rs1_addr = 5'(i);
      `TICK(clk);
      `CHECK_EQ(rs1_data, 32'h0);
    end
  endtask

  //
  // Test: x0 hardwired to zero
  //
  task automatic test_x0_hardwired();
    rd_en   = 1'b1;
    rd_addr = 5'h0;
    rd_data = 32'hDEADBEEF;
    `TICK(clk);
    rd_en = 1'b0;
    `TICK(clk);

    rs1_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h0);

    rs2_addr = 5'h0;
    `TICK(clk);
    `CHECK_EQ(rs2_data, 32'h0);
  endtask

  //
  // Test: Write and read back
  //
  task automatic test_write_read();
    for (int i = 1; i < 32; i++) begin
      rd_en   = 1'b1;
      rd_addr = 5'(i);
      rd_data = 32'hA0000000 | i;
      `TICK(clk);
      rd_en = 1'b0;
      `TICK(clk);

      rs1_addr = 5'(i);
      `TICK(clk);
      `CHECK_EQ(rs1_data, 32'hA0000000 | i);
    end
  endtask

  //
  // Test: Dual read ports
  //
  task automatic test_dual_read();
    rd_en   = 1'b1;
    rd_addr = 5'd5;
    rd_data = 32'h12345678;
    `TICK(clk);
    rd_addr = 5'd10;
    rd_data = 32'h9ABCDEF0;
    `TICK(clk);
    rd_en = 1'b0;
    `TICK(clk);

    rs1_addr = 5'd5;
    rs2_addr = 5'd10;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h12345678);
    `CHECK_EQ(rs2_data, 32'h9ABCDEF0);

    rs1_addr = 5'd10;
    rs2_addr = 5'd5;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h9ABCDEF0);
    `CHECK_EQ(rs2_data, 32'h12345678);
  endtask

  //
  // Test: Read same register on both ports
  //
  task automatic test_dual_read_same();
    rd_en   = 1'b1;
    rd_addr = 5'd15;
    rd_data = 32'hCAFEBABE;
    `TICK(clk);
    rd_en = 1'b0;
    `TICK(clk);

    rs1_addr = 5'd15;
    rs2_addr = 5'd15;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'hCAFEBABE);
    `CHECK_EQ(rs2_data, 32'hCAFEBABE);
  endtask

  //
  // Test: Write disabled
  //
  task automatic test_write_disabled();
    rd_en   = 1'b1;
    rd_addr = 5'd7;
    rd_data = 32'h11111111;
    `TICK(clk);
    rd_en = 1'b0;
    `TICK(clk);

    rs1_addr = 5'd7;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h11111111);

    rd_en   = 1'b0;
    rd_addr = 5'd7;
    rd_data = 32'h22222222;
    `TICK(clk);
    `TICK(clk);

    rs1_addr = 5'd7;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h11111111);
  endtask

  //
  // Test: Overwrite existing value
  //
  task automatic test_overwrite();
    rd_en   = 1'b1;
    rd_addr = 5'd20;
    rd_data = 32'hAAAAAAAA;
    `TICK(clk);
    rd_data = 32'hBBBBBBBB;
    `TICK(clk);
    rd_en = 1'b0;
    `TICK(clk);

    rs1_addr = 5'd20;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'hBBBBBBBB);
  endtask

  //
  // Test: All registers independent
  //
  task automatic test_all_independent();
    for (int i = 1; i < 32; i++) begin
      rd_en   = 1'b1;
      rd_addr = 5'(i);
      rd_data = 32'hB0000000 | (i << 16) | i;
      `TICK(clk);
    end
    rd_en = 1'b0;
    `TICK(clk);

    for (int i = 1; i < 32; i++) begin
      rs1_addr = 5'(i);
      `TICK(clk);
      `CHECK_EQ(rs1_data, 32'hB0000000 | (i << 16) | i);
    end
  endtask

  //
  // Test: Combinational read (zero latency)
  //
  task automatic test_combinational_read();
    rd_en   = 1'b1;
    rd_addr = 5'd3;
    rd_data = 32'h33333333;
    `TICK(clk);
    rd_addr = 5'd4;
    rd_data = 32'h44444444;
    `TICK(clk);
    rd_en = 1'b0;
    `TICK(clk);

    rs1_addr = 5'd3;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h33333333);

    rs1_addr = 5'd4;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h44444444);

    rs1_addr = 5'd3;
    `TICK(clk);
    `CHECK_EQ(rs1_data, 32'h33333333);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_regfile_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_x0_hardwired);
  `TEST_CASE(test_write_read);
  `TEST_CASE(test_dual_read);
  `TEST_CASE(test_dual_read_same);
  `TEST_CASE(test_write_disabled);
  `TEST_CASE(test_overwrite);
  `TEST_CASE(test_all_independent);
  `TEST_CASE(test_combinational_read);
  `TEST_SUITE_END();

endmodule
