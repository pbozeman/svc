`include "svc_unit.sv"

`include "svc_rv_fwd_id.sv"

//
// ID stage forward unit testbench
//
module svc_rv_fwd_id_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam int XLEN = 32;

  logic [     4:0] rs1_id;
  logic [     4:0] rs2_id;
  logic [XLEN-1:0] rs1_data_id;
  logic [XLEN-1:0] rs2_data_id;
  logic [     4:0] rd_mem;
  logic            reg_write_mem;
  logic [     2:0] res_src_mem;
  logic [XLEN-1:0] result_mem;
  logic [XLEN-1:0] load_data_mem;
  logic [     4:0] rd_wb;
  logic            reg_write_wb;
  logic [XLEN-1:0] rd_data_wb;
  logic [XLEN-1:0] fwd_rs1_id;
  logic [XLEN-1:0] fwd_rs2_id;

  svc_rv_fwd_id #(
      .XLEN    (XLEN),
      .MEM_TYPE(0)
  ) uut (
      .clk          (clk),
      .rst_n        (rst_n),
      .rs1_id       (rs1_id),
      .rs2_id       (rs2_id),
      .rs1_data_id  (rs1_data_id),
      .rs2_data_id  (rs2_data_id),
      .rd_mem       (rd_mem),
      .reg_write_mem(reg_write_mem),
      .res_src_mem  (res_src_mem),
      .result_mem   (result_mem),
      .load_data_mem(load_data_mem),
      .rd_wb        (rd_wb),
      .reg_write_wb (reg_write_wb),
      .rd_data_wb   (rd_data_wb),
      .fwd_rs1_id   (fwd_rs1_id),
      .fwd_rs2_id   (fwd_rs2_id)
  );

  task automatic reset_inputs;
    rs1_id        = 5'd0;
    rs2_id        = 5'd0;
    rs1_data_id   = 32'h0;
    rs2_data_id   = 32'h0;
    rd_mem        = 5'd0;
    reg_write_mem = 1'b0;
    res_src_mem   = 3'd0;
    result_mem    = 32'h0;
    load_data_mem = 32'h0;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b0;
    rd_data_wb    = 32'h0;
  endtask

  //
  // Test: Basic reset
  //
  task automatic test_reset;
    reset_inputs();
    `TICK(clk);
    `CHECK_TRUE(1);
  endtask

  //
  // Test: No forwarding needed (no hazards)
  //
  task automatic test_no_forwarding;
    reset_inputs();
    rs1_id       = 5'd1;
    rs2_id       = 5'd2;
    rs1_data_id  = 32'hAAAAAAAA;
    rs2_data_id  = 32'hBBBBBBBB;

    rd_wb        = 5'd3;
    reg_write_wb = 1'b1;
    rd_data_wb   = 32'hCCCCCCCC;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_id, 32'hBBBBBBBB);
  endtask

  //
  // Test: WB→ID forwarding for rs1
  //
  task automatic test_wb_to_id_fwd_rs1;
    reset_inputs();
    rs1_id       = 5'd10;
    rs2_id       = 5'd2;
    rs1_data_id  = 32'hAAAAAAAA;
    rs2_data_id  = 32'hBBBBBBBB;

    rd_wb        = 5'd10;
    reg_write_wb = 1'b1;
    rd_data_wb   = 32'hDEADBEEF;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'hDEADBEEF);
    `CHECK_EQ(fwd_rs2_id, 32'hBBBBBBBB);
  endtask

  //
  // Test: WB→ID forwarding for rs2
  //
  task automatic test_wb_to_id_fwd_rs2;
    reset_inputs();
    rs1_id       = 5'd1;
    rs2_id       = 5'd10;
    rs1_data_id  = 32'hAAAAAAAA;
    rs2_data_id  = 32'hBBBBBBBB;

    rd_wb        = 5'd10;
    reg_write_wb = 1'b1;
    rd_data_wb   = 32'hFEEDBEEF;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_id, 32'hFEEDBEEF);
  endtask

  //
  // Test: WB→ID forwarding for both rs1 and rs2
  //
  task automatic test_wb_to_id_fwd_both;
    reset_inputs();
    rs1_id       = 5'd10;
    rs2_id       = 5'd10;
    rs1_data_id  = 32'hAAAAAAAA;
    rs2_data_id  = 32'hBBBBBBBB;

    rd_wb        = 5'd10;
    reg_write_wb = 1'b1;
    rd_data_wb   = 32'hCAFEBABE;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'hCAFEBABE);
    `CHECK_EQ(fwd_rs2_id, 32'hCAFEBABE);
  endtask

  //
  // Test: No forwarding to x0
  //
  task automatic test_no_fwd_to_x0;
    reset_inputs();
    rs1_id       = 5'd0;
    rs2_id       = 5'd0;
    rs1_data_id  = 32'h0;
    rs2_data_id  = 32'h0;

    rd_wb        = 5'd0;
    reg_write_wb = 1'b1;
    rd_data_wb   = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'h0);
    `CHECK_EQ(fwd_rs2_id, 32'h0);
  endtask

  //
  // Test: MEM→ID forwarding for rs1
  //
  task automatic test_mem_to_id_fwd_rs1;
    reset_inputs();
    rs1_id        = 5'd10;
    rs2_id        = 5'd2;
    rs1_data_id   = 32'hAAAAAAAA;
    rs2_data_id   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'h12345678);
    `CHECK_EQ(fwd_rs2_id, 32'hBBBBBBBB);
  endtask

  //
  // Test: MEM→ID forwarding for rs2
  //
  task automatic test_mem_to_id_fwd_rs2;
    reset_inputs();
    rs1_id        = 5'd1;
    rs2_id        = 5'd10;
    rs1_data_id   = 32'hAAAAAAAA;
    rs2_data_id   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'h87654321;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_id, 32'h87654321);
  endtask

  //
  // Test: MEM→ID forwarding for both rs1 and rs2
  //
  task automatic test_mem_to_id_fwd_both;
    reset_inputs();
    rs1_id        = 5'd10;
    rs2_id        = 5'd10;
    rs1_data_id   = 32'hAAAAAAAA;
    rs2_data_id   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'hABCDEF00;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'hABCDEF00);
    `CHECK_EQ(fwd_rs2_id, 32'hABCDEF00);
  endtask

  //
  // Test: MEM priority over WB
  //
  task automatic test_mem_priority_over_wb;
    reset_inputs();
    rs1_id        = 5'd10;
    rs2_id        = 5'd2;
    rs1_data_id   = 32'hAAAAAAAA;
    rs2_data_id   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'h11110000;

    rd_wb         = 5'd10;
    reg_write_wb  = 1'b1;
    rd_data_wb    = 32'h22220000;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'h11110000);
    `CHECK_EQ(fwd_rs2_id, 32'hBBBBBBBB);
  endtask

  //
  // Test: No forwarding from MEM if it's a CSR (data not ready)
  //
  task automatic test_no_fwd_from_csr;
    reset_inputs();
    rs1_id        = 5'd10;
    rs2_id        = 5'd2;
    rs1_data_id   = 32'hAAAAAAAA;
    rs2_data_id   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd4;
    result_mem    = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_id, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_id, 32'hBBBBBBBB);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_fwd_id_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_no_forwarding);
  `TEST_CASE(test_wb_to_id_fwd_rs1);
  `TEST_CASE(test_wb_to_id_fwd_rs2);
  `TEST_CASE(test_wb_to_id_fwd_both);
  `TEST_CASE(test_no_fwd_to_x0);
  `TEST_CASE(test_mem_to_id_fwd_rs1);
  `TEST_CASE(test_mem_to_id_fwd_rs2);
  `TEST_CASE(test_mem_to_id_fwd_both);
  `TEST_CASE(test_mem_priority_over_wb);
  `TEST_CASE(test_no_fwd_from_csr);
  `TEST_SUITE_END();

endmodule
