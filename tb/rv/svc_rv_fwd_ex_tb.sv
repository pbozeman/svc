`include "svc_unit.sv"

`include "svc_rv_fwd_ex.sv"

//
// Forward unit testbench
//
// Tests forwarding logic with MEM_TYPE=0 (SRAM)
// BRAM behavior (no load forwarding) is tested in integration tests:
// - svc_rv_soc_bram_fwd_tb
// - svc_rv_soc_bram_bpred_tb
//
module svc_rv_fwd_ex_tb;
  `TEST_CLK_NS(clk, 10);

  localparam int XLEN = 32;

  logic [     4:0] rs1_ex;
  logic [     4:0] rs2_ex;
  logic [XLEN-1:0] rs1_data_ex;
  logic [XLEN-1:0] rs2_data_ex;
  logic [     4:0] rd_mem;
  logic            reg_write_mem;
  logic [     2:0] res_src_mem;
  logic [XLEN-1:0] result_mem;
  logic [XLEN-1:0] load_data_mem;
  logic [XLEN-1:0] fwd_rs1_ex;
  logic [XLEN-1:0] fwd_rs2_ex;

  svc_rv_fwd_ex #(
      .XLEN    (XLEN),
      .FWD     (1),
      .MEM_TYPE(0)
  ) uut (
      .rs1_ex       (rs1_ex),
      .rs2_ex       (rs2_ex),
      .rs1_data_ex  (rs1_data_ex),
      .rs2_data_ex  (rs2_data_ex),
      .rd_mem       (rd_mem),
      .reg_write_mem(reg_write_mem),
      .res_src_mem  (res_src_mem),
      .result_mem   (result_mem),
      .load_data_mem(load_data_mem),
      .fwd_rs1_ex   (fwd_rs1_ex),
      .fwd_rs2_ex   (fwd_rs2_ex)
  );

  task automatic reset_inputs;
    rs1_ex        = 5'd0;
    rs2_ex        = 5'd0;
    rs1_data_ex   = 32'h0;
    rs2_data_ex   = 32'h0;
    rd_mem        = 5'd0;
    reg_write_mem = 1'b0;
    res_src_mem   = 3'd0;
    result_mem    = 32'h0;
    load_data_mem = 32'h0;
  endtask

  //
  // Test: No forwarding needed (no hazards)
  //
  task automatic test_no_forwarding;
    reset_inputs();
    rs1_ex        = 5'd1;
    rs2_ex        = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd3;
    reg_write_mem = 1'b1;
    result_mem    = 32'hCCCCCCCC;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: MEM→EX forwarding for rs1 (EX hazard)
  //
  task automatic test_mem_to_ex_fwd_rs1;
    reset_inputs();
    rs1_ex        = 5'd10;
    rs2_ex        = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'hFEEDBEEF;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'hFEEDBEEF);
    `CHECK_EQ(fwd_rs2_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: MEM→EX forwarding for rs2 (EX hazard)
  //
  task automatic test_mem_to_ex_fwd_rs2;
    reset_inputs();
    rs1_ex        = 5'd1;
    rs2_ex        = 5'd10;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'hDEADBEEF;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_ex, 32'hDEADBEEF);
  endtask

  //
  // Test: MEM→EX forwarding for both rs1 and rs2
  //
  task automatic test_mem_to_ex_fwd_both;
    reset_inputs();
    rs1_ex        = 5'd10;
    rs2_ex        = 5'd10;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'hCAFEBABE;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'hCAFEBABE);
    `CHECK_EQ(fwd_rs2_ex, 32'hCAFEBABE);
  endtask

  //
  // Test: Load forwarding for SRAM (data ready in MEM stage)
  //
  // This testbench uses MEM_TYPE=0 (SRAM), so load data can be forwarded
  // from MEM stage via load_data_mem signal
  //
  task automatic test_sram_load_fwd;
    reset_inputs();
    rs1_ex        = 5'd10;
    rs2_ex        = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd1;
    result_mem    = 32'h99990000;
    load_data_mem = 32'h12340000;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'h12340000);
    `CHECK_EQ(fwd_rs2_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: Load priority over ALU for SRAM
  //
  // When both load and ALU forwarding are possible, load takes priority
  //
  task automatic test_sram_load_priority;
    reset_inputs();
    rs1_ex        = 5'd10;
    rs2_ex        = 5'd2;
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd1;
    result_mem    = 32'h99990000;
    load_data_mem = 32'hFEEDBEEF;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'hFEEDBEEF);
    `CHECK_EQ(fwd_rs2_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: No forwarding from MEM if it's a CSR (data not ready)
  //
  task automatic test_no_fwd_from_csr;
    reset_inputs();
    rs1_ex        = 5'd10;
    rs2_ex        = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd4;
    result_mem    = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: No forwarding to x0 (even if write to x0 in MEM)
  //
  task automatic test_no_fwd_to_x0;
    reset_inputs();
    rs1_ex        = 5'd0;
    rs2_ex        = 5'd0;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex   = 32'h0;
    rs2_data_ex   = 32'h0;

    rd_mem        = 5'd0;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'h0);
    `CHECK_EQ(fwd_rs2_ex, 32'h0);
  endtask

  //
  // Test: No forwarding if register not used
  //
  task automatic test_no_fwd_if_not_used;
    reset_inputs();
    // rs1_ex/rs2_ex already set to 0 to indicate not used (from reset_inputs)
    rs1_data_ex   = 32'hAAAAAAAA;
    rs2_data_ex   = 32'hBBBBBBBB;

    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    res_src_mem   = 3'd0;
    result_mem    = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(fwd_rs1_ex, 32'hAAAAAAAA);
    `CHECK_EQ(fwd_rs2_ex, 32'hBBBBBBBB);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_fwd_ex_tb);
  `TEST_CASE(test_no_forwarding);
  `TEST_CASE(test_mem_to_ex_fwd_rs1);
  `TEST_CASE(test_mem_to_ex_fwd_rs2);
  `TEST_CASE(test_mem_to_ex_fwd_both);
  `TEST_CASE(test_sram_load_fwd);
  `TEST_CASE(test_sram_load_priority);
  `TEST_CASE(test_no_fwd_from_csr);
  `TEST_CASE(test_no_fwd_to_x0);
  `TEST_CASE(test_no_fwd_if_not_used);
  `TEST_SUITE_END();

endmodule
