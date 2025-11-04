`include "svc_unit.sv"

`include "svc_rv_forward.sv"

module svc_rv_forward_tb;
  `TEST_CLK_NS(clk, 10);

  localparam int XLEN = 32;

  logic [     4:0] rs1_ex;
  logic [     4:0] rs2_ex;
  logic [XLEN-1:0] rs1_data_ex;
  logic [XLEN-1:0] rs2_data_ex;
  logic [     4:0] rd_mem;
  logic            reg_write_mem;
  logic            is_load_mem;
  logic            is_csr_mem;
  logic [XLEN-1:0] alu_result_mem;
  logic [     4:0] rd_wb;
  logic            reg_write_wb;
  logic [XLEN-1:0] rd_data;
  logic [XLEN-1:0] rs1_fwd_ex;
  logic [XLEN-1:0] rs2_fwd_ex;

  svc_rv_forward #(
      .XLEN(XLEN),
      .FWD (1)
  ) uut (
      .rs1_ex        (rs1_ex),
      .rs2_ex        (rs2_ex),
      .rs1_data_ex   (rs1_data_ex),
      .rs2_data_ex   (rs2_data_ex),
      .rd_mem        (rd_mem),
      .reg_write_mem (reg_write_mem),
      .is_load_mem   (is_load_mem),
      .is_csr_mem    (is_csr_mem),
      .alu_result_mem(alu_result_mem),
      .rd_wb         (rd_wb),
      .reg_write_wb  (reg_write_wb),
      .rd_data       (rd_data),
      .rs1_fwd_ex    (rs1_fwd_ex),
      .rs2_fwd_ex    (rs2_fwd_ex)
  );

  task automatic reset_inputs;
    rs1_ex         = 5'd0;
    rs2_ex         = 5'd0;
    // rs1_ex/rs2_ex already set to 0 to indicate not used
    rs1_data_ex    = 32'h0;
    rs2_data_ex    = 32'h0;
    rd_mem         = 5'd0;
    reg_write_mem  = 1'b0;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'h0;
    rd_wb          = 5'd0;
    reg_write_wb   = 1'b0;
    rd_data        = 32'h0;
  endtask

  //
  // Test: No forwarding needed (no hazards)
  //
  task automatic test_no_forwarding;
    reset_inputs();
    rs1_ex         = 5'd1;
    rs2_ex         = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd3;
    reg_write_mem  = 1'b1;
    alu_result_mem = 32'hCCCCCCCC;

    rd_wb          = 5'd4;
    reg_write_wb   = 1'b1;
    rd_data        = 32'hDDDDDDDD;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hAAAAAAAA);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: MEM→EX forwarding for rs1 (EX hazard)
  //
  task automatic test_mem_to_ex_fwd_rs1;
    reset_inputs();
    rs1_ex         = 5'd10;
    rs2_ex         = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd10;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'hFEEDBEEF;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hFEEDBEEF);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: MEM→EX forwarding for rs2 (EX hazard)
  //
  task automatic test_mem_to_ex_fwd_rs2;
    reset_inputs();
    rs1_ex         = 5'd1;
    rs2_ex         = 5'd10;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd10;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'hDEADBEEF;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hAAAAAAAA);
    `CHECK_EQ(rs2_fwd_ex, 32'hDEADBEEF);
  endtask

  //
  // Test: MEM→EX forwarding for both rs1 and rs2
  //
  task automatic test_mem_to_ex_fwd_both;
    reset_inputs();
    rs1_ex         = 5'd10;
    rs2_ex         = 5'd10;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd10;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'hCAFEBABE;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hCAFEBABE);
    `CHECK_EQ(rs2_fwd_ex, 32'hCAFEBABE);
  endtask

  //
  // Test: WB→EX forwarding for rs1 (MEM hazard)
  //
  task automatic test_wb_to_ex_fwd_rs1;
    reset_inputs();
    rs1_ex         = 5'd10;
    rs2_ex         = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd3;
    reg_write_mem  = 1'b0;
    alu_result_mem = 32'hCCCCCCCC;

    rd_wb          = 5'd10;
    reg_write_wb   = 1'b1;
    rd_data        = 32'h12345678;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'h12345678);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: WB→EX forwarding for rs2 (MEM hazard)
  //
  task automatic test_wb_to_ex_fwd_rs2;
    reset_inputs();
    rs1_ex         = 5'd1;
    rs2_ex         = 5'd10;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd3;
    reg_write_mem  = 1'b0;
    alu_result_mem = 32'hCCCCCCCC;

    rd_wb          = 5'd10;
    reg_write_wb   = 1'b1;
    rd_data        = 32'h87654321;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hAAAAAAAA);
    `CHECK_EQ(rs2_fwd_ex, 32'h87654321);
  endtask

  //
  // Test: Priority - MEM stage takes priority over WB stage
  //
  task automatic test_mem_priority_over_wb;
    reset_inputs();
    rs1_ex         = 5'd10;
    rs2_ex         = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd10;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'h11110000;

    rd_wb          = 5'd10;
    reg_write_wb   = 1'b1;
    rd_data        = 32'h22220000;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'h11110000);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: No forwarding from MEM if it's a load (data not ready)
  //
  task automatic test_no_fwd_from_load;
    reset_inputs();
    rs1_ex         = 5'd10;
    rs2_ex         = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd10;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b1;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'h99990000;

    rd_wb          = 5'd11;
    reg_write_wb   = 1'b0;
    rd_data        = 32'h0;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hAAAAAAAA);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: No forwarding from MEM if it's a CSR (data not ready)
  //
  task automatic test_no_fwd_from_csr;
    reset_inputs();
    rs1_ex         = 5'd10;
    rs2_ex         = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd10;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b1;
    alu_result_mem = 32'h99990000;

    rd_wb          = 5'd11;
    reg_write_wb   = 1'b0;
    rd_data        = 32'h0;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hAAAAAAAA);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: No forwarding to x0 (even if write to x0 in MEM/WB)
  //
  task automatic test_no_fwd_to_x0;
    reset_inputs();
    rs1_ex         = 5'd0;
    rs2_ex         = 5'd0;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'h0;
    rs2_data_ex    = 32'h0;

    rd_mem         = 5'd0;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'h99990000;

    rd_wb          = 5'd0;
    reg_write_wb   = 1'b1;
    rd_data        = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'h0);
    `CHECK_EQ(rs2_fwd_ex, 32'h0);
  endtask

  //
  // Test: No forwarding if register not used
  //
  task automatic test_no_fwd_if_not_used;
    reset_inputs();
    // rs1_ex/rs2_ex already set to 0 to indicate not used (from reset_inputs)
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd10;
    reg_write_mem  = 1'b1;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'h99990000;

    rd_wb          = 5'd10;
    reg_write_wb   = 1'b1;
    rd_data        = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'hAAAAAAAA);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  //
  // Test: Load-use case - WB forwards after stall
  //
  task automatic test_load_use_wb_forward;
    reset_inputs();
    rs1_ex         = 5'd10;
    rs2_ex         = 5'd2;
    // rs1_ex/rs2_ex non-zero indicates used
    rs1_data_ex    = 32'hAAAAAAAA;
    rs2_data_ex    = 32'hBBBBBBBB;

    rd_mem         = 5'd11;
    reg_write_mem  = 1'b0;
    is_load_mem    = 1'b0;
    is_csr_mem     = 1'b0;
    alu_result_mem = 32'hCCCCCCCC;

    rd_wb          = 5'd10;
    reg_write_wb   = 1'b1;
    rd_data        = 32'h99990000;

    `TICK(clk);

    `CHECK_EQ(rs1_fwd_ex, 32'h99990000);
    `CHECK_EQ(rs2_fwd_ex, 32'hBBBBBBBB);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_forward_tb);
  `TEST_CASE(test_no_forwarding);
  `TEST_CASE(test_mem_to_ex_fwd_rs1);
  `TEST_CASE(test_mem_to_ex_fwd_rs2);
  `TEST_CASE(test_mem_to_ex_fwd_both);
  `TEST_CASE(test_wb_to_ex_fwd_rs1);
  `TEST_CASE(test_wb_to_ex_fwd_rs2);
  `TEST_CASE(test_mem_priority_over_wb);
  `TEST_CASE(test_no_fwd_from_load);
  `TEST_CASE(test_no_fwd_from_csr);
  `TEST_CASE(test_no_fwd_to_x0);
  `TEST_CASE(test_no_fwd_if_not_used);
  `TEST_CASE(test_load_use_wb_forward);
  `TEST_SUITE_END();

endmodule
