`include "svc_unit.sv"

`include "svc_rv_hazard.sv"

module svc_rv_hazard_tb;
  `include "svc_rv_defs.svh"

  `TEST_CLK_NS(clk, 10);

  logic [4:0] rs1_id;
  logic [4:0] rs2_id;
  logic       rs1_used_id;
  logic       rs2_used_id;
  logic [4:0] rd_ex;
  logic       reg_write_ex;
  logic       is_load_ex;
  logic       is_csr_ex;
  logic       is_m_ex;
  logic       op_active_ex;
  logic [4:0] rd_mem;
  logic       reg_write_mem;
  logic [2:0] res_src_mem;
  logic [4:0] rd_wb;
  logic       reg_write_wb;
  logic [1:0] pc_sel;
  logic       mispredicted_ex;
  logic       jalr_mispredicted_mem;
  logic       pc_stall;
  logic       if_id_stall;
  logic       if_id_flush;
  // verilator lint_off UNUSEDSIGNAL
  logic       id_ex_stall;
  logic       ex_mem_stall;
  logic       ex_mem_flush;
  logic       mem_wb_stall;
  // verilator lint_on UNUSEDSIGNAL
  logic       id_ex_flush;

  svc_rv_hazard #(
      .FWD_REGFILE(1),
      .FWD        (0),
      .MEM_TYPE   (0)
  ) uut (
      .rs1_id               (rs1_id),
      .rs2_id               (rs2_id),
      .rs1_used_id          (rs1_used_id),
      .rs2_used_id          (rs2_used_id),
      .rd_ex                (rd_ex),
      .reg_write_ex         (reg_write_ex),
      .is_load_ex           (is_load_ex),
      .is_csr_ex            (is_csr_ex),
      .is_m_ex              (is_m_ex),
      .op_active_ex         (op_active_ex),
      .rd_mem               (rd_mem),
      .reg_write_mem        (reg_write_mem),
      .mem_read_mem         (1'b0),
      .res_src_mem          (res_src_mem),
      .rd_wb                (rd_wb),
      .reg_write_wb         (reg_write_wb),
      .pc_sel               (pc_sel),
      .mispredicted_ex      (mispredicted_ex),
      .jalr_mispredicted_mem(jalr_mispredicted_mem),
      .btb_pred_taken       (1'b0),
      .ras_pred_taken       (1'b0),
      .pc_stall             (pc_stall),
      .if_id_stall          (if_id_stall),
      .if_id_flush          (if_id_flush),
      .id_ex_stall          (id_ex_stall),
      .id_ex_flush          (id_ex_flush),
      .ex_mem_stall         (ex_mem_stall),
      .ex_mem_flush         (ex_mem_flush),
      .mem_wb_stall         (mem_wb_stall)
  );

  task automatic test_reset;
    rs1_id                = 5'd0;
    rs2_id                = 5'd0;
    rs1_used_id           = 1'b0;
    rs2_used_id           = 1'b0;
    rd_ex                 = 5'd0;
    reg_write_ex          = 1'b0;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    is_m_ex               = 1'b0;
    op_active_ex          = 1'b0;
    rd_mem                = 5'd0;
    reg_write_mem         = 1'b0;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_no_hazard;
    rs1_id                = 5'd1;
    rs2_id                = 5'd2;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd3;
    reg_write_ex          = 1'b1;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    rd_mem                = 5'd4;
    reg_write_mem         = 1'b1;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd5;
    reg_write_wb          = 1'b1;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_ex_hazard_rs1;
    rs1_id                = 5'd10;
    rs2_id                = 5'd2;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd10;
    reg_write_ex          = 1'b1;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    op_active_ex          = 1'b0;
    rd_mem                = 5'd0;
    reg_write_mem         = 1'b0;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_ex_hazard_rs2;
    rs1_id                = 5'd1;
    rs2_id                = 5'd10;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd10;
    reg_write_ex          = 1'b1;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    op_active_ex          = 1'b0;
    rd_mem                = 5'd0;
    reg_write_mem         = 1'b0;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_mem_hazard_rs1;
    rs1_id                = 5'd10;
    rs2_id                = 5'd2;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd0;
    reg_write_ex          = 1'b0;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    rd_mem                = 5'd10;
    reg_write_mem         = 1'b1;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_mem_hazard_rs2;
    rs1_id                = 5'd1;
    rs2_id                = 5'd10;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd0;
    reg_write_ex          = 1'b0;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    rd_mem                = 5'd10;
    reg_write_mem         = 1'b1;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_x0_no_hazard;
    rs1_id                = 5'd0;
    rs2_id                = 5'd0;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd0;
    reg_write_ex          = 1'b1;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    rd_mem                = 5'd0;
    reg_write_mem         = 1'b1;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b1;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_no_write_no_hazard;
    rs1_id                = 5'd10;
    rs2_id                = 5'd10;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd10;
    reg_write_ex          = 1'b0;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    rd_mem                = 5'd10;
    reg_write_mem         = 1'b0;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd10;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_control_hazard;
    rs1_id          = 5'd1;
    rs2_id          = 5'd2;
    rs1_used_id     = 1'b1;
    rs2_used_id     = 1'b1;
    rd_ex           = 5'd0;
    reg_write_ex    = 1'b0;
    is_load_ex      = 1'b0;
    is_csr_ex       = 1'b0;
    is_m_ex         = 1'b0;
    op_active_ex    = 1'b0;
    rd_mem          = 5'd0;
    reg_write_mem   = 1'b0;
    res_src_mem     = 3'd0;
    rd_wb           = 5'd0;
    reg_write_wb    = 1'b0;
    pc_sel          = PC_SEL_REDIRECT;
    mispredicted_ex = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b1);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  //
  // Test that hazards are NOT detected when registers are not used
  //
  task automatic test_rs1_not_used_no_hazard;
    rs1_id                = 5'd10;
    rs2_id                = 5'd2;
    rs1_used_id           = 1'b0;
    rs2_used_id           = 1'b1;
    rd_ex                 = 5'd10;
    reg_write_ex          = 1'b1;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    op_active_ex          = 1'b0;
    rd_mem                = 5'd0;
    reg_write_mem         = 1'b0;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_rs2_not_used_no_hazard;
    rs1_id                = 5'd1;
    rs2_id                = 5'd10;
    rs1_used_id           = 1'b1;
    rs2_used_id           = 1'b0;
    rd_ex                 = 5'd10;
    reg_write_ex          = 1'b1;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    op_active_ex          = 1'b0;
    rd_mem                = 5'd0;
    reg_write_mem         = 1'b0;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_neither_used_no_hazard;
    rs1_id                = 5'd10;
    rs2_id                = 5'd10;
    rs1_used_id           = 1'b0;
    rs2_used_id           = 1'b0;
    rd_ex                 = 5'd10;
    reg_write_ex          = 1'b1;
    is_load_ex            = 1'b0;
    is_csr_ex             = 1'b0;
    rd_mem                = 5'd10;
    reg_write_mem         = 1'b1;
    res_src_mem           = 3'd0;
    rd_wb                 = 5'd0;
    reg_write_wb          = 1'b0;
    pc_sel                = PC_SEL_SEQUENTIAL;
    mispredicted_ex       = 1'b0;
    jalr_mispredicted_mem = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_hazard_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_no_hazard);
  `TEST_CASE(test_ex_hazard_rs1);
  `TEST_CASE(test_ex_hazard_rs2);
  `TEST_CASE(test_mem_hazard_rs1);
  `TEST_CASE(test_mem_hazard_rs2);
  `TEST_CASE(test_x0_no_hazard);
  `TEST_CASE(test_no_write_no_hazard);
  `TEST_CASE(test_control_hazard);
  `TEST_CASE(test_rs1_not_used_no_hazard);
  `TEST_CASE(test_rs2_not_used_no_hazard);
  `TEST_CASE(test_neither_used_no_hazard);
  `TEST_SUITE_END();

endmodule
