`include "svc_unit.sv"

`include "svc_rv_hazard.sv"

module svc_rv_hazard_tb;
  `TEST_CLK_NS(clk, 10);

  logic [4:0] rs1_id;
  logic [4:0] rs2_id;
  logic [4:0] rd_ex;
  logic       reg_write_ex;
  logic [4:0] rd_mem;
  logic       reg_write_mem;
  logic [4:0] rd_wb;
  logic       reg_write_wb;
  logic       pc_sel;
  logic       pc_stall;
  logic       if_id_stall;
  logic       if_id_flush;
  logic       id_ex_flush;

  svc_rv_hazard #(
      .REGFILE_FWD(1)
  ) uut (
      .rs1_id       (rs1_id),
      .rs2_id       (rs2_id),
      .rd_ex        (rd_ex),
      .reg_write_ex (reg_write_ex),
      .rd_mem       (rd_mem),
      .reg_write_mem(reg_write_mem),
      .rd_wb        (rd_wb),
      .reg_write_wb (reg_write_wb),
      .pc_sel       (pc_sel),
      .pc_stall     (pc_stall),
      .if_id_stall  (if_id_stall),
      .if_id_flush  (if_id_flush),
      .id_ex_flush  (id_ex_flush)
  );

  task automatic test_reset;
    rs1_id        = 5'd0;
    rs2_id        = 5'd0;
    rd_ex         = 5'd0;
    reg_write_ex  = 1'b0;
    rd_mem        = 5'd0;
    reg_write_mem = 1'b0;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b0;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_no_hazard;
    rs1_id        = 5'd1;
    rs2_id        = 5'd2;
    rd_ex         = 5'd3;
    reg_write_ex  = 1'b1;
    rd_mem        = 5'd4;
    reg_write_mem = 1'b1;
    rd_wb         = 5'd5;
    reg_write_wb  = 1'b1;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_ex_hazard_rs1;
    rs1_id        = 5'd10;
    rs2_id        = 5'd2;
    rd_ex         = 5'd10;
    reg_write_ex  = 1'b1;
    rd_mem        = 5'd0;
    reg_write_mem = 1'b0;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b0;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_ex_hazard_rs2;
    rs1_id        = 5'd1;
    rs2_id        = 5'd10;
    rd_ex         = 5'd10;
    reg_write_ex  = 1'b1;
    rd_mem        = 5'd0;
    reg_write_mem = 1'b0;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b0;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_mem_hazard_rs1;
    rs1_id        = 5'd10;
    rs2_id        = 5'd2;
    rd_ex         = 5'd0;
    reg_write_ex  = 1'b0;
    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b0;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_mem_hazard_rs2;
    rs1_id        = 5'd1;
    rs2_id        = 5'd10;
    rd_ex         = 5'd0;
    reg_write_ex  = 1'b0;
    rd_mem        = 5'd10;
    reg_write_mem = 1'b1;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b0;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b1);
    `CHECK_EQ(if_id_stall, 1'b1);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b1);
  endtask

  task automatic test_x0_no_hazard;
    rs1_id        = 5'd0;
    rs2_id        = 5'd0;
    rd_ex         = 5'd0;
    reg_write_ex  = 1'b1;
    rd_mem        = 5'd0;
    reg_write_mem = 1'b1;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b1;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_no_write_no_hazard;
    rs1_id        = 5'd10;
    rs2_id        = 5'd10;
    rd_ex         = 5'd10;
    reg_write_ex  = 1'b0;
    rd_mem        = 5'd10;
    reg_write_mem = 1'b0;
    rd_wb         = 5'd10;
    reg_write_wb  = 1'b0;
    pc_sel        = 1'b0;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b0);
    `CHECK_EQ(id_ex_flush, 1'b0);
  endtask

  task automatic test_control_hazard;
    rs1_id        = 5'd1;
    rs2_id        = 5'd2;
    rd_ex         = 5'd0;
    reg_write_ex  = 1'b0;
    rd_mem        = 5'd0;
    reg_write_mem = 1'b0;
    rd_wb         = 5'd0;
    reg_write_wb  = 1'b0;
    pc_sel        = 1'b1;

    `TICK(clk);
    `CHECK_EQ(pc_stall, 1'b0);
    `CHECK_EQ(if_id_stall, 1'b0);
    `CHECK_EQ(if_id_flush, 1'b1);
    `CHECK_EQ(id_ex_flush, 1'b1);
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
  `TEST_SUITE_END();

endmodule
