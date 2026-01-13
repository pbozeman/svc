`include "svc_unit.sv"

`include "svc_rv_stage_ex.sv"

//
// Testbench for EX stage multi-cycle operation handling
//
// Tests the interaction between multi-cycle operations (div/rem) and the
// pipeline register valid signal in PIPELINED mode. Specifically verifies
// that m_valid is correctly asserted when a multi-cycle operation completes.
//
module svc_rv_stage_ex_mc_tb;
  `include "svc_rv_defs.svh"

  localparam int XLEN = 32;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  //
  // DUT signals
  //
  logic            ex_mem_flush;

  logic            reg_write_ex;
  logic            mem_read_ex;
  logic            mem_write_ex;
  logic [     1:0] alu_a_src_ex;
  logic            alu_b_src_ex;
  logic [     1:0] alu_instr_ex;
  logic [     2:0] res_src_ex;
  logic            is_branch_ex;
  logic            is_jmp_ex;
  logic            jb_tgt_src_ex;
  logic            is_jal_ex;
  logic            is_jalr_ex;
  logic            is_mc_ex;
  logic            is_m_ex;
  logic            is_csr_ex;
  logic            trap_ex;
  logic [     1:0] trap_code_ex;
  logic            is_ebreak_ex;
  logic [    31:0] instr_ex;
  logic [     4:0] rd_ex;
  logic [     4:0] rs1_ex;
  logic [     4:0] rs2_ex;
  logic [     2:0] funct3_ex;
  logic [     6:0] funct7_ex;
  logic [XLEN-1:0] rs1_data_ex;
  logic [XLEN-1:0] rs2_data_ex;
  logic [XLEN-1:0] imm_ex;
  logic [XLEN-1:0] pc_ex;
  logic [XLEN-1:0] pc_plus4_ex;
  logic            bpred_taken_ex;
  logic [XLEN-1:0] pred_tgt_ex;

  logic            s_valid;

  logic [XLEN-1:0] result_mem;
  logic [XLEN-1:0] ld_data_mem;

  logic            retired;

  // verilator lint_off UNUSEDSIGNAL
  logic [     1:0] pc_sel_ex_out;
  logic [XLEN-1:0] pc_redir_tgt_ex_out;
  logic            mispredicted_ex_out;
  // verilator lint_on UNUSEDSIGNAL

  // verilator lint_off UNUSEDSIGNAL
  logic            reg_write_mem;
  logic            mem_read_mem;
  logic            mem_write_mem;
  logic [     2:0] res_src_mem_out;
  logic [    31:0] instr_mem;
  logic [     4:0] rd_mem;
  logic [     4:0] rs2_mem;
  logic [     2:0] funct3_mem;
  logic [XLEN-1:0] alu_result_mem;
  logic [XLEN-1:0] rs1_data_mem;
  logic [XLEN-1:0] rs2_data_mem;
  logic [XLEN-1:0] pc_plus4_mem;
  logic [XLEN-1:0] jb_tgt_mem;
  logic [XLEN-1:0] csr_rdata_mem;
  logic [XLEN-1:0] m_result_mem;
  logic [XLEN-1:0] mul_ll_mem;
  logic [XLEN-1:0] mul_lh_mem;
  logic [XLEN-1:0] mul_hl_mem;
  logic [XLEN-1:0] mul_hh_mem;
  logic            is_branch_mem;
  logic            is_jalr_mem;
  logic            is_jmp_mem;
  logic            branch_taken_mem;
  logic            bpred_taken_mem;
  logic [XLEN-1:0] pred_tgt_mem;
  logic            trap_mem;
  logic [     1:0] trap_code_mem;
  logic            btb_update_en;
  logic [XLEN-1:0] btb_update_pc;
  logic [XLEN-1:0] btb_update_tgt;
  logic            btb_update_taken;
  logic            btb_update_is_ret;
  logic            btb_update_is_jal;
  logic            is_ebreak_mem;
  logic            m_valid;
  logic            instr_valid_mem;
  // verilator lint_on UNUSEDSIGNAL

  logic            stall_ex;
  logic            op_active_ex;

  //
  // DUT instantiation - pipelined EX stage with M extension
  //
  svc_rv_stage_ex #(
      .XLEN      (XLEN),
      .PIPELINED (1),
      .FWD       (1),
      .MEM_TYPE  (MEM_TYPE_SRAM),
      .BPRED     (0),
      .BTB_ENABLE(0),
      .EXT_ZMMUL (0),
      .EXT_M     (1)
  ) uut (
      .clk              (clk),
      .rst_n            (rst_n),
      .ex_mem_flush     (ex_mem_flush),
      .stall_ex         (stall_ex),
      .reg_write_ex     (reg_write_ex),
      .mem_read_ex      (mem_read_ex),
      .mem_write_ex     (mem_write_ex),
      .alu_a_src_ex     (alu_a_src_ex),
      .alu_b_src_ex     (alu_b_src_ex),
      .alu_instr_ex     (alu_instr_ex),
      .res_src_ex       (res_src_ex),
      .is_branch_ex     (is_branch_ex),
      .is_jmp_ex        (is_jmp_ex),
      .jb_tgt_src_ex    (jb_tgt_src_ex),
      .is_jal_ex        (is_jal_ex),
      .is_jalr_ex       (is_jalr_ex),
      .is_mc_ex         (is_mc_ex),
      .is_m_ex          (is_m_ex),
      .is_csr_ex        (is_csr_ex),
      .is_ebreak_ex     (is_ebreak_ex),
      .trap_ex          (trap_ex),
      .trap_code_ex     (trap_code_ex),
      .instr_ex         (instr_ex),
      .rd_ex            (rd_ex),
      .rs1_ex           (rs1_ex),
      .rs2_ex           (rs2_ex),
      .funct3_ex        (funct3_ex),
      .funct7_ex        (funct7_ex),
      .rs1_data_ex      (rs1_data_ex),
      .rs2_data_ex      (rs2_data_ex),
      .imm_ex           (imm_ex),
      .pc_ex            (pc_ex),
      .pc_plus4_ex      (pc_plus4_ex),
      .bpred_taken_ex   (bpred_taken_ex),
      .pred_tgt_ex      (pred_tgt_ex),
      .s_valid          (s_valid),
      .result_mem       (result_mem),
      .ld_data_mem      (ld_data_mem),
      .retired          (retired),
      .pc_sel_ex        (pc_sel_ex_out),
      .pc_redir_tgt_ex  (pc_redir_tgt_ex_out),
      .mispredicted_ex  (mispredicted_ex_out),
      .reg_write_mem    (reg_write_mem),
      .mem_read_mem     (mem_read_mem),
      .mem_write_mem    (mem_write_mem),
      .res_src_mem      (res_src_mem_out),
      .instr_mem        (instr_mem),
      .rd_mem           (rd_mem),
      .rs2_mem          (rs2_mem),
      .funct3_mem       (funct3_mem),
      .alu_result_mem   (alu_result_mem),
      .rs1_data_mem     (rs1_data_mem),
      .rs2_data_mem     (rs2_data_mem),
      .pc_plus4_mem     (pc_plus4_mem),
      .jb_tgt_mem       (jb_tgt_mem),
      .csr_rdata_mem    (csr_rdata_mem),
      .m_result_mem     (m_result_mem),
      .mul_ll_mem       (mul_ll_mem),
      .mul_lh_mem       (mul_lh_mem),
      .mul_hl_mem       (mul_hl_mem),
      .mul_hh_mem       (mul_hh_mem),
      .is_branch_mem    (is_branch_mem),
      .is_jalr_mem      (is_jalr_mem),
      .is_jmp_mem       (is_jmp_mem),
      .branch_taken_mem (branch_taken_mem),
      .bpred_taken_mem  (bpred_taken_mem),
      .pred_tgt_mem     (pred_tgt_mem),
      .trap_mem         (trap_mem),
      .trap_code_mem    (trap_code_mem),
      .is_ebreak_mem    (is_ebreak_mem),
      .m_valid          (m_valid),
      .instr_valid_mem  (instr_valid_mem),
      .op_active_ex     (op_active_ex),
      .btb_update_en    (btb_update_en),
      .btb_update_pc    (btb_update_pc),
      .btb_update_tgt   (btb_update_tgt),
      .btb_update_taken (btb_update_taken),
      .btb_update_is_ret(btb_update_is_ret),
      .btb_update_is_jal(btb_update_is_jal)
  );

  //
  // Helper task to initialize all inputs to idle state
  //
  task automatic init_inputs;
    ex_mem_flush   = 1'b0;
    reg_write_ex   = 1'b0;
    mem_read_ex    = 1'b0;
    mem_write_ex   = 1'b0;
    alu_a_src_ex   = 2'b00;
    alu_b_src_ex   = 1'b0;
    alu_instr_ex   = 2'b00;
    res_src_ex     = RES_ALU;
    is_branch_ex   = 1'b0;
    is_jmp_ex      = 1'b0;
    jb_tgt_src_ex  = 1'b0;
    is_jal_ex      = 1'b0;
    is_jalr_ex     = 1'b0;
    is_mc_ex       = 1'b0;
    is_m_ex        = 1'b0;
    is_csr_ex      = 1'b0;
    is_ebreak_ex   = 1'b0;
    trap_ex        = 1'b0;
    trap_code_ex   = TRAP_NONE;
    instr_ex       = I_NOP;
    rd_ex          = 5'd0;
    rs1_ex         = 5'd0;
    rs2_ex         = 5'd0;
    funct3_ex      = 3'b000;
    funct7_ex      = 7'b0000000;
    rs1_data_ex    = 32'd0;
    rs2_data_ex    = 32'd0;
    imm_ex         = 32'd0;
    pc_ex          = 32'd0;
    pc_plus4_ex    = 32'd4;
    bpred_taken_ex = 1'b0;
    pred_tgt_ex    = 32'd0;
    s_valid        = 1'b0;
    result_mem     = 32'd0;
    ld_data_mem    = 32'd0;
    retired        = 1'b0;
    stall_ex       = 1'b0;
  endtask

  //
  // Helper task to set up a DIV instruction
  //
  // DIV rd, rs1, rs2: funct7=0000001, funct3=100
  //
  task automatic setup_div(input logic [31:0] dividend,
                           input logic [31:0] divisor,
                           input logic [4:0] dest_reg);
    reg_write_ex = 1'b1;
    res_src_ex   = RES_M;
    is_mc_ex     = 1'b1;
    is_m_ex      = 1'b1;
    rd_ex        = dest_reg;
    funct3_ex    = 3'b100;
    funct7_ex    = 7'b0000001;
    rs1_data_ex  = dividend;
    rs2_data_ex  = divisor;
    s_valid      = 1'b1;
  endtask

  //
  // Test reset state
  //
  task automatic test_reset;
    init_inputs();
    `TICK(clk);

    `CHECK_EQ(m_valid, 1'b0);
    `CHECK_EQ(op_active_ex, 1'b0);
  endtask

  //
  // Test basic ALU operation passes through correctly
  //
  task automatic test_alu_passthrough;
    init_inputs();
    `TICK(clk);

    //
    // Present a simple ALU instruction
    //
    reg_write_ex = 1'b1;
    res_src_ex   = RES_ALU;
    rd_ex        = 5'd10;
    rs1_data_ex  = 32'd100;
    rs2_data_ex  = 32'd50;
    s_valid      = 1'b1;

    `TICK(clk);

    //
    // Should be valid on the next cycle
    //
    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(op_active_ex, 1'b0);
    `CHECK_EQ(reg_write_mem, 1'b1);
    `CHECK_EQ(rd_mem, 5'd10);
  endtask

  //
  // Test multi-cycle DIV operation
  //
  // This is the key test: verify that after a DIV completes, m_valid is
  // correctly asserted and the result is available.
  //
  // BUG SCENARIO (what we're testing for):
  // When a multi-cycle op starts, op_active_ex=1 causes ex_mem_flush=1
  // (from hazard unit). In the pipelined EX stage, this clears valid_reg to 0.
  // When the div completes, if valid_reg stays 0, m_valid will never assert.
  //
  task automatic test_div_completes_with_valid;
    int cycle_count;

    init_inputs();
    `TICK(clk);

    //
    // Start a DIV instruction: 9 / 7 = 1
    //
    setup_div(32'd9, 32'd7, 5'd19);

    //
    // On first cycle with ex_mem_flush (simulating hazard unit behavior),
    // the pipeline might incorrectly clear valid_reg
    //
    ex_mem_flush = 1'b1;
    `TICK(clk);

    //
    // Verify op_active_ex is asserted
    //
    `CHECK_EQ(op_active_ex, 1'b1);

    //
    // Clear flush and wait for division to complete
    //
    ex_mem_flush = 1'b0;
    s_valid      = 1'b0;
    is_mc_ex     = 1'b0;
    is_m_ex      = 1'b0;

    cycle_count  = 0;
    while (op_active_ex && cycle_count < 50) begin
      `TICK(clk);
      cycle_count++;
    end

    //
    // Division should complete within 35 cycles
    //
    `CHECK_TRUE(cycle_count < 40);

    //
    // KEY CHECK: After div completes, m_valid MUST be asserted
    // This is the bug we're testing for - if valid_reg was incorrectly
    // cleared by ex_mem_flush, m_valid will be 0
    //
    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(reg_write_mem, 1'b1);
    `CHECK_EQ(rd_mem, 5'd19);

    //
    // Verify the result is correct (9 / 7 = 1)
    //
    `CHECK_EQ(m_result_mem, 32'd1);
  endtask

  //
  // Test DIV result held during stall (stall_ex=1)
  //
  task automatic test_div_with_stall;
    int cycle_count;

    init_inputs();
    `TICK(clk);

    //
    // Start DIV (no stall yet)
    //
    setup_div(32'd20, 32'd4, 5'd15);

    ex_mem_flush = 1'b1;
    `TICK(clk);
    ex_mem_flush = 1'b0;

    s_valid      = 1'b0;
    is_mc_ex     = 1'b0;
    is_m_ex      = 1'b0;

    //
    // Wait for division to complete
    //
    cycle_count  = 0;
    while (op_active_ex && cycle_count < 50) begin
      `TICK(clk);
      cycle_count++;
    end

    //
    // m_valid should be asserted with result ready
    //
    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(m_result_mem, 32'd5);

    //
    // Now assert stall and verify m_valid stays high
    //
    stall_ex = 1'b1;
    `TICK(clk);
    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(m_result_mem, 32'd5);

    //
    // Release stall and verify pipeline can advance
    //
    stall_ex = 1'b0;
    `TICK(clk);

    //
    // op_active_ex should be low (ready to accept new instruction)
    //
    `CHECK_EQ(op_active_ex, 1'b0);
  endtask

  //
  // Test consecutive div operations
  //
  task automatic test_consecutive_divs;
    int cycle_count;

    init_inputs();
    `TICK(clk);

    //
    // First DIV: 100 / 10 = 10
    //
    setup_div(32'd100, 32'd10, 5'd1);
    ex_mem_flush = 1'b1;
    `TICK(clk);
    ex_mem_flush = 1'b0;
    s_valid      = 1'b0;
    is_mc_ex     = 1'b0;
    is_m_ex      = 1'b0;

    cycle_count  = 0;
    while (op_active_ex && cycle_count < 50) begin
      `TICK(clk);
      cycle_count++;
    end

    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(m_result_mem, 32'd10);

    //
    // Accept first result
    //
    `TICK(clk);

    //
    // Second DIV: 50 / 5 = 10
    //
    setup_div(32'd50, 32'd5, 5'd2);
    ex_mem_flush = 1'b1;
    `TICK(clk);
    ex_mem_flush = 1'b0;
    s_valid      = 1'b0;
    is_mc_ex     = 1'b0;
    is_m_ex      = 1'b0;

    cycle_count  = 0;
    while (op_active_ex && cycle_count < 50) begin
      `TICK(clk);
      cycle_count++;
    end

    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(m_result_mem, 32'd10);
    `CHECK_EQ(rd_mem, 5'd2);
  endtask

  //
  // Test divide by zero (should complete immediately)
  //
  task automatic test_div_by_zero;
    init_inputs();
    `TICK(clk);

    //
    // DIV by zero: 42 / 0 = -1 (0xFFFFFFFF)
    //
    setup_div(32'd42, 32'd0, 5'd5);
    ex_mem_flush = 1'b1;
    `TICK(clk);
    ex_mem_flush = 1'b0;
    s_valid      = 1'b0;
    is_mc_ex     = 1'b0;
    is_m_ex      = 1'b0;

    //
    // Divide by zero should complete after 1 cycle
    // (div unit takes 1 cycle to detect div-by-zero)
    //
    `TICK(clk);

    //
    // m_valid should now be asserted with the result
    //
    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(m_result_mem, 32'hFFFFFFFF);
  endtask

  //
  // Test div followed by dependent instruction
  //
  // Simulates: DIV x3, x1, x2 followed by ADDI x4, x3, 100
  // The ADDI depends on x3 (div result).
  //
  task automatic test_div_then_dependent_instr;
    int cycle_count;

    init_inputs();
    `TICK(clk);

    //
    // Start DIV: 20 / 4 = 5
    //
    setup_div(32'd20, 32'd4, 5'd3);
    ex_mem_flush = 1'b1;
    `TICK(clk);
    ex_mem_flush = 1'b0;
    s_valid      = 1'b0;
    is_mc_ex     = 1'b0;
    is_m_ex      = 1'b0;

    //
    // Wait for division to complete
    //
    cycle_count  = 0;
    while (op_active_ex && cycle_count < 50) begin
      `TICK(clk);
      cycle_count++;
    end

    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(m_result_mem, 32'd5);
    `CHECK_EQ(rd_mem, 5'd3);

    //
    // Now the next instruction (ADDI x4, x3, 100) should be able to enter
    // Present it as a simple ALU op (simulating that hazard is resolved)
    //
    reg_write_ex = 1'b1;
    res_src_ex   = RES_ALU;
    rd_ex        = 5'd4;
    s_valid      = 1'b1;

    `TICK(clk);

    //
    // The ALU instruction should now be valid
    //
    `CHECK_EQ(m_valid, 1'b1);
    `CHECK_EQ(rd_mem, 5'd4);
    `CHECK_EQ(op_active_ex, 1'b0);
  endtask

  `TEST_SUITE_BEGIN(svc_rv_stage_ex_mc_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_alu_passthrough);
  `TEST_CASE(test_div_completes_with_valid);
  `TEST_CASE(test_div_with_stall);
  `TEST_CASE(test_consecutive_divs);
  `TEST_CASE(test_div_by_zero);
  `TEST_CASE(test_div_then_dependent_instr);
  `TEST_SUITE_END();

endmodule
