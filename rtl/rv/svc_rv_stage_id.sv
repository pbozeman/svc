`ifndef SVC_RV_STAGE_ID_SV
`define SVC_RV_STAGE_ID_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_idec.sv"
`include "svc_rv_regfile.sv"
`include "svc_rv_fwd_id.sv"

//
// RISC-V Instruction Decode (ID) Stage
//
// Encapsulates all logic for the instruction decode pipeline stage:
// - Instruction decoder
// - Register file reads
// - Immediate value generation
// - Branch prediction logic
// - ID/EX pipeline register
//
// This stage decodes instructions, reads register operands, and prepares
// control signals for the execute stage.
//
module svc_rv_stage_id #(
    parameter int XLEN        = 32,
    parameter int PIPELINED   = 0,
    parameter int FWD_REGFILE = PIPELINED,
    parameter int BPRED       = 0,
    parameter int BTB_ENABLE  = 0,
    parameter int EXT_ZMMUL   = 0,
    parameter int EXT_M       = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic id_ex_stall,
    input logic id_ex_flush,

    //
    // From IF stage
    //
    input logic [    31:0] instr_id,
    input logic [    31:0] pc_id,
    input logic [    31:0] pc_plus4_id,
    input logic            btb_hit_id,
    input logic            btb_pred_taken_id,
    input logic [XLEN-1:0] btb_target_id,

    //
    // Write-back from WB stage
    //
    input logic        reg_write_wb,
    input logic [ 4:0] rd_wb,
    input logic [31:0] rd_data_wb,

    //
    // MEM stage forwarding inputs
    //
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic [     2:0] res_src_mem,
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] load_data_mem,

    //
    // Outputs to EX stage
    //
    output logic            reg_write_ex,
    output logic            mem_read_ex,
    output logic            mem_write_ex,
    output logic [     1:0] alu_a_src_ex,
    output logic            alu_b_src_ex,
    output logic [     1:0] alu_instr_ex,
    output logic [     2:0] res_src_ex,
    output logic            is_branch_ex,
    output logic            is_jump_ex,
    output logic            jb_target_src_ex,
    output logic            is_mc_ex,
    output logic [    31:0] instr_ex,
    output logic [     4:0] rd_ex,
    output logic [     4:0] rs1_ex,
    output logic [     4:0] rs2_ex,
    output logic [     2:0] funct3_ex,
    output logic [     6:0] funct7_ex,
    output logic [XLEN-1:0] rs1_data_ex,
    output logic [XLEN-1:0] rs2_data_ex,
    output logic [XLEN-1:0] imm_ex,
    output logic [XLEN-1:0] pc_ex,
    output logic [XLEN-1:0] pc_plus4_ex,
    output logic            bpred_taken_ex,

    //
    // Outputs to hazard unit (combinational from ID stage)
    //
    output logic [4:0] rs1_id,
    output logic [4:0] rs2_id,
    output logic       rs1_used_id,
    output logic       rs2_used_id,

    //
    // Branch prediction outputs to IF stage
    //
    output logic [     1:0] pc_sel_id,
    output logic [XLEN-1:0] pred_target,
    output logic            pred_taken_id,

    //
    // BTB prediction inputs
    //
    input logic            btb_hit,
    input logic [XLEN-1:0] btb_target,
    input logic            btb_taken
);

  `include "svc_rv_defs.svh"

  //
  // ID stage signals
  //
  logic            reg_write_id;
  logic            mem_read_id;
  logic            mem_write_id;
  logic [     1:0] alu_a_src_id;
  logic            alu_b_src_id;
  logic [     1:0] alu_instr_id;
  logic [     2:0] res_src_id;
  logic [     2:0] imm_type;
  logic            is_branch_id;
  logic            is_jump_id;
  logic            jb_target_src_id;
  logic            is_mc_id;
  logic [     4:0] rd_id;
  logic [     2:0] funct3_id;
  logic [     6:0] funct7_id;
  logic [XLEN-1:0] imm_i;
  logic [XLEN-1:0] imm_s;
  logic [XLEN-1:0] imm_b;
  logic [XLEN-1:0] imm_u;
  logic [XLEN-1:0] imm_j;
  logic [XLEN-1:0] imm_id;
  logic [XLEN-1:0] rs1_data_id;
  logic [XLEN-1:0] rs2_data_id;

  //
  // Instruction Decoder
  //
  svc_rv_idec #(
      .XLEN (XLEN),
      .EXT_M(EXT_ZMMUL | EXT_M)
  ) idec (
      .instr        (instr_id),
      .reg_write    (reg_write_id),
      .mem_read     (mem_read_id),
      .mem_write    (mem_write_id),
      .alu_a_src    (alu_a_src_id),
      .alu_b_src    (alu_b_src_id),
      .alu_instr    (alu_instr_id),
      .res_src      (res_src_id),
      .imm_type     (imm_type),
      .is_branch    (is_branch_id),
      .is_jump      (is_jump_id),
      .jb_target_src(jb_target_src_id),
      .is_m         (),
      .rd           (rd_id),
      .rs1          (rs1_id),
      .rs2          (rs2_id),
      .funct3       (funct3_id),
      .funct7       (funct7_id),
      .rs1_used     (rs1_used_id),
      .rs2_used     (rs2_used_id),
      .imm_i        (imm_i),
      .imm_s        (imm_s),
      .imm_b        (imm_b),
      .imm_u        (imm_u),
      .imm_j        (imm_j)
  );

  //
  // Immediate mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (5)
  ) mux_imm (
      .sel (imm_type),
      .data({imm_u, imm_j, imm_b, imm_s, imm_i}),
      .out (imm_id)
  );

  //
  // Multi-cycle operation detection
  //
  // Identifies operations that require multiple cycles to complete.
  // Currently: DIV/REM (funct3[2]=1) from M extension (not ZMMUL)
  //
  // M-extension detection: R-type instruction with funct7[0]=1
  //
  logic is_m_id;

  assign is_m_id  = (res_src_id == RES_M);
  assign is_mc_id = (EXT_M != 0) && is_m_id && funct3_id[2];

  //
  // Register File
  //
  svc_rv_regfile #(
      .XLEN       (XLEN),
      .FWD_REGFILE(FWD_REGFILE)
  ) regfile (
      .clk     (clk),
      .rst_n   (rst_n),
      .rs1_addr(rs1_id),
      .rs1_data(rs1_data_id),
      .rs2_addr(rs2_id),
      .rs2_data(rs2_data_id),
      .rd_en   (reg_write_wb),
      .rd_addr (rd_wb),
      .rd_data (rd_data_wb)
  );

  //
  // ID Stage Forwarding Unit
  //
  logic [XLEN-1:0] fwd_rs1_id;
  logic [XLEN-1:0] fwd_rs2_id;

  svc_rv_fwd_id #(
      .XLEN    (XLEN),
      .MEM_TYPE(0)
  ) fwd_id (
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

  //
  // Branch Prediction: BTB with static BTFNT fallback
  //
  if (BPRED != 0) begin : g_bpred
    if (BTB_ENABLE != 0) begin : g_btb_pred
      //
      // Hybrid prediction: BTB hit > Static BTFNT fallback
      //
      logic is_predictable;
      logic static_taken;

      //
      // Predictable: branches and PC-relative jumps (JAL), but not JALR
      //
      assign is_predictable = is_branch_id || (is_jump_id && !jb_target_src_id);

      //
      // Static BTFNT: backward branches taken, JAL taken
      //
      assign static_taken = ((is_branch_id && imm_id[XLEN-1]) ||
                             (is_jump_id && !jb_target_src_id));

      //
      // Three-tier prediction: BTB (IF) > Static BTFNT (ID) > No prediction
      //
      // This implements the standard predictor hierarchy:
      // 1. BTB hit in IF stage → immediate speculation (highest priority)
      // 2. BTB miss → Static BTFNT in ID stage (fallback)
      // 3. Not predictable → No prediction
      //
      // CRITICAL: Check btb_hit_id (buffered from IF) not btb_hit (current lookup)
      // to avoid double-prediction. When BTB already predicted this instruction
      // in IF stage, ID must NOT issue another redirect or it will flush the
      // wrong PC (the instruction after the target, not the target itself).
      //
      // For BRAM with 2-cycle latency (BRAM + IF/ID register), by the time
      // instruction reaches ID, IF has already moved to the target. ID's redirect
      // would flush that target instruction, skipping it - architectural bug!
      //
      always_comb begin
        if (btb_hit_id && is_predictable) begin
          // BTB already handled this in IF stage - ID must NOT redirect
          // Setting pred_taken_id=0 prevents pc_sel_id from issuing another redirect
          // BTB prediction is tracked separately via btb_pred_taken_id for misprediction detection
          pred_taken_id = 1'b0;
          pred_target   = '0;
        end else if (is_predictable) begin
          // BTB missed - use static BTFNT prediction
          pred_taken_id = static_taken;
          pred_target   = pc_id + imm_id;
        end else begin
          pred_taken_id = 1'b0;
          pred_target   = '0;
        end
      end

      //
      // Current BTB lookup signals unused - we use buffered signals from IF
      //
      `SVC_UNUSED({btb_hit, btb_target, btb_taken, btb_target_id});

    end else begin : g_static_pred
      //
      // Static BTFNT only (original logic)
      //
      assign pred_taken_id = ((is_branch_id && imm_id[XLEN-1]) ||
                              (is_jump_id && !jb_target_src_id));
      assign pred_target = pc_id + imm_id;

      `SVC_UNUSED({btb_hit, btb_target, btb_taken, btb_hit_id, btb_target_id});
    end

    //
    // PC selection output to IF stage
    //
    assign pc_sel_id = pred_taken_id ? PC_SEL_PREDICTED : PC_SEL_SEQUENTIAL;

  end else begin : g_no_bpred
    assign pred_taken_id = 1'b0;
    assign pred_target   = '0;
    assign pc_sel_id     = PC_SEL_SEQUENTIAL;

    `SVC_UNUSED({
                btb_hit,
                btb_target,
                btb_taken,
                btb_hit_id,
                btb_pred_taken_id,
                btb_target_id
                });
  end

  //
  // ID/EX Pipeline Register
  //
  if (PIPELINED != 0) begin : g_registered
    logic bpred_taken_id;

    if (BPRED != 0) begin : g_bpred_pipe
      //
      // Use BTB prediction from IF stage if BTB made a prediction,
      // otherwise use ID stage's static prediction
      //
      assign bpred_taken_id = btb_pred_taken_id ? 1'b1 : pred_taken_id;
    end else begin : g_no_bpred_pipe
      assign bpred_taken_id = 1'b0;
    end

    always_ff @(posedge clk) begin
      if (!rst_n || id_ex_flush) begin
        reg_write_ex     <= 1'b0;
        mem_read_ex      <= 1'b0;
        mem_write_ex     <= 1'b0;
        alu_a_src_ex     <= '0;
        alu_b_src_ex     <= 1'b0;
        alu_instr_ex     <= '0;
        res_src_ex       <= '0;
        is_branch_ex     <= 1'b0;
        is_jump_ex       <= 1'b0;
        jb_target_src_ex <= 1'b0;
        is_mc_ex         <= 1'b0;
        instr_ex         <= I_NOP;
        rd_ex            <= '0;
        rs1_ex           <= '0;
        rs2_ex           <= '0;
        funct3_ex        <= '0;
        funct7_ex        <= '0;
        rs1_data_ex      <= '0;
        rs2_data_ex      <= '0;
        imm_ex           <= '0;
        pc_ex            <= '0;
        pc_plus4_ex      <= '0;
        bpred_taken_ex   <= 1'b0;
      end else if (!id_ex_stall) begin
        reg_write_ex     <= reg_write_id;
        mem_read_ex      <= mem_read_id;
        mem_write_ex     <= mem_write_id;
        alu_a_src_ex     <= alu_a_src_id;
        alu_b_src_ex     <= alu_b_src_id;
        alu_instr_ex     <= alu_instr_id;
        res_src_ex       <= res_src_id;
        is_branch_ex     <= is_branch_id;
        is_jump_ex       <= is_jump_id;
        jb_target_src_ex <= jb_target_src_id;
        is_mc_ex         <= is_mc_id;
        instr_ex         <= instr_id;
        rd_ex            <= rd_id;
        rs1_ex           <= rs1_id;
        rs2_ex           <= rs2_id;
        funct3_ex        <= funct3_id;
        funct7_ex        <= funct7_id;
        rs1_data_ex      <= fwd_rs1_id;
        rs2_data_ex      <= fwd_rs2_id;
        imm_ex           <= imm_id;
        pc_ex            <= pc_id;
        pc_plus4_ex      <= pc_plus4_id;
        bpred_taken_ex   <= bpred_taken_id;
      end
    end

  end else begin : g_passthrough
    assign reg_write_ex     = reg_write_id;
    assign mem_read_ex      = mem_read_id;
    assign mem_write_ex     = mem_write_id;
    assign alu_a_src_ex     = alu_a_src_id;
    assign alu_b_src_ex     = alu_b_src_id;
    assign alu_instr_ex     = alu_instr_id;
    assign res_src_ex       = res_src_id;
    assign is_branch_ex     = is_branch_id;
    assign is_jump_ex       = is_jump_id;
    assign jb_target_src_ex = jb_target_src_id;
    assign is_mc_ex         = is_mc_id;
    assign instr_ex         = instr_id;
    assign rd_ex            = rd_id;
    assign rs1_ex           = rs1_id;
    assign rs2_ex           = rs2_id;
    assign funct3_ex        = funct3_id;
    assign funct7_ex        = funct7_id;
    assign rs1_data_ex      = rs1_data_id;
    assign rs2_data_ex      = rs2_data_id;
    assign imm_ex           = imm_id;
    assign pc_ex            = pc_id;
    assign pc_plus4_ex      = pc_plus4_id;
    assign bpred_taken_ex   = 1'b0;

    `SVC_UNUSED({id_ex_stall, id_ex_flush, fwd_rs1_id, fwd_rs2_id});
  end

endmodule

`endif
