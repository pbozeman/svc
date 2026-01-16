`ifndef SVC_RV_STAGE_EX_SV
`define SVC_RV_STAGE_EX_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_alu.sv"
`include "svc_rv_pipe_ctrl.sv"
`include "svc_rv_pipe_data.sv"
`include "svc_rv_alu_dec.sv"
`include "svc_rv_bcmp.sv"
`include "svc_rv_bpred_ex.sv"
`include "svc_rv_csr.sv"
`include "svc_rv_ext_mul_ex.sv"
`include "svc_rv_ext_div.sv"
`include "svc_rv_ext_fp_ex.sv"
`include "svc_rv_fp_csr.sv"
`include "svc_rv_fwd_ex.sv"

// Provide defaults for extension parameters (can be overridden via -D flags)
`ifndef EXT_F
`define EXT_F 0
`endif

//
// RISC-V Execute (EX) Stage
//
// Encapsulates all logic for the execute pipeline stage:
// - ALU operations
// - Branch comparison and target calculation
// - Jump target calculation
// - CSR operations
// - M extension (multiply/divide)
// - Data forwarding from MEM/WB stages
// - Multi-cycle operation control
// - EX/MEM pipeline register
//
// This stage performs arithmetic operations, branch decisions, and
// prepares results for the memory stage.
//
module svc_rv_stage_ex #(
    parameter int XLEN       = 32,
    parameter int PIPELINED  = 1,
    parameter int FWD        = 1,
    parameter int MEM_TYPE   = 0,
    parameter int BPRED      = 0,
    parameter int BTB_ENABLE = 0,
    parameter int EXT_ZMMUL  = 0,
    parameter int EXT_M      = 0,
    parameter int EXT_F      = `EXT_F
) (
    input logic clk,
    input logic rst_n,

    // Hazard control
    input logic ex_mem_flush,

    // Stall
    input logic stall_ex,

    // From ID stage
    input logic            instr_valid_ex,
    input logic            reg_write_ex,
    input logic            mem_read_ex,
    input logic            mem_write_ex,
    input logic [     1:0] alu_a_src_ex,
    input logic            alu_b_src_ex,
    input logic [     1:0] alu_instr_ex,
    input logic [     2:0] res_src_ex,
    input logic            is_branch_ex,
    input logic            is_jmp_ex,
    input logic            jb_tgt_src_ex,
    input logic            is_jal_ex,
    input logic            is_jalr_ex,
    input logic            is_mc_ex,
    input logic            is_m_ex,
    input logic            is_csr_ex,
    input logic            trap_ex,
    input logic [     1:0] trap_code_ex,
    input logic            is_ebreak_ex,
    input logic [    31:0] instr_ex,
    input logic [     4:0] rd_ex,
    input logic [     4:0] rs1_ex,
    input logic [     4:0] rs2_ex,
    input logic [     2:0] funct3_ex,
    input logic [     6:0] funct7_ex,
    input logic [XLEN-1:0] rs1_data_ex,
    input logic [XLEN-1:0] rs2_data_ex,
    input logic [XLEN-1:0] imm_ex,
    input logic [XLEN-1:0] pc_ex,
    input logic [XLEN-1:0] pc_plus4_ex,
    input logic            bpred_taken_ex,
    input logic [XLEN-1:0] pred_tgt_ex,

    // FP inputs from ID stage
    input logic            is_fp_ex,
    input logic            is_fp_load_ex,
    input logic            is_fp_store_ex,
    input logic            is_fp_compute_ex,
    input logic            is_fp_mc_ex,
    input logic            fp_reg_write_ex,
    input logic [XLEN-1:0] fp_rs1_data_ex,
    input logic [XLEN-1:0] fp_rs2_data_ex,
    input logic [XLEN-1:0] fp_rs3_data_ex,
    input logic [     4:0] fp_rs1_ex,
    input logic [     4:0] fp_rs2_ex,
    input logic [     4:0] fp_rs3_ex,
    input logic [     4:0] fp_rd_ex,
    input logic [     2:0] fp_rm_ex,
    input logic            fp_rm_dyn_ex,

    // Forwarding from MEM stage
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] ld_data_mem,

    // Instruction retirement (for CSR)
    input logic retired,

    // FP fflags accumulation (from WB stage)
    input logic [4:0] fflags_set,
    input logic       fflags_set_en,

    // PC control outputs to IF
    output logic [     1:0] pc_sel_ex,
    output logic [XLEN-1:0] pc_redir_tgt_ex,
    output logic            mispredicted_ex,

    // Outputs to MEM stage
    output logic            instr_valid_mem,
    output logic            reg_write_mem,
    output logic            mem_read_mem,
    output logic            mem_write_mem,
    output logic [     2:0] res_src_mem,
    output logic [    31:0] instr_mem,
    output logic [     4:0] rd_mem,
    output logic [     4:0] rs2_mem,
    output logic [     2:0] funct3_mem,
    output logic [XLEN-1:0] alu_result_mem,
    output logic [XLEN-1:0] rs1_data_mem,
    output logic [XLEN-1:0] rs2_data_mem,
    output logic [XLEN-1:0] pc_plus4_mem,
    output logic [XLEN-1:0] jb_tgt_mem,
    output logic [XLEN-1:0] csr_rdata_mem,
    output logic [XLEN-1:0] m_result_mem,
    output logic [XLEN-1:0] mul_ll_mem,
    output logic [XLEN-1:0] mul_lh_mem,
    output logic [XLEN-1:0] mul_hl_mem,
    output logic [XLEN-1:0] mul_hh_mem,
    output logic            is_branch_mem,
    output logic            is_jalr_mem,
    output logic            is_jmp_mem,
    output logic            branch_taken_mem,
    output logic            bpred_taken_mem,
    output logic [XLEN-1:0] pred_tgt_mem,
    output logic            trap_mem,
    output logic [     1:0] trap_code_mem,
    output logic            is_ebreak_mem,

    // FP outputs to MEM stage
    output logic            is_fp_load_mem,
    output logic            is_fp_store_mem,
    output logic            fp_reg_write_mem,
    output logic [     4:0] fp_rd_mem,
    output logic [XLEN-1:0] fp_result_mem,
    output logic [     4:0] fflags_mem,
    output logic [XLEN-1:0] fp_rs2_data_mem,

    // Outputs to hazard unit
    output logic op_active_ex,

    // BTB update interface
    output logic            btb_update_en,
    output logic [XLEN-1:0] btb_update_pc,
    output logic [XLEN-1:0] btb_update_tgt,
    output logic            btb_update_taken,
    output logic            btb_update_is_ret,
    output logic            btb_update_is_jal
);

  `include "svc_rv_defs.svh"

  //===========================================================================
  // FP instruction classification (for FPU interface timing)
  //===========================================================================

  logic is_fp_fmv;
  logic is_fp_mc;

  if (EXT_F != 0) begin : g_fp_classify
    logic [6:0] opcode;
    assign opcode = instr_ex[6:0];

    // FMV.X.W and FMV.W.X bypass the FPU and are effectively single-cycle.
    // All other FP compute ops (including FCLASS/FCVT/compare/arithmetic)
    // have latency due to fpnew PipeRegs.
    assign is_fp_fmv = (opcode == OP_FP) &&
        ((funct7_ex == FP7_FMVXW && funct3_ex == FP3_FMV) ||
         (funct7_ex == FP7_FMVWX && funct3_ex == FP3_FMV));

    // FPnew is configured with PipeRegs >= 1, so *all* FP compute ops have
    // latency (not just FDIV/FSQRT). Stall EX until fp_result_valid_ex.
    assign is_fp_mc = is_fp_compute_ex && !is_fp_fmv;
  end else begin : g_no_fp_classify
    assign is_fp_fmv = 1'b0;
    assign is_fp_mc  = 1'b0;
  end

  // EX stage internal signals
  logic [     3:0] alu_op_ex;
  logic [XLEN-1:0] alu_a_ex;
  logic [XLEN-1:0] alu_b_ex;
  logic [XLEN-1:0] alu_result_ex;
  logic [XLEN-1:0] jb_tgt_ex;

  // Multi-cycle operation control
  logic            op_en_ex;
  logic [XLEN-1:0] m_result_ex;
  logic            div_busy_ex;
  logic            m_busy_ex;

  // M extension partial products (for 2-stage multiply)
  logic [XLEN-1:0] mul_ll_ex;
  logic [XLEN-1:0] mul_lh_ex;
  logic [XLEN-1:0] mul_hl_ex;
  logic [XLEN-1:0] mul_hh_ex;

  // Branch signals
  logic            branch_taken_ex;

  // CSR signals
  logic [XLEN-1:0] int_csr_rdata;
  logic [XLEN-1:0] fp_csr_rdata;
  logic            fp_csr_valid;
  logic [XLEN-1:0] csr_rdata_ex;

  // FP signals
  logic [XLEN-1:0] fp_result_ex;
  logic [     4:0] fflags_ex;
  logic            fp_busy_ex;
  logic            fp_result_valid_ex;
  logic [     2:0] frm_csr;

  //===========================================================================
  // EX statemachine for single and multi-cycle ops
  //===========================================================================

  typedef enum logic [1:0] {
    EX_IDLE,
    EX_MC_EXEC,
    EX_MC_DONE
  } ex_state_t;

  ex_state_t state;
  ex_state_t state_next;

  // One-cycle issue pulse for fpnew-backed FP compute ops.
  // (FMV.* bypasses fpnew and uses instr_valid_ex directly.)
  logic      fp_issue;
  assign fp_issue = (is_fp_mc && instr_valid_ex && !stall_ex &&
                     ((state == EX_IDLE) || (state == EX_MC_DONE)));

  //
  // Result valid - indicates EX stage has a valid result to output
  //
  // For single-cycle ops: valid when input is valid
  // For multi-cycle ops: valid when operation completes (EX_MC_DONE)
  //
  logic result_valid;

  logic op_done;
  always_comb begin
    // For FP ops, completion is indicated by fp_result_valid_ex (valid/ready).
    // For integer multi-cycle ops (DIV/REM), completion is when busy deasserts.
    if (is_fp_mc) begin
      op_done = fp_result_valid_ex;
    end else begin
      op_done = !m_busy_ex;
    end
  end

  always_comb begin
    state_next   = state;
    result_valid = 1'b0;

    op_active_ex = 1'b0;
    op_en_ex     = 1'b0;

    case (state)
      EX_IDLE: begin
        if (instr_valid_ex) begin
          if (!(is_mc_ex || is_fp_mc)) begin
            result_valid = 1'b1;
          end else begin
            state_next   = EX_MC_EXEC;
            op_en_ex     = 1'b1;
            op_active_ex = 1'b1;
          end
        end
      end

      EX_MC_EXEC: begin
        op_active_ex = 1'b1;

        if (op_done) begin
          op_active_ex = 1'b0;
          state_next   = EX_MC_DONE;
          result_valid = 1'b1;
        end
      end

      EX_MC_DONE: begin
        if (!stall_ex) begin
          if (instr_valid_ex && (is_mc_ex || is_fp_mc)) begin
            state_next   = EX_MC_EXEC;
            op_en_ex     = 1'b1;
            op_active_ex = 1'b1;
          end else begin
            result_valid = instr_valid_ex;
            state_next   = EX_IDLE;
          end
        end
      end

      default: begin
        state_next   = EX_IDLE;
        result_valid = 1'b0;
      end
    endcase
  end

  //
  // State register
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state <= EX_IDLE;
    end else if (!stall_ex) begin
      //
      // Only advance state when not stalled. This ensures division results
      // are not lost if stall_ex is asserted when division completes.
      //
      state <= state_next;
    end
  end


  //===========================================================================
  // ALU
  //===========================================================================

  // ALU Decoder
  svc_rv_alu_dec alu_dec (
      .alu_instr(alu_instr_ex),
      .funct3   (funct3_ex),
      .funct7_b5(funct7_ex[5]),
      .op_b5    (instr_ex[5]),
      .alu_op   (alu_op_ex)
  );

  // Data forwarding unit
  logic [XLEN-1:0] fwd_rs1_ex;
  logic [XLEN-1:0] fwd_rs2_ex;

  svc_rv_fwd_ex #(
      .XLEN    (XLEN),
      .FWD     ((PIPELINED != 0 && FWD != 0) ? 1 : 0),
      .MEM_TYPE(MEM_TYPE)
  ) forward (
      .*
  );

  // ALU A input mux
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (3)
  ) mux_alu_a (
      .sel (alu_a_src_ex),
      .data({pc_ex, {XLEN{1'b0}}, fwd_rs1_ex}),
      .out (alu_a_ex)
  );

  // ALU B input mux
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_alu_b (
      .sel (alu_b_src_ex),
      .data({imm_ex, fwd_rs2_ex}),
      .out (alu_b_ex)
  );

  // ALU
  svc_rv_alu #(
      .XLEN(XLEN)
  ) alu (
      .a     (alu_a_ex),
      .b     (alu_b_ex),
      .alu_op(alu_op_ex),
      .result(alu_result_ex)
  );

  //===========================================================================
  // M Extension Units
  //===========================================================================

  // Multiply and division are split into separate units:
  // - Multiply: combinational 16-bit partial products (EX stage)
  // - Division: sequential 32-cycle operation (multi-cycle)
  //
  // ZMMUL: multiply only
  // M:     multiply + division
  if (EXT_ZMMUL != 0 || EXT_M != 0) begin : g_m_ext

    // Produces 16-bit partial products that are combined in MEM stage.
    svc_rv_ext_mul_ex ext_mul (
        .rs1   (fwd_rs1_ex),
        .rs2   (fwd_rs2_ex),
        .op    (funct3_ex),
        .mul_ll(mul_ll_ex),
        .mul_lh(mul_lh_ex),
        .mul_hl(mul_hl_ex),
        .mul_hh(mul_hh_ex)
    );

    if (EXT_M != 0) begin : g_div
      logic div_en;
      logic div_busy;

      assign div_en = op_en_ex && is_m_ex && funct3_ex[2];

      svc_rv_ext_div ext_div (
          .clk   (clk),
          .rst_n (rst_n),
          .en    (div_en),
          .rs1   (fwd_rs1_ex),
          .rs2   (fwd_rs2_ex),
          .op    (funct3_ex),
          .busy  (div_busy),
          .result(m_result_ex)
      );

      assign div_busy_ex = div_busy;

    end else begin : g_no_div
      // ZMMUL: no division unit
      assign m_result_ex = '0;
      assign div_busy_ex = 1'b0;

      `SVC_UNUSED({op_en_ex, op_active_ex});
    end

  end else begin : g_no_m_ext
    // No M extension
    assign m_result_ex = '0;
    assign div_busy_ex = 1'b0;
    assign mul_ll_ex   = '0;
    assign mul_lh_ex   = '0;
    assign mul_hl_ex   = '0;
    assign mul_hh_ex   = '0;

    `SVC_UNUSED({op_en_ex, op_active_ex});
  end

  //===========================================================================
  // F Extension Unit
  //===========================================================================

  // FP forwarded operand wires (declared outside generate for visibility)
  logic [XLEN-1:0] fwd_fp_rs1_ex;
  logic [XLEN-1:0] fwd_fp_rs2_ex;
  logic [XLEN-1:0] fwd_fp_rs3_ex;

  if (EXT_F != 0) begin : g_fp_ext
    // No FP forwarding - pass through regfile values directly
    // (FP hazard unit stalls until values are in regfile)
    assign fwd_fp_rs1_ex = fp_rs1_data_ex;
    assign fwd_fp_rs2_ex = fp_rs2_data_ex;
    assign fwd_fp_rs3_ex = fp_rs3_data_ex;

    svc_rv_ext_fp_ex fpu (
        .clk(clk),
        .rst_n(rst_n),
        .op_valid((instr_valid_ex && is_fp_compute_ex && is_fp_fmv) ||
                  fp_issue),
        .instr(instr_ex),
        .fp_rm(fp_rm_ex),
        .fp_rm_dyn(fp_rm_dyn_ex),
        .frm_csr(frm_csr),
        .fp_rs1(fwd_fp_rs1_ex),
        .fp_rs2(fwd_fp_rs2_ex),
        .fp_rs3(fwd_fp_rs3_ex),
        .rs1(fwd_rs1_ex),  // Integer source for FCVT.S.W/FMV.W.X
        .result_valid(fp_result_valid_ex),
        .result(fp_result_ex),
        .fflags(fflags_ex),
        .busy(fp_busy_ex)
    );

    // FP CSR module for frm and fflags
    svc_rv_fp_csr fp_csr (
        .clk          (clk),
        .rst_n        (rst_n),
        .csr_addr     (imm_ex[11:0]),
        .csr_op       (funct3_ex),
        .csr_wdata    (fwd_rs1_ex),
        .csr_en       (is_csr_ex),
        .csr_rdata    (fp_csr_rdata),
        .csr_valid    (fp_csr_valid),
        .frm          (frm_csr),
        .fflags_set   (fflags_set),
        .fflags_set_en(fflags_set_en)
    );

  end else begin : g_no_fp_ext
    assign fp_result_ex       = '0;
    assign fflags_ex          = '0;
    assign fp_busy_ex         = 1'b0;
    assign fp_result_valid_ex = 1'b0;
    assign fwd_fp_rs1_ex      = '0;
    assign fwd_fp_rs2_ex      = '0;
    assign fwd_fp_rs3_ex      = '0;
    assign fp_csr_rdata       = '0;
    assign fp_csr_valid       = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({
                is_fp_ex,
                is_fp_load_ex,
                is_fp_store_ex,
                is_fp_compute_ex,
                is_fp_mc_ex,
                fp_reg_write_ex,
                fp_rs1_data_ex,
                fp_rs2_data_ex,
                fp_rs3_data_ex,
                fp_rs1_ex,
                fp_rs2_ex,
                fp_rs3_ex,
                fp_rd_ex,
                fp_rm_ex,
                fp_rm_dyn_ex,
                fwd_fp_rs1_ex,
                fwd_fp_rs2_ex,
                fwd_fp_rs3_ex,
                fflags_set,
                fflags_set_en,
                is_csr_ex,
                is_fp_fmv,
                fp_issue
                });
    // verilog_format: on
  end

  // frm_csr only used in g_fp_ext, unused in g_no_fp_ext
  if (EXT_F == 0) begin : g_no_fp_frm
    assign frm_csr = '0;
    `SVC_UNUSED(frm_csr);
  end

  // Combined multi-cycle busy signal (division + FP FDIV/FSQRT)
  assign m_busy_ex = div_busy_ex || fp_busy_ex;

  // FP result valid is handled by EX state machine (is_fp_mc).

  //===========================================================================
  // Jump/Branch target calculation
  //===========================================================================

  // Two target address calculation modes:
  //
  // 1. PC-relative (JAL and all branches):
  //    target = PC + offset
  //    Used by: JAL, BEQ, BNE, BLT, BGE, BLTU, BGEU
  //
  // 2. Register-indirect (JALR only):
  //    target = (rs1 + offset) & ~1
  //    The ALU computes rs1+offset, then LSB is cleared per RISC-V spec.
  //    This ensures all jump targets are aligned to even addresses
  logic [XLEN-1:0] jb_tgt_jalr;
  logic [XLEN-1:0] jb_tgt_pc_rel;

  // JALR target: ALU result with LSB cleared
  assign jb_tgt_jalr   = {alu_result_ex[XLEN-1:1], 1'b0};

  // PC-relative target: Dedicated adder for JAL and branches
  assign jb_tgt_pc_rel = pc_ex + imm_ex;

  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_jb_tgt (
      .sel (jb_tgt_src_ex),
      .data({jb_tgt_jalr, jb_tgt_pc_rel}),
      .out (jb_tgt_ex)
  );

  //===========================================================================
  // Trap detection
  //===========================================================================

  logic misalign_trap;
  logic jb_active;

  assign jb_active = (is_branch_ex & branch_taken_ex) | is_jal_ex | is_jalr_ex;
  assign misalign_trap = jb_active & (|jb_tgt_ex[1:0]);

  //===========================================================================
  // Branch comparison
  //===========================================================================

  svc_rv_bcmp #(
      .XLEN(XLEN)
  ) bcmp (
      .a_ex           (fwd_rs1_ex),
      .b_ex           (fwd_rs2_ex),
      .funct3         (funct3_ex),
      .branch_taken_ex(branch_taken_ex)
  );

  //===========================================================================
  // Branch prediction and misprediction detection
  //===========================================================================

  svc_rv_bpred_ex #(
      .XLEN      (XLEN),
      .BPRED     (BPRED),
      .BTB_ENABLE(BTB_ENABLE)
  ) bpred (
      .en(instr_valid_ex && !op_active_ex),
      .*
  );

  //===========================================================================
  // PC redirect target calculation
  //===========================================================================

  // On misprediction, redirect to:
  // - pc + 4 if predicted taken but actually not-taken
  // - jb_tgt if predicted not-taken but actually taken
  // On actual taken branch/jump: jb_tgt
  //
  if (BPRED != 0) begin : g_pc_redir
    logic mispred_not_taken;

    assign mispred_not_taken = mispredicted_ex && !branch_taken_ex;

    always_comb begin
      pc_redir_tgt_ex = jb_tgt_ex;
      if (mispred_not_taken) begin
        pc_redir_tgt_ex = pc_ex + 4;
      end
    end
  end else begin : g_no_pc_redir
    assign pc_redir_tgt_ex = jb_tgt_ex;
  end

  //===========================================================================
  // PC selection
  //===========================================================================

  // Determines which PC source to use based on control flow and prediction:
  // - PC_SEL_REDIRECT: Actual taken branches/jumps or mispredictions
  // - PC_SEL_PREDICTED: Handled by ID stage (never set here)
  // - PC_SEL_SEQUENTIAL: Normal execution (default)
  //
  // When BPRED is enabled:
  //   - JAL is handled by predictor in ID stage, so don't redirect in EX
  //   - JALR misprediction handled in MEM stage (moved for timing)
  //   - Branches handled by predictor, only redirect on misprediction
  //   - Mispredictions trigger recovery
  //
  // Without BPRED:
  //   - Taken branches and all jumps (JAL/JALR) redirect in EX
  //
  logic pc_sel_branch_or_jump;

  if (BPRED != 0) begin : g_bpred_ex_redir
    // With prediction: only redirect on UNPREDICTED JALR
    // - Predicted JALR: Wait for MEM stage misprediction check (timing opt)
    // - Unpredicted JALR: Redirect immediately in EX (avoid wrong-path execution)
    // - Branches: Never redirect in EX (handled by misprediction logic)
    // - JAL: Predicted in ID stage, never reaches here
    assign pc_sel_branch_or_jump = is_jalr_ex && !bpred_taken_ex;
  end else begin : g_no_bpred_redir
    // Without prediction: taken branches and all jumps redirect in EX
    assign pc_sel_branch_or_jump = ((is_branch_ex & branch_taken_ex) ||
                                    is_jal_ex || is_jalr_ex);
  end

  // Calculate PC selection mode
  //
  // Only signal redirect when EX is actually accepting the instruction.
  // When stalled, the instruction at ID's output hasn't been captured yet,
  // so the redirect decision must be deferred to avoid flushing the
  // instruction before EX can accept it.
  //
  always_comb begin
    if ((pc_sel_branch_or_jump || mispredicted_ex) &&
        (instr_valid_ex && !stall_ex)) begin
      pc_sel_ex = PC_SEL_REDIRECT;
    end else begin
      pc_sel_ex = PC_SEL_SEQUENTIAL;
    end
  end


  //===========================================================================
  // CSR - Zicntr
  //===========================================================================

  svc_rv_csr csr (
      .clk        (clk),
      .rst_n      (rst_n),
      .csr_addr   (imm_ex[11:0]),
      .csr_rdata  (int_csr_rdata),
      .instret_inc(retired)
  );

  // Mux FP CSR rdata with main CSR rdata
  assign csr_rdata_ex = fp_csr_valid ? fp_csr_rdata : int_csr_rdata;

  //===========================================================================
  // Pipeline reg
  //===========================================================================

  logic pipe_flush_i;
  logic pipe_advance_o;
  logic pipe_flush_o;
  logic pipe_bubble_o;


  if (PIPELINED != 0) begin : g_registered
    logic mc_active;

    assign mc_active    = op_active_ex || (state != EX_IDLE);

    //
    // The hazard unit might request a flush while we are mid mc op.
    // By the time the op completes, it might lower the flush request,
    // don't send it until mc is done.
    //
    assign pipe_flush_i = ex_mem_flush && !mc_active;

  end else begin : g_passthrough
    assign pipe_flush_i = 1'b0;

    `SVC_UNUSED({ex_mem_flush});
  end

  svc_rv_pipe_ctrl #(
      .REG(PIPELINED)
  ) pipe_ctrl_inst (
      .clk      (clk),
      .rst_n    (rst_n),
      .stall_i  (stall_ex),
      .flush_i  (pipe_flush_i),
      .bubble_i (!result_valid),
      .advance_o(pipe_advance_o),
      .flush_o  (pipe_flush_o),
      .bubble_o (pipe_bubble_o)
  );

  //
  // Control signals (WITH bubble)
  //
  // These trigger actions (regfile write, memory access, trap handling) so
  // they must be cleared when invalid. This allows downstream to use them
  // directly without re-checking valid.
  //
  // For instr_valid_mem, we use result_valid rather than instr_valid_ex
  // because the EX stage has its own state machine for multi-cycle ops.
  // result_valid correctly reflects when EX is producing a valid result
  // (accounting for multi-cycle operations), while instr_valid_ex only
  // reflects the input.
  //
  localparam int CTRL_WIDTH = 5;

  svc_rv_pipe_data #(
      .WIDTH(CTRL_WIDTH),
      .REG  (PIPELINED)
  ) pipe_ctrl_data (
      .clk(clk),
      .rst_n(rst_n),
      .advance(pipe_advance_o),
      .flush(pipe_flush_o),
      .bubble(pipe_bubble_o),
      .data_i({
        result_valid,
        reg_write_ex,
        mem_read_ex,
        mem_write_ex,
        trap_ex | misalign_trap
      }),
      .data_o({
        instr_valid_mem, reg_write_mem, mem_read_mem, mem_write_mem, trap_mem
      })
  );

  //
  // Payload signals (NO bubble) - can be stale
  //
  localparam int PAYLOAD_WIDTH = 1 +  // is_branch_mem
  1 +  // is_jalr_mem
  1 +  // is_jmp_mem
  1 +  // branch_taken_mem
  1 +  // bpred_taken_mem
  1 +  // is_ebreak_mem
  32 +  // instr_mem
  3 +  // res_src_mem
  5 +  // rd_mem
  5 +  // rs2_mem
  3 +  // funct3_mem
  XLEN +  // alu_result_mem
  XLEN +  // rs1_data_mem
  XLEN +  // rs2_data_mem
  XLEN +  // pc_plus4_mem
  XLEN +  // jb_tgt_mem
  XLEN +  // pred_tgt_mem
  XLEN +  // csr_rdata_mem
  4 * XLEN +  // mul_ll/lh/hl/hh_mem
  2;  // trap_code_mem

  svc_rv_pipe_data #(
      .WIDTH(PAYLOAD_WIDTH),
      .REG  (PIPELINED)
  ) pipe_payload_data (
      .clk(clk),
      .rst_n(rst_n),
      .advance(pipe_advance_o),
      .flush(1'b0),
      .bubble(1'b0),
      .data_i({
        is_branch_ex,
        is_jalr_ex,
        is_jmp_ex,
        branch_taken_ex,
        bpred_taken_ex,
        is_ebreak_ex,
        instr_ex,
        res_src_ex,
        rd_ex,
        rs2_ex,
        funct3_ex,
        alu_result_ex,
        fwd_rs1_ex,
        fwd_rs2_ex,
        pc_plus4_ex,
        jb_tgt_ex,
        pred_tgt_ex,
        csr_rdata_ex,
        mul_ll_ex,
        mul_lh_ex,
        mul_hl_ex,
        mul_hh_ex,
        misalign_trap ? TRAP_INSTR_MISALIGN : trap_code_ex
      }),
      .data_o({
        is_branch_mem,
        is_jalr_mem,
        is_jmp_mem,
        branch_taken_mem,
        bpred_taken_mem,
        is_ebreak_mem,
        instr_mem,
        res_src_mem,
        rd_mem,
        rs2_mem,
        funct3_mem,
        alu_result_mem,
        rs1_data_mem,
        rs2_data_mem,
        pc_plus4_mem,
        jb_tgt_mem,
        pred_tgt_mem,
        csr_rdata_mem,
        mul_ll_mem,
        mul_lh_mem,
        mul_hl_mem,
        mul_hh_mem,
        trap_code_mem
      })
  );

  //
  // M-extension result (NO bubble) - payload
  //
  svc_rv_pipe_data #(
      .WIDTH(XLEN),
      .REG  (PIPELINED)
  ) pipe_m_result_data (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance_o),
      .flush  (1'b0),
      .bubble (1'b0),
      .data_i (m_result_ex),
      .data_o (m_result_mem)
  );

  //
  // FP control signals (WITH bubble)
  //
  localparam int FP_CTRL_WIDTH = 1 + 1 + 1 +
      5;  // is_fp_load, is_fp_store, fp_reg_write, fp_rd

  svc_rv_pipe_data #(
      .WIDTH(FP_CTRL_WIDTH),
      .REG  (PIPELINED)
  ) pipe_fp_ctrl_data (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance_o),
      .flush  (pipe_flush_o),
      .bubble (pipe_bubble_o),
      .data_i ({is_fp_load_ex, is_fp_store_ex, fp_reg_write_ex, fp_rd_ex}),
      .data_o ({is_fp_load_mem, is_fp_store_mem, fp_reg_write_mem, fp_rd_mem})
  );

  //
  // FP result and flags (NO bubble) - payload
  //
  localparam
      int FP_RESULT_WIDTH = XLEN + 5 + XLEN;  // fp_result, fflags, fp_rs2_data

  svc_rv_pipe_data #(
      .WIDTH(FP_RESULT_WIDTH),
      .REG  (PIPELINED)
  ) pipe_fp_result_data (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance_o),
      .flush  (1'b0),
      .bubble (1'b0),
      .data_i ({fp_result_ex, fflags_ex, fp_rs2_data_ex}),
      .data_o ({fp_result_mem, fflags_mem, fp_rs2_data_mem})
  );

  `SVC_UNUSED({funct7_ex[6:5], funct7_ex[4:0], is_m_ex, fp_result_valid_ex,
               is_fp_ex});

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_STAGE_EX
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)

  //
  // Force reset at start of formal verification
  //
  // This ensures the solver starts from a valid reset state rather than
  // an arbitrary initial state that may violate module invariants.
  //
  // Only apply when verifying this module specifically, not when used as
  // a submodule in other formal checks (like RVFI verification).
  //
  initial assume (!rst_n);
`else
  `define FASSERT(label, a) label: assume(a)
  `define FASSUME(label, a) label: assert(a)
  `define FCOVER(label, a)
`endif

  logic f_past_valid = 1'b0;

  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  //
  // instr_valid_ex assumptions (input interface)
  //
  // instr_valid_ex stability is controlled by upstream (ID stage) based on
  // op_active_ex. No handshake assumptions needed here since s_ready
  // was removed.
  //

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cover back-to-back valid outputs
      `FCOVER(c_back_to_back, $past(instr_valid_mem) && instr_valid_mem);
    end
  end

  //
  // Cover multi-cycle operation scenarios
  //
  if (PIPELINED != 0) begin : g_mc_covers
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        `FCOVER(c_mc_starts, $rose(op_active_ex) && is_mc_ex);
        `FCOVER(c_mc_complete, $past(state == EX_MC_EXEC
                ) && state == EX_MC_DONE && instr_valid_mem);
        `FCOVER(c_mc_back_to_back, $past(state == EX_MC_DONE
                ) && state == EX_MC_EXEC);
        `FCOVER(c_mc_then_normal, $past(state == EX_MC_DONE
                ) && state == EX_IDLE && instr_valid_ex);
      end
    end
  end

  //
  // Stall during multi-cycle operation assertions
  //
  // When stall_ex is asserted during a multi-cycle operation:
  // 1. State machine should pause (not advance)
  // 2. Division result should not be lost
  // 3. When stall releases, result should be correctly output
  //
  if (PIPELINED != 0) begin : g_mc_stall_asserts
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        //
        // State should not advance while stalled
        //
        if ($past(stall_ex)) begin
          `FASSERT(a_stall_holds_state, state == $past(state));
        end

        //
        // If division completes during stall, result must not be lost.
        // When we're in EXEC and division completes (!m_busy_ex), if stalled,
        // we must stay in EXEC (not advance to DONE).
        //
        if ($past(stall_ex && state == EX_MC_EXEC && !m_busy_ex)) begin
          `FASSERT(a_stall_preserves_mc_result, state == EX_MC_EXEC);
        end

        //
        // After stall releases following a completed division,
        // instr_valid_mem must eventually assert
        //
        // (This is a liveness property - covered by the cover above)
        //
      end
    end

    //
    // Cover: stall during MC execution
    //
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        `FCOVER(c_stall_during_mc_exec, state == EX_MC_EXEC && stall_ex);
        `FCOVER(c_stall_when_div_completes, $past(
                state == EX_MC_EXEC && stall_ex && !m_busy_ex));
        `FCOVER(c_stall_release_after_div, $past(state == EX_MC_EXEC && stall_ex
                ) && !stall_ex);
      end
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
