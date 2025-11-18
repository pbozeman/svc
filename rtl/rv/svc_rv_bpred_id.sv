`ifndef SVC_RV_BPRED_ID_SV
`define SVC_RV_BPRED_ID_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Branch Prediction - ID Stage
//
// Implements static BTFNT prediction with RAS and BTB arbitration.
//
// Four-tier prediction hierarchy:
// 1. RAS hit (from IF stage) - highest priority for JALR returns
// 2. BTB hit (from IF stage) - dynamic prediction for branches/JAL
// 3. Static BTFNT (ID stage) - fallback when RAS/BTB miss
// 4. No prediction - for unpredictable instructions
//
// CRITICAL: Double-prediction avoidance. When RAS or BTB already predicted
// in IF stage, ID must NOT issue another redirect or it will flush the
// wrong PC (the target instruction, not sequential).
//
module svc_rv_bpred_id #(
    parameter int XLEN       = 32,
    parameter int BPRED      = 0,
    parameter int BTB_ENABLE = 0,
    parameter int RAS_ENABLE = 0
) (
    //
    // Instruction analysis from decoder
    //
    input logic [XLEN-1:0] pc_id,
    input logic [XLEN-1:0] imm_id,
    input logic            is_branch_id,
    input logic            is_jump_id,
    input logic            jb_target_src_id,

    //
    // BTB prediction from IF stage (via pipeline register)
    //
    input logic btb_hit_id,
    input logic btb_pred_taken_id,

    //
    // RAS prediction from IF stage (via pipeline register)
    //
    input logic            ras_valid_id,
    input logic [XLEN-1:0] ras_target_id,

    //
    // Prediction outputs
    //
    output logic [     1:0] pc_sel_id,
    output logic [XLEN-1:0] pred_target,
    output logic            pred_taken_id,
    output logic            bpred_taken_id,

    //
    // RAS detection output
    //
    output logic is_jalr_id
);

  `include "svc_rv_defs.svh"

  //
  // JALR detection: used for RAS prediction
  //
  // JALR is indicated by: is_jump_id && jb_target_src_id
  // This signal tells the pipeline that RAS prediction should be considered
  //
  assign is_jalr_id = is_jump_id && jb_target_src_id;

  if (BPRED != 0) begin : g_bpred

    if (BTB_ENABLE != 0 || RAS_ENABLE != 0) begin : g_dynamic_pred
      logic is_predictable;
      logic static_taken;
      logic ras_pred_taken;

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
      // RAS prediction: valid when RAS has entry and instruction is JALR
      //
      assign ras_pred_taken = ras_valid_id && is_jalr_id;

      //
      // Four-tier prediction: RAS (IF) > BTB (IF) > Static BTFNT (ID) > No prediction
      //
      // This implements the predictor hierarchy:
      // 1. RAS hit in IF stage for JALR → immediate speculation (highest priority)
      // 2. BTB hit in IF stage for branches/JAL → immediate speculation
      // 3. RAS/BTB miss → Static BTFNT in ID stage (fallback)
      // 4. Not predictable → No prediction
      //
      // CRITICAL: Check ras_pred_taken and btb_hit_id (buffered from IF) to avoid
      // double-prediction. When RAS or BTB already predicted this instruction in IF
      // stage, ID must NOT issue another redirect or it will flush the wrong PC
      // (the instruction after the target, not the target itself).
      //
      // For BRAM with 2-cycle latency (BRAM + IF/ID register), by the time
      // instruction reaches ID, IF has already moved to the target. ID's redirect
      // would flush that target instruction, skipping it - architectural bug!
      //
      always_comb begin
        if (ras_pred_taken) begin
          //
          // RAS already handled this in IF stage - ID must NOT redirect
          //
          // Setting pred_taken_id=0 prevents pc_sel_id from issuing another redirect
          // RAS prediction is tracked separately via ras_pred_taken for misprediction detection
          //
          pred_taken_id = 1'b0;
          pred_target   = '0;
        end else if (btb_hit_id && is_predictable) begin
          //
          // BTB already handled this in IF stage - ID must NOT redirect
          //
          // Setting pred_taken_id=0 prevents pc_sel_id from issuing another redirect
          // BTB prediction is tracked separately via btb_pred_taken_id for misprediction detection
          //
          pred_taken_id = 1'b0;
          pred_target   = '0;
        end else if (is_predictable) begin
          //
          // RAS/BTB missed - use static BTFNT prediction
          //
          pred_taken_id = static_taken;
          pred_target   = pc_id + imm_id;
        end else begin
          pred_taken_id = 1'b0;
          pred_target   = '0;
        end
      end

      //
      // Final prediction: Use RAS for JALR, BTB for branches/JAL,
      // otherwise use ID stage's static prediction
      //
      // Priority: RAS > BTB > Static
      //
      // RAS always predicts taken when valid, BTB uses its prediction counter
      //
      assign bpred_taken_id = ras_pred_taken ? 1'b1 :
          (btb_hit_id && is_predictable) ? btb_pred_taken_id : pred_taken_id;

      //
      // ras_target_id is passed through from IF stage
      // but not used in this module (used elsewhere in pipeline)
      //
      `SVC_UNUSED(ras_target_id);

    end else begin : g_static_pred
      //
      // Static BTFNT only (no RAS or BTB)
      //
      assign pred_taken_id = ((is_branch_id && imm_id[XLEN-1]) ||
                              (is_jump_id && !jb_target_src_id));
      assign pred_target = pc_id + imm_id;
      assign bpred_taken_id = pred_taken_id;

      `SVC_UNUSED({btb_hit_id, btb_pred_taken_id, ras_valid_id, ras_target_id});
    end

    //
    // PC selection output to IF stage
    //
    assign pc_sel_id = pred_taken_id ? PC_SEL_PREDICTED : PC_SEL_SEQUENTIAL;

  end else begin : g_no_bpred
    assign pred_taken_id  = 1'b0;
    assign pred_target    = '0;
    assign pc_sel_id      = PC_SEL_SEQUENTIAL;
    assign bpred_taken_id = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({pc_id, imm_id, is_branch_id, is_jump_id, jb_target_src_id,
                 btb_hit_id, btb_pred_taken_id, ras_valid_id, ras_target_id});
    // verilog_format: on
  end

endmodule

`endif
