`ifndef SVC_RV_BPRED_ID_SV
`define SVC_RV_BPRED_ID_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Branch Prediction - ID Stage
//
// Implements static BTFNT prediction and BTB/static arbitration.
//
// Three-tier prediction hierarchy:
// 1. BTB hit (from IF stage) - highest priority, already predicted
// 2. Static BTFNT (ID stage) - fallback when BTB misses
// 3. No prediction - for unpredictable instructions
//
// CRITICAL: Double-prediction avoidance. When BTB already predicted in
// IF stage (btb_hit_id=1), ID must NOT issue another redirect or it
// will flush the wrong PC (the target instruction, not sequential).
//
module svc_rv_bpred_id #(
    parameter int XLEN       = 32,
    parameter int BPRED      = 0,
    parameter int BTB_ENABLE = 0
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
    // Prediction outputs
    //
    output logic [     1:0] pc_sel_id,
    output logic [XLEN-1:0] pred_target,
    output logic            pred_taken_id,
    output logic            bpred_taken_id
);

  `include "svc_rv_defs.svh"

  if (BPRED != 0) begin : g_bpred

    if (BTB_ENABLE != 0) begin : g_btb_pred
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
      // CRITICAL: Check btb_hit_id (buffered from IF) to avoid double-prediction.
      // When BTB already predicted this instruction in IF stage, ID must NOT
      // issue another redirect or it will flush the wrong PC (the instruction
      // after the target, not the target itself).
      //
      // For BRAM with 2-cycle latency (BRAM + IF/ID register), by the time
      // instruction reaches ID, IF has already moved to the target. ID's redirect
      // would flush that target instruction, skipping it - architectural bug!
      //
      always_comb begin
        if (btb_hit_id && is_predictable) begin
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
          // BTB missed - use static BTFNT prediction
          //
          pred_taken_id = static_taken;
          pred_target   = pc_id + imm_id;
        end else begin
          pred_taken_id = 1'b0;
          pred_target   = '0;
        end
      end

      //
      // Use BTB prediction from IF stage if BTB made a prediction,
      // otherwise use ID stage's static prediction
      //
      assign bpred_taken_id = btb_hit_id ? btb_pred_taken_id : pred_taken_id;

    end else begin : g_static_pred
      //
      // Static BTFNT only
      //
      assign pred_taken_id = ((is_branch_id && imm_id[XLEN-1]) ||
                              (is_jump_id && !jb_target_src_id));
      assign pred_target = pc_id + imm_id;
      assign bpred_taken_id = pred_taken_id;

      `SVC_UNUSED({btb_hit_id, btb_pred_taken_id});
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
                 btb_hit_id, btb_pred_taken_id});
    // verilog_format: on
  end

endmodule

`endif
