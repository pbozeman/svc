`ifndef SVC_RV_PC_SEL_SV
`define SVC_RV_PC_SEL_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V PC Selection Arbiter
//
// Combines PC selection signals from multiple sources with priority:
// 1. MEM stage redirects (highest priority) - branch/JALR mispredictions
// 2. EX stage redirects - non-predicted branches/jumps (BPRED=0 only)
// 3. RAS predictions (IF stage) - JALR return predictions
// 4. BTB predictions (IF stage) - branch/JAL predictions
// 5. ID stage predictions - static BTFNT fallback
// 6. Sequential PC (default)
//
module svc_rv_pc_sel #(
    parameter int XLEN,
    parameter int RAS_ENABLE,
    parameter int BTB_ENABLE
) (
    //
    // PC selection from MEM stage (branch/JALR mispredictions)
    //
    input logic            jalr_mispredicted_mem,
    input logic            mispredicted_mem,
    input logic [XLEN-1:0] pc_redirect_target_mem,

    //
    // PC selection from EX stage (non-predicted branch/jump redirects)
    //
    input logic [     1:0] pc_sel_ex,
    input logic [XLEN-1:0] pc_redirect_target_ex,

    //
    // PC selection and target from ID stage (static prediction)
    //
    input logic [     1:0] pc_sel_id,
    input logic [XLEN-1:0] pred_target_id,

    //
    // RAS prediction
    //
    input logic            ras_valid,
    input logic [XLEN-1:0] ras_target,
    input logic            is_jalr_id,
    input logic            ras_valid_id,
    input logic [XLEN-1:0] ras_target_id,

    //
    // BTB prediction (IF stage)
    //
    input logic            btb_hit,
    input logic            btb_taken,
    input logic [XLEN-1:0] btb_target,
    input logic            btb_is_return,

    //
    // BTB prediction (ID stage - for checking early RAS prediction)
    //
    input logic btb_hit_id,
    input logic btb_is_return_id,

    //
    // Final PC selection outputs
    //
    output logic [     1:0] pc_sel,
    output logic [XLEN-1:0] pred_target,
    output logic [XLEN-1:0] pc_redirect_target,
    output logic            btb_pred_taken,
    output logic            ras_pred_taken,

    //
    // Prediction signals to PC stage (for optional registration)
    //
    output logic            ras_valid_pc,
    output logic [XLEN-1:0] ras_target_pc,
    output logic            btb_hit_pc,
    output logic            btb_pred_taken_pc,
    output logic [XLEN-1:0] btb_target_pc,
    output logic            btb_is_return_pc
);

  `include "svc_rv_defs.svh"

  //
  // Internal PC selection (before EX override)
  //
  logic [1:0] pc_sel_ras_btb;

  if (RAS_ENABLE != 0 || BTB_ENABLE != 0) begin : g_ras_btb_pc_sel
    logic btb_prediction_valid;
    logic ras_prediction_valid;
    logic ras_early_pred_if;
    logic ras_late_pred_id;

    //
    // RAS prediction is valid when:
    // - RAS has valid entry (stack not empty) AND one of:
    //   - BTB hit with is_return flag (early prediction, no flush needed)
    //   - ID stage confirms this is a JALR (late prediction on first execution)
    //
    // The BTB-based path enables zero-bubble returns after the first execution.
    //
    if (RAS_ENABLE != 0) begin : g_ras_pred
      //
      // Early prediction: BTB hit with is_return in IF (speculative fetch)
      // Late prediction: JALR in ID that was NOT predicted early
      //
      // Note: Late prediction uses ras_valid_id (buffered from IF) to match
      // bpred_taken_id in svc_rv_bpred_id.sv. If we used ras_valid (current),
      // a RAS pop between IF and ID would cause bpred_taken_id=1 but
      // ras_prediction_valid=0, leading to undetected mispredictions.
      //
      assign ras_early_pred_if = btb_hit && btb_is_return;
      assign ras_late_pred_id = is_jalr_id && !(btb_hit_id && btb_is_return_id);
      assign ras_prediction_valid = ((ras_early_pred_if && ras_valid) ||
                                     (ras_late_pred_id && ras_valid_id));
      assign ras_valid_pc = ras_valid;
      assign ras_target_pc = ras_target;
    end else begin : g_no_ras_pred
      assign ras_prediction_valid = 1'b0;
      assign ras_early_pred_if    = 1'b0;
      assign ras_late_pred_id     = 1'b0;
      assign ras_valid_pc         = 1'b0;
      assign ras_target_pc        = '0;

      `SVC_UNUSED({
                  ras_valid,
                  ras_valid_id,
                  ras_target,
                  ras_target_id,
                  is_jalr_id,
                  btb_is_return,
                  btb_hit_id,
                  btb_is_return_id
                  });
    end

    //
    // BTB prediction is valid when:
    // - BTB hits and predicts taken
    //
    // No ID stage validation needed - BTB only contains entries for actual
    // branch/jump instructions (updated only for is_predictable in EX stage)
    //
    if (BTB_ENABLE != 0) begin : g_btb_pred
      assign btb_prediction_valid = btb_hit && btb_taken;
      assign btb_hit_pc           = btb_hit;
      assign btb_pred_taken_pc    = btb_prediction_valid;
      assign btb_target_pc        = btb_target;
      assign btb_is_return_pc     = btb_is_return;
    end else begin : g_no_btb_pred
      assign btb_prediction_valid = 1'b0;
      assign btb_hit_pc           = 1'b0;
      assign btb_pred_taken_pc    = 1'b0;
      assign btb_target_pc        = '0;
      assign btb_is_return_pc     = 1'b0;

      `SVC_UNUSED({btb_hit, btb_taken, btb_target});
    end

    //
    // RAS + BTB + Static prediction arbitration
    //
    // Priority: ID prediction > RAS > BTB > static
    // - ID prediction takes highest priority (for concrete decoded instructions)
    // - RAS takes priority over BTB for return instructions
    // - BTB handles other branches
    // - Static prediction is the fallback
    //
    // When ID makes a prediction (pc_sel_id==PREDICTED), it must override
    // RAS/BTB speculation for the current IF PC. ID's prediction is for a
    // concrete, decoded instruction already in the pipeline. RAS/BTB predictions
    // are speculative for instructions not yet decoded. The decoded instruction
    // must take priority.
    //
    always_comb begin
      if (pc_sel_id == PC_SEL_PREDICTED) begin
        pc_sel_ras_btb = pc_sel_id;
        pred_target    = pred_target_id;
      end else if (ras_prediction_valid) begin
        pc_sel_ras_btb = PC_SEL_PREDICTED;
        //
        // Late prediction uses ras_target_id (buffered from IF to ID) to match
        // the target that bpred_taken_id was based on. This ensures consistency
        // with misprediction detection in MEM stage.
        //
        // Early prediction uses current ras_target (prediction happens in IF).
        //
        // Note: Use ras_late_pred_id (not ras_early_pred_if) to select the
        // target. ras_early_pred_if reflects the current IF state, which may be
        // for a different instruction. When making a late prediction for the
        // ID-stage JALR, we must use the buffered target even if IF currently
        // has an early prediction for a different instruction.
        //
        pred_target    = ras_late_pred_id ? ras_target_id : ras_target;
      end else if (btb_prediction_valid) begin
        pc_sel_ras_btb = PC_SEL_PREDICTED;
        pred_target    = btb_target;
      end else begin
        pc_sel_ras_btb = pc_sel_id;
        pred_target    = pred_target_id;
      end
    end

    //
    // PC-mux-synchronous signals indicating prediction source
    //
    // These signals are used by the hazard unit to distinguish prediction types:
    // - btb_pred_taken: BTB or RAS early predicted (no flush needed)
    // - ras_pred_taken: RAS predicted late without BTB (flush needed)
    // - static: Neither BTB nor RAS (flush needed)
    //
    // For RAS early predictions (btb_hit && btb_is_return), we set btb_pred_taken
    // even if btb_taken=0. This prevents incorrect flushes when the BTB counter
    // hasn't been trained to "taken" yet. Returns are always taken, so we treat
    // any BTB hit with is_return as an early prediction.
    //
    assign btb_pred_taken = ((pc_sel_id != PC_SEL_PREDICTED) &&
                             (btb_prediction_valid || ras_early_pred_if));
    assign
        ras_pred_taken = ((pc_sel_id != PC_SEL_PREDICTED) && ras_late_pred_id);

  end else begin : g_no_ras_btb_pc_sel
    assign pc_sel_ras_btb    = pc_sel_id;
    assign pred_target       = pred_target_id;
    assign btb_pred_taken    = 1'b0;
    assign ras_pred_taken    = 1'b0;
    assign btb_hit_pc        = 1'b0;
    assign btb_pred_taken_pc = 1'b0;
    assign btb_target_pc     = '0;
    assign btb_is_return_pc  = 1'b0;
    assign ras_valid_pc      = 1'b0;
    assign ras_target_pc     = '0;

    // verilog_format: off
    `SVC_UNUSED({ras_valid, ras_valid_id, ras_target, ras_target_id, is_jalr_id,
                 btb_hit, btb_taken, btb_target, btb_is_return, btb_hit_id,
                 btb_is_return_id});
    // verilog_format: on
  end

  //
  // Final PC selection: MEM mispredictions override EX, EX overrides predictions
  //
  // Priority:
  // 1. MEM stage misprediction (branch/JALR - takes 2 cycles to detect)
  // 2. EX stage redirect (for non-predicted configurations)
  // 3. Predictions (speculative)
  //
  always_comb begin
    if (mispredicted_mem) begin
      pc_sel             = PC_SEL_REDIRECT;
      pc_redirect_target = pc_redirect_target_mem;
    end else if (pc_sel_ex == PC_SEL_REDIRECT) begin
      pc_sel             = PC_SEL_REDIRECT;
      pc_redirect_target = pc_redirect_target_ex;
    end else begin
      pc_sel             = pc_sel_ras_btb;
      pc_redirect_target = '0;
    end
  end


  `SVC_UNUSED(jalr_mispredicted_mem);

endmodule

`endif
