`ifndef SVC_RV_PC_SEL_SV
`define SVC_RV_PC_SEL_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V PC Selection Arbiter
//
// Combines PC selection signals from multiple sources with priority:
// 1. MEM stage JALR redirects (highest priority) - JALR misprediction
// 2. EX stage redirects - branch mispredictions/actual jump resolution
// 3. RAS predictions (IF stage) - JALR return predictions
// 4. BTB predictions (IF stage) - branch/JAL predictions
// 5. ID stage predictions - static BTFNT fallback
// 6. Sequential PC (default)
//
module svc_rv_pc_sel #(
    parameter int XLEN       = 32,
    parameter int RAS_ENABLE = 0,
    parameter int BTB_ENABLE = 0
) (
    //
    // PC selection from MEM stage (JALR misprediction)
    //
    input logic            jalr_mispredicted_mem,
    input logic [XLEN-1:0] pc_redirect_target_mem,

    //
    // PC selection from EX stage (branch redirects)
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
    // Prediction signals to IF stage
    //
    output logic            ras_valid_if,
    output logic [XLEN-1:0] ras_target_if,
    output logic            btb_hit_if,
    output logic            btb_pred_taken_if,
    output logic [XLEN-1:0] btb_target_if,
    output logic            btb_is_return_if
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
      assign ras_early_pred_if = btb_hit && btb_is_return;
      assign ras_late_pred_id = is_jalr_id && !(btb_hit_id && btb_is_return_id);
      assign ras_prediction_valid = ras_valid &&
          (ras_early_pred_if || ras_late_pred_id);
      assign ras_valid_if = ras_valid;
      assign ras_target_if = ras_target;
    end else begin : g_no_ras_pred
      assign ras_prediction_valid = 1'b0;
      assign ras_early_pred_if    = 1'b0;
      assign ras_late_pred_id     = 1'b0;
      assign ras_valid_if         = 1'b0;
      assign ras_target_if        = '0;

      `SVC_UNUSED({
                  ras_valid,
                  ras_target,
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
      assign btb_hit_if           = btb_hit;
      assign btb_pred_taken_if    = btb_prediction_valid;
      assign btb_target_if        = btb_target;
      assign btb_is_return_if     = btb_is_return;
    end else begin : g_no_btb_pred
      assign btb_prediction_valid = 1'b0;
      assign btb_hit_if           = 1'b0;
      assign btb_pred_taken_if    = 1'b0;
      assign btb_target_if        = '0;
      assign btb_is_return_if     = 1'b0;

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
      unique case (1'b1)
        (pc_sel_id == PC_SEL_PREDICTED): begin
          pc_sel_ras_btb = pc_sel_id;
          pred_target    = pred_target_id;
        end
        ras_prediction_valid: begin
          pc_sel_ras_btb = PC_SEL_PREDICTED;
          pred_target    = ras_target;
        end
        btb_prediction_valid: begin
          pc_sel_ras_btb = PC_SEL_PREDICTED;
          pred_target    = btb_target;
        end
        default: begin
          pc_sel_ras_btb = pc_sel_id;
          pred_target    = pred_target_id;
        end
      endcase
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
    assign btb_hit_if        = 1'b0;
    assign btb_pred_taken_if = 1'b0;
    assign btb_target_if     = '0;
    assign btb_is_return_if  = 1'b0;
    assign ras_valid_if      = 1'b0;
    assign ras_target_if     = '0;

    // verilog_format: off
    `SVC_UNUSED({ras_valid, ras_target, is_jalr_id, btb_hit, btb_taken, btb_target,
                 btb_is_return, btb_hit_id, btb_is_return_id});
    // verilog_format: on
  end

  //
  // Final PC selection: MEM JALR mispredictions override EX, EX overrides predictions
  //
  // Priority:
  // 1. MEM stage JALR misprediction (takes 2 cycles to detect, but rare)
  // 2. EX stage branch/jump redirect (1 cycle, common for branches)
  // 3. Predictions (speculative)
  //
  always_comb begin
    if (jalr_mispredicted_mem) begin
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

endmodule

`endif
