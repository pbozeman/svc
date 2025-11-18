`ifndef SVC_RV_BPRED_EX_SV
`define SVC_RV_BPRED_EX_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Branch Prediction - EX Stage
//
// Implements:
// - Misprediction detection (actual vs predicted outcome)
// - BTB update signal generation
//
module svc_rv_bpred_ex #(
    parameter int XLEN       = 32,
    parameter int BPRED      = 0,
    parameter int BTB_ENABLE = 0,
    parameter int RAS_ENABLE = 0
) (
    //
    // Branch/jump analysis from EX stage
    //
    input logic            is_branch_ex,
    input logic            is_jal_ex,
    input logic            is_jalr_ex,
    input logic [     4:0] rd_ex,
    input logic            bpred_taken_ex,
    input logic            branch_taken_ex,
    input logic [XLEN-1:0] pc_ex,
    input logic [XLEN-1:0] jb_target_ex,
    input logic [XLEN-1:0] pred_target_ex,

    //
    // Misprediction detection output
    //
    output logic mispredicted_ex,

    //
    // PC control output
    //
    output logic pc_sel_jump_ex,

    //
    // BTB update interface
    //
    output logic            btb_update_en,
    output logic [XLEN-1:0] btb_update_pc,
    output logic [XLEN-1:0] btb_update_target,
    output logic            btb_update_taken,
    output logic            btb_update_is_return
);

  //
  // Misprediction detection
  //
  if (BPRED != 0) begin : g_bpred
    //
    // Branch misprediction: actual outcome vs prediction
    //
    always_comb begin
      mispredicted_ex = is_branch_ex && (bpred_taken_ex != branch_taken_ex);
    end
  end else begin : g_no_bpred
    assign mispredicted_ex = 1'b0;
    `SVC_UNUSED({is_branch_ex, bpred_taken_ex, branch_taken_ex});
  end

  //
  // JALR misprediction detection
  //
  if (BPRED != 0 && RAS_ENABLE != 0) begin : g_jalr_mispred
    logic jalr_mispredicted;

    //
    // JALR mispredicted if: not predicted OR predicted target doesn't match actual
    //
    assign jalr_mispredicted = is_jalr_ex &&
        (!bpred_taken_ex || (pred_target_ex != jb_target_ex));

    //
    // Only redirect on JALR misprediction (JAL is predicted in ID)
    //
    assign pc_sel_jump_ex = jalr_mispredicted;

  end else if (BPRED != 0) begin : g_jalr_no_ras
    //
    // Without RAS, always redirect on JALR (not predicted)
    //
    assign pc_sel_jump_ex = is_jalr_ex;

    `SVC_UNUSED(pred_target_ex);

  end else begin : g_no_jalr_mispred
    //
    // Without BPRED, all jumps cause redirects (JAL and JALR)
    //
    assign pc_sel_jump_ex = is_jal_ex || is_jalr_ex;

    `SVC_UNUSED(pred_target_ex);
  end

  //
  // BTB Update Logic
  //
  // Update BTB for branches, PC-relative jumps (JAL), and return instructions.
  // Regular JALR excluded because target depends on register values.
  // Returns (JALR x0, x1, 0) are special - they use RAS for prediction.
  //
  if (BTB_ENABLE != 0) begin : g_btb_update
    logic is_predictable;
    logic is_return;

    //
    // Return detection: JALR with rd = x0
    //
    // Detects return/tail-call pattern where rd = x0 (don't save return address).
    // Typical returns use rs1 = x1/x5 and imm = 0, but we don't check these to
    // also catch tail calls and other indirect jumps with rd = x0.
    //
    // RAS will only predict if it has a valid entry, so false positives
    // (non-return JALR x0 instructions) are handled gracefully.
    //
    assign is_return = is_jalr_ex && (rd_ex == 5'd0);

    //
    // Predictable: branches, JAL, and returns
    //
    // Returns are predictable using RAS, so we add them to BTB with is_return
    // flag. On subsequent fetches, BTB hit + is_return enables early RAS lookup.
    //
    assign is_predictable = is_branch_ex || is_jal_ex || is_return;

    //
    // Update BTB for all predictable instructions
    //
    // This allows 2-bit counter to train on both taken and not-taken outcomes
    //
    assign btb_update_en = is_predictable;
    assign btb_update_pc = pc_ex;
    assign btb_update_target = jb_target_ex;
    assign btb_update_is_return = is_return;

    //
    // For branches: pass actual outcome to train counter
    // For JAL/returns: always taken
    //
    assign btb_update_taken = (is_jal_ex || is_return) ? 1'b1 : branch_taken_ex;

  end else begin : g_no_btb_update
    assign btb_update_en        = 1'b0;
    assign btb_update_pc        = '0;
    assign btb_update_target    = '0;
    assign btb_update_taken     = 1'b0;
    assign btb_update_is_return = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({is_branch_ex, is_jal_ex, is_jalr_ex, rd_ex, pc_ex, jb_target_ex,
                 branch_taken_ex});
    // verilog_format: on
  end

endmodule

`endif
