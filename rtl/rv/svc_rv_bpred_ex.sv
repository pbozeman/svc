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
    parameter int BTB_ENABLE = 0
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
    // BTB update interface
    //
    output logic            btb_update_en,
    output logic [XLEN-1:0] btb_update_pc,
    output logic [XLEN-1:0] btb_update_target,
    output logic            btb_update_taken,
    output logic            btb_update_is_return
);

  //
  // Misprediction detection moved to MEM stage
  //
  // Branch misprediction detection moved to MEM stage (svc_rv_bpred_mem) to
  // break critical timing path. EX stage computes branch outcome but doesn't
  // compare against prediction - that comparison happens one cycle later in MEM.
  //
  assign mispredicted_ex = 1'b0;

  //
  // JALR misprediction detection moved to MEM stage (svc_rv_bpred_mem)
  //
  // This was moved to break the critical timing path from:
  // forwarding → ALU → JALR target → misprediction comparison → PC selection
  //
  `SVC_UNUSED({BPRED, bpred_taken_ex, is_jalr_ex, pred_target_ex});

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
