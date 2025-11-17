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
    input logic            is_jump_ex,
    input logic            jb_target_src_ex,
    input logic            bpred_taken_ex,
    input logic            branch_taken_ex,
    input logic [XLEN-1:0] pc_ex,
    input logic [XLEN-1:0] jb_target_ex,

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
    output logic            btb_update_taken
);

  //
  // Misprediction detection
  //
  if (BPRED != 0) begin : g_bpred
    //
    // Misprediction detection (actual outcome vs prediction)
    //
    always_comb begin
      mispredicted_ex = is_branch_ex && (bpred_taken_ex != branch_taken_ex);
    end
  end else begin : g_no_bpred
    assign mispredicted_ex = 1'b0;
    `SVC_UNUSED({is_branch_ex, bpred_taken_ex, branch_taken_ex});
  end

  //
  // BTB Update Logic
  //
  // Update BTB for all branches and PC-relative jumps (JAL).
  // JALR excluded because target depends on register values unknown at fetch.
  //
  if (BTB_ENABLE != 0) begin : g_btb_update
    logic is_predictable;
    logic is_jalr;

    //
    // Predictable: branches and PC-relative jumps (JAL), but not JALR
    //
    assign is_predictable = is_branch_ex || (is_jump_ex && !jb_target_src_ex);
    assign is_jalr        = is_jump_ex && jb_target_src_ex;

    `SVC_UNUSED({is_jalr});

    //
    // Update BTB for all predictable instructions
    //
    // This allows 2-bit counter to train on both taken and not-taken outcomes
    //
    assign btb_update_en     = is_predictable;
    assign btb_update_pc     = pc_ex;
    assign btb_update_target = jb_target_ex;

    //
    // For branches: pass actual outcome to train counter
    // For JAL: always taken
    //
    assign btb_update_taken  = is_jump_ex ? 1'b1 : branch_taken_ex;

  end else begin : g_no_btb_update
    assign btb_update_en     = 1'b0;
    assign btb_update_pc     = '0;
    assign btb_update_target = '0;
    assign btb_update_taken  = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({is_branch_ex, is_jump_ex, jb_target_src_ex, pc_ex, jb_target_ex,
                 branch_taken_ex});
    // verilog_format: on
  end

endmodule

`endif
