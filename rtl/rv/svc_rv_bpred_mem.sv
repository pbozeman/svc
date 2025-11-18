`ifndef SVC_RV_BPRED_MEM_SV
`define SVC_RV_BPRED_MEM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Branch Prediction - MEM Stage
//
// Implements JALR misprediction detection one cycle after EX.
//
// TIMING OPTIMIZATION: JALR misprediction detection moved from EX to MEM
// stage to break critical path. In EX stage, computing the JALR target
// requires forwarding → ALU → target computation. Comparing this target
// with the predicted target in the same cycle created a long combinational
// path that prevented meeting timing.
//
// By registering the computed target and performing the comparison in MEM
// stage, we break this path. The cost is one extra cycle of misprediction
// penalty for incorrect JALR predictions, but correct predictions (the
// common case with RAS) still have zero penalty.
//
module svc_rv_bpred_mem #(
    parameter int XLEN       = 32,
    parameter int BPRED      = 0,
    parameter int RAS_ENABLE = 0
) (
    //
    // JALR analysis from MEM stage
    //
    input logic            is_jalr_mem,
    input logic            bpred_taken_mem,
    input logic [XLEN-1:0] jb_target_mem,
    input logic [XLEN-1:0] pred_target_mem,

    //
    // Misprediction detection output
    //
    output logic jalr_mispredicted_mem,

    //
    // PC control output
    //
    output logic pc_sel_jalr_mem
);

  //
  // JALR misprediction detection
  //
  if (BPRED != 0 && RAS_ENABLE != 0) begin : g_jalr_mispred
    //
    // JALR mispredicted if: not predicted OR predicted target doesn't match actual
    //
    assign jalr_mispredicted_mem = is_jalr_mem &&
        (!bpred_taken_mem || (pred_target_mem != jb_target_mem));

    //
    // Redirect on JALR misprediction
    //
    assign pc_sel_jalr_mem = jalr_mispredicted_mem;

  end else if (BPRED != 0) begin : g_jalr_no_ras
    //
    // Without RAS, always redirect on JALR (not predicted)
    //
    assign jalr_mispredicted_mem = is_jalr_mem;
    assign pc_sel_jalr_mem       = is_jalr_mem;

    `SVC_UNUSED({bpred_taken_mem, jb_target_mem, pred_target_mem});

  end else begin : g_no_jalr_mispred
    //
    // Without BPRED, no misprediction detection (handled elsewhere)
    //
    assign jalr_mispredicted_mem = 1'b0;
    assign pc_sel_jalr_mem       = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({is_jalr_mem, bpred_taken_mem, pred_target_mem,
                 jb_target_mem});
    // verilog_format: on
  end

endmodule

`endif
