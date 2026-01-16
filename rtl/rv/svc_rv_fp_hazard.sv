`ifndef SVC_RV_FP_HAZARD_SV
`define SVC_RV_FP_HAZARD_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// FP Hazard Detection Unit
//
// Detects data hazards for floating-point instructions. This module runs
// in parallel with the integer hazard unit and produces additional stall
// signals that are OR'd with the integer hazard signals.
//
// FP-specific hazards detected:
// - FP RAW (EX/MEM/WB): fp_rs1/fp_rs2/fp_rs3 matches fp_rd in later stages
//
// INT<->FP hazards (FMV.W.X, FCVT.S.W use integer rs1) are handled by
// the integer hazard unit since they use integer source registers.
//
// FP->INT hazards (FMV.X.W, FCVT.W.S write integer rd) are handled by
// the integer hazard unit since they write to integer destination.
//
module svc_rv_fp_hazard #(
    parameter int XLEN        = 32,
    parameter int FWD_REGFILE = 1,
    parameter int MEM_TYPE    = 0
) (
    //
    // FP register usage from ID stage
    //
    input logic [4:0] fp_rs1_id,
    input logic [4:0] fp_rs2_id,
    input logic [4:0] fp_rs3_id,
    input logic       fp_rs1_used_id,
    input logic       fp_rs2_used_id,
    input logic       fp_rs3_used_id,
    input logic       is_fp_mc_id,

    //
    // FP destinations in EX stage
    //
    input logic [4:0] fp_rd_ex,
    input logic       fp_reg_write_ex,
    input logic       is_fp_load_ex,
    input logic       is_fp_compute_ex,

    //
    // FP destinations in MEM stage
    //
    input logic [4:0] fp_rd_mem,
    input logic       fp_reg_write_mem,
    input logic       is_fp_load_mem,

    //
    // FP destinations in WB stage
    //
    input logic [4:0] fp_rd_wb,
    input logic       fp_reg_write_wb,

    //
    // Control flow (to gate hazards on flush)
    //
    input logic control_flush,

    //
    // Hazard outputs
    //
    output logic fp_data_hazard_id
);

  `include "svc_rv_defs.svh"

  //
  // EX stage hazard detection
  //
  // Check if any FP source register in ID matches the FP destination in EX
  //
  logic ex_hazard_fp_rs1;
  logic ex_hazard_fp_rs2;
  logic ex_hazard_fp_rs3;
  logic ex_hazard;

  always_comb begin
    ex_hazard_fp_rs1 = 1'b0;
    ex_hazard_fp_rs2 = 1'b0;
    ex_hazard_fp_rs3 = 1'b0;

    if (fp_reg_write_ex) begin
      ex_hazard_fp_rs1 = fp_rs1_used_id && (fp_rd_ex == fp_rs1_id);
      ex_hazard_fp_rs2 = fp_rs2_used_id && (fp_rd_ex == fp_rs2_id);
      ex_hazard_fp_rs3 = fp_rs3_used_id && (fp_rd_ex == fp_rs3_id);
    end
  end

  assign ex_hazard = ex_hazard_fp_rs1 || ex_hazard_fp_rs2 || ex_hazard_fp_rs3;

  //
  // MEM stage hazard detection
  //
  logic mem_hazard_fp_rs1;
  logic mem_hazard_fp_rs2;
  logic mem_hazard_fp_rs3;
  logic mem_hazard;

  always_comb begin
    mem_hazard_fp_rs1 = 1'b0;
    mem_hazard_fp_rs2 = 1'b0;
    mem_hazard_fp_rs3 = 1'b0;

    if (fp_reg_write_mem) begin
      mem_hazard_fp_rs1 = fp_rs1_used_id && (fp_rd_mem == fp_rs1_id);
      mem_hazard_fp_rs2 = fp_rs2_used_id && (fp_rd_mem == fp_rs2_id);
      mem_hazard_fp_rs3 = fp_rs3_used_id && (fp_rd_mem == fp_rs3_id);
    end
  end

  assign
      mem_hazard = mem_hazard_fp_rs1 || mem_hazard_fp_rs2 || mem_hazard_fp_rs3;

  //
  // WB stage hazard detection
  //
  // Only needed if FP regfile doesn't have internal forwarding
  //
  logic wb_hazard_fp_rs1;
  logic wb_hazard_fp_rs2;
  logic wb_hazard_fp_rs3;
  logic wb_hazard;

  if (FWD_REGFILE != 0) begin : g_wb_no_hazard
    assign wb_hazard_fp_rs1 = 1'b0;
    assign wb_hazard_fp_rs2 = 1'b0;
    assign wb_hazard_fp_rs3 = 1'b0;
    assign wb_hazard        = 1'b0;

    `SVC_UNUSED({
                fp_rd_wb,
                fp_reg_write_wb,
                wb_hazard_fp_rs1,
                wb_hazard_fp_rs2,
                wb_hazard_fp_rs3
                });
  end else begin : g_wb_hazard
    always_comb begin
      wb_hazard_fp_rs1 = 1'b0;
      wb_hazard_fp_rs2 = 1'b0;
      wb_hazard_fp_rs3 = 1'b0;

      if (fp_reg_write_wb) begin
        wb_hazard_fp_rs1 = fp_rs1_used_id && (fp_rd_wb == fp_rs1_id);
        wb_hazard_fp_rs2 = fp_rs2_used_id && (fp_rd_wb == fp_rs2_id);
        wb_hazard_fp_rs3 = fp_rs3_used_id && (fp_rd_wb == fp_rs3_id);
      end
    end

    assign wb_hazard = wb_hazard_fp_rs1 || wb_hazard_fp_rs2 || wb_hazard_fp_rs3;
  end

  //
  // Data hazard output
  //
  // Stall on all FP RAW hazards - no FP forwarding
  //
  assign fp_data_hazard_id = (ex_hazard || mem_hazard || wb_hazard) &&
      !control_flush;

  `SVC_UNUSED({is_fp_load_ex, is_fp_load_mem, is_fp_compute_ex, MEM_TYPE,
               is_fp_mc_id});

endmodule

`endif
