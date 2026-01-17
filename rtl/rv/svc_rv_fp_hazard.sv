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
// - FP Load-Use: FLW in EX, consumer in ID (data not ready)
// - FP Multi-cycle: FDIV/FSQRT in progress (handled via op_active_ex)
//
// INT<->FP hazards (FMV.W.X, FCVT.S.W use integer rs1) are handled by
// the integer hazard unit since they use integer source registers.
//
// FP->INT hazards (FMV.X.W, FCVT.W.S write integer rd) are handled by
// the integer hazard unit since they write to integer destination.
//
module svc_rv_fp_hazard #(
    parameter int XLEN        = 32,
    parameter int FWD_FP      = 1,
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
  if (FWD_FP != 0) begin : g_fp_forwarding
    //
    // With FP forwarding enabled: only stall on unavoidable hazards
    //
    // FP load-use hazard: FLW in EX, FP consumer in ID
    // - Data not ready until WB (BRAM) or MEM (SRAM)
    //
    // FP compute result: Available in EX, can forward to ID
    //
    logic fp_load_use_ex;
    logic fp_load_use_mem;
    logic fp_load_use_hazard;

    if (MEM_TYPE != MEM_TYPE_SRAM) begin : g_bram_stall
      //
      // BRAM/Cache: FP load data not ready until WB, must stall for EX and MEM
      //
      assign fp_load_use_ex     = is_fp_load_ex && ex_hazard;
      assign fp_load_use_mem    = is_fp_load_mem && mem_hazard;
      assign fp_load_use_hazard = fp_load_use_ex || fp_load_use_mem;
    end else begin : g_sram_stall
      //
      // SRAM: FP load data ready in MEM, only stall for EX
      //
      assign fp_load_use_ex     = is_fp_load_ex && ex_hazard;
      assign fp_load_use_mem    = 1'b0;
      assign fp_load_use_hazard = fp_load_use_ex;

      `SVC_UNUSED(is_fp_load_mem);
    end

    //
    // Multi-cycle FP op hazard detection
    //
    // FDIV/FSQRT do not receive forwarding (svc_rv_fp_fwd_ex disables it when
    // is_fp_mc_ex=1). If an FP MC op in ID depends on EX or MEM results, we
    // must stall until the result reaches the regfile (via WB→ID forwarding).
    //
    logic fp_mc_hazard;
    assign fp_mc_hazard = is_fp_mc_id && (ex_hazard || mem_hazard);

    //
    // With forwarding: only stall on load-use and WB hazards (if no regfile fwd)
    // Regular EX/MEM hazards resolved by FP forwarding unit
    //
    assign fp_data_hazard_id = (fp_load_use_hazard || fp_mc_hazard ||
                                wb_hazard) && !control_flush;

    `SVC_UNUSED(is_fp_compute_ex);
  end else begin : g_no_fp_forwarding
    //
    // Without FP forwarding: stall on all FP RAW hazards
    //
    assign fp_data_hazard_id = (ex_hazard || mem_hazard || wb_hazard) &&
        !control_flush;

    `SVC_UNUSED(
        {is_fp_load_ex, is_fp_load_mem, is_fp_compute_ex, MEM_TYPE, is_fp_mc_id
        });
  end

endmodule

`endif
