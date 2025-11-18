`ifndef SVC_RV_HAZARD_SV
`define SVC_RV_HAZARD_SV

`include "svc.sv"
`include "svc_unused.sv"

// Hazard detection unit for RISC-V pipeline
//
// Detects data and control hazards and sets control flags for resolution.
//
// Control hazards are resolved by flushing the pipeline. For data hazards
// (RAW dependencies), this unit detects hazards and generates stall signals.
// Actual data forwarding, when enabled, is handled by a separate forwarding
// unit in the EX stage.
//
// FWD parameter controls hazard detection behavior:
// - FWD=0: Stall on all RAW hazards (EX, MEM, WB stages)
// - FWD=1: Assume external forwarding unit exists, only stall on hazards that
//          cannot be forwarded (load-use, CSR-use, WB if no regfile forwarding)
//
// In early tests on an hx8k, a design with forwarding achieved better CPI but
// lower fmax (40% drop), while stalling had worse CPI but higher fmax. The
// optimal choice depends on the specific workload and FPGA target.
//
// NOTE: This unit only detects register-based RAW hazards. It does NOT detect
// memory address hazards (e.g., store followed by load to the same address
// through different base registers). The current design assumes single-cycle
// memory operations where stores complete before subsequent loads execute.
// For multi-cycle memory (caches, slow SRAM, external memory), additional
// hazard detection would be needed:
// - Store buffer with address comparison and forwarding
// - Memory ordering unit to enforce load/store dependencies
// - Stall logic based on memory ready signals
//
module svc_rv_hazard #(
    parameter int FWD_REGFILE = 1,
    parameter int FWD         = 0,
    parameter int MEM_TYPE    = 0
) (
    // ID stage input registers
    input logic [4:0] rs1_id,
    input logic [4:0] rs2_id,
    input logic       rs1_used_id,
    input logic       rs2_used_id,

    // EX stage control signals and destination
    input logic [4:0] rd_ex,
    input logic       reg_write_ex,
    input logic       is_load_ex,
    input logic       is_csr_ex,
    input logic       is_m_ex,
    input logic       op_active_ex,

    // MEM stage control signals and destination
    input logic [4:0] rd_mem,
    input logic       reg_write_mem,
    input logic       mem_read_mem,
    input logic [2:0] res_src_mem,

    // WB stage control signals and destination
    input logic [4:0] rd_wb,
    input logic       reg_write_wb,

    // PC selection mode from EX stage
    input logic [1:0] pc_sel,

    // Branch misprediction (EX stage)
    input logic mispredicted_ex,

    //
    // Prediction indicators (IF stage, synchronous with PC mux)
    //
    // btb_pred_taken: BTB predicted (early prediction, no flush needed)
    // ras_pred_taken: RAS predicted (late prediction, flush needed)
    //
    // These signals indicate whether the current PC_SEL_PREDICTED came from BTB
    // or RAS in this cycle. They must be IF-synchronous (not ID-aligned) to
    // correctly control flush logic.
    //
    input logic btb_pred_taken,
    input logic ras_pred_taken,

    // Hazard control outputs
    output logic pc_stall,
    output logic if_id_stall,
    output logic if_id_flush,
    output logic id_ex_stall,
    output logic id_ex_flush,
    output logic ex_mem_stall,
    output logic mem_wb_stall
);

  //
  // Detect if ID stage reads from EX stage destination
  //
  logic ex_hazard_rs1;
  logic ex_hazard_rs2;
  logic ex_hazard;

  always_comb begin
    ex_hazard_rs1 = 1'b0;
    ex_hazard_rs2 = 1'b0;

    if (reg_write_ex && rd_ex != 5'd0) begin
      ex_hazard_rs1 = rs1_used_id && (rd_ex == rs1_id);
      ex_hazard_rs2 = rs2_used_id && (rd_ex == rs2_id);
    end
  end

  assign ex_hazard = ex_hazard_rs1 || ex_hazard_rs2;

  //
  // Detect if ID stage reads from MEM stage destination
  //
  logic mem_hazard_rs1;
  logic mem_hazard_rs2;
  logic mem_hazard;

  always_comb begin
    mem_hazard_rs1 = 1'b0;
    mem_hazard_rs2 = 1'b0;

    if (reg_write_mem && rd_mem != 5'd0) begin
      mem_hazard_rs1 = rs1_used_id && (rd_mem == rs1_id);
      mem_hazard_rs2 = rs2_used_id && (rd_mem == rs2_id);
    end
  end

  assign mem_hazard = mem_hazard_rs1 || mem_hazard_rs2;

  //
  // WB hazard detection (conditional based on regfile forwarding)
  //
  // If the regfile has internal forwarding, WB hazards are handled there.
  // Otherwise, we need to detect and stall for WB stage hazards.
  //
  logic wb_hazard_rs1;
  logic wb_hazard_rs2;
  logic wb_hazard;

  if (FWD_REGFILE != 0) begin : g_wb_no_hazard
    assign wb_hazard_rs1 = 1'b0;
    assign wb_hazard_rs2 = 1'b0;
    assign wb_hazard     = 1'b0;

    `SVC_UNUSED({rd_wb, reg_write_wb, wb_hazard_rs1, wb_hazard_rs2});
  end else begin : g_wb_hazard
    always_comb begin
      wb_hazard_rs1 = 1'b0;
      wb_hazard_rs2 = 1'b0;

      if (reg_write_wb && rd_wb != 5'd0) begin
        wb_hazard_rs1 = rs1_used_id && (rd_wb == rs1_id);
        wb_hazard_rs2 = rs2_used_id && (rd_wb == rs2_id);
      end
    end

    assign wb_hazard = wb_hazard_rs1 || wb_hazard_rs2;
  end

  //
  // Generate stall and flush signals
  //
  // Data hazards: Stall behavior depends on FWD parameter:
  // - FWD=0: Stall on all RAW hazards (EX, MEM, WB stages)
  // - FWD=1: Only stall on unavoidable hazards (load-use, CSR-use, and WB if
  //          regfile lacks internal forwarding)
  //
  // When a data hazard is detected:
  // - Stall PC to prevent fetching new instructions
  // - Stall IF/ID to hold current instruction in decode
  // - Flush ID/EX to insert a bubble (NOP) in execute stage
  //   (unless multi-cycle operation is active, then ID/EX is stalled instead)
  //
  // Control hazards: When a branch/jump is taken (pc_sel asserted in EX stage),
  // we need to flush the instructions already in the pipeline:
  // - Flush IF/ID (the instruction we just fetched shouldn't execute)
  // - Flush ID/EX (the instruction we just decoded shouldn't execute)
  //
  `include "svc_rv_defs.svh"

  logic data_hazard;

  if (FWD != 0) begin : g_external_forwarding
    //
    // Decode result source to determine if instruction in MEM is a CSR or M extension
    //
    logic is_csr_mem;
    logic is_m_result_mem;

    assign is_csr_mem      = (res_src_mem == RES_CSR);
    assign is_m_result_mem = (res_src_mem == RES_M);

    //
    // Load-use hazard detection
    //
    // TIMING NOTE: WB→EX forwarding was removed to improve timing (reduces
    // EX stage mux depth). Instead, forwarding happens earlier at ID stage:
    // - MEM→ID: Forwards ALU results (cheap, data ready in MEM)
    // - WB→ID: Forwards all results including loads (before ID→EX register)
    //
    // This moves expensive WB forwarding path off EX critical path, but
    // requires more aggressive stall detection for loads on BRAM:
    //
    // For BRAM loads:
    // - EX stage: Data not computed yet → must stall
    // - MEM stage: Data being read but not ready → must stall until WB
    // - WB stage: Data ready → WB→ID can forward (no stall)
    //
    // For SRAM loads:
    // - MEM stage: Data ready → MEM→ID can forward (no stall)
    //
    // CSR results only ready in WB stage, similar to BRAM loads.
    //
    // TODO: Consider making WB→EX configurable for timing-relaxed designs
    // where the extra mux depth is acceptable.
    //
    logic load_use_hazard;
    logic load_use_ex;
    logic load_use_mem;

    if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_bram_stall
      //
      // BRAM: Must stall on load-use hazards in EX and MEM stages
      //
      // Load/CSR/M-ext in EX, consumer in ID: Data not computed yet
      //
      assign load_use_ex = ((is_load_ex || is_csr_ex || is_m_ex) &&
                            (ex_hazard_rs1 || ex_hazard_rs2));

      //
      // Load/CSR/M-ext in MEM, consumer in ID: Data not ready yet (BRAM latency)
      //
      // MEM→ID forwarding skips loads, CSRs, and M extension results (checked via
      // !is_load_mem && !is_csr_mem && !is_m_result_mem in svc_rv_fwd_id).
      // Must stall until result reaches WB where WB→ID can forward it.
      //
      assign load_use_mem = ((mem_read_mem || is_csr_mem || is_m_result_mem) &&
                             (mem_hazard_rs1 || mem_hazard_rs2));

      assign load_use_hazard = load_use_ex || load_use_mem;
    end else begin : g_sram_no_stall
      //
      // SRAM: Load data forwarded from MEM stage, only stall on CSR-use and M-ext-use
      //
      // CSR/M-ext in EX, consumer in ID: Data not computed yet
      //
      assign load_use_ex = ((is_csr_ex || is_m_ex) &&
                            (ex_hazard_rs1 || ex_hazard_rs2));

      //
      // CSR/M-ext in MEM, consumer in ID: Data not ready yet
      //
      // SRAM loads are ready in MEM stage and can be forwarded, but CSRs and
      // M extension results are not ready until WB. Must stall until result
      // reaches WB where WB→ID can forward it.
      //
      assign load_use_mem = ((is_csr_mem || is_m_result_mem) &&
                             (mem_hazard_rs1 || mem_hazard_rs2));

      assign load_use_hazard = load_use_ex || load_use_mem;

      `SVC_UNUSED({is_load_ex, mem_read_mem});
    end

    //
    // With forwarding enabled: only stall on unavoidable hazards
    //
    // - load_use_hazard: Load/CSR in EX can't forward to consumer in ID
    // - wb_hazard: Only if regfile doesn't have internal forwarding
    //
    // Regular EX and MEM stage RAW hazards are assumed to be resolved by the
    // external forwarding unit (in the EX stage), so they don't cause stalls.
    //
    assign data_hazard = load_use_hazard || wb_hazard;

    `SVC_UNUSED({ex_hazard, mem_hazard});
  end else begin : g_no_forwarding
    //
    // Non-forwarding: stall on all hazards
    //
    assign data_hazard = ex_hazard || mem_hazard || wb_hazard;
    `SVC_UNUSED({is_load_ex, is_csr_ex, is_m_ex, mem_read_mem, res_src_mem});
  end

  //
  // Multi-cycle EX operation stall
  //
  // When op_active_ex is asserted, a multi-cycle operation (e.g., division)
  // is executing in the EX stage. Freeze the entire pipeline:
  // - Stall PC, IF/ID, ID/EX (prevent new instructions from entering EX)
  // - Stall EX/MEM, MEM/WB (prevent incomplete result from advancing)
  // - When operation completes (op_active_ex drops), all stalls release
  //   and the completed result flows normally through MEM→WB→regfile
  //
  // Note: For ID/EX stage, we use STALL during multi-cycle operations but
  // FLUSH for data hazards. This is why id_ex_stall only checks op_active_ex.
  //
  // Don't stall on data hazards when redirecting (pc_redirect or misprediction),
  // since the hazardous instruction will be flushed anyway.
  //
  logic stall_disable;

  assign stall_disable = pc_redirect || mispredicted_ex;

  assign pc_stall      = (data_hazard || op_active_ex) && !stall_disable;
  assign if_id_stall   = (data_hazard || op_active_ex) && !stall_disable;
  assign id_ex_stall   = op_active_ex;
  assign ex_mem_stall  = op_active_ex;
  assign mem_wb_stall  = op_active_ex;

  //
  // Flush logic with stall interaction
  //
  // if_id_flush: Flush when PC redirection occurs (branches/jumps or prediction)
  //
  // For BTB predictions (IF stage): Do NOT flush - the branch instruction must
  // flow through the pipeline to EX for validation.
  //
  // For static predictions (ID stage): DO flush - the sequential instruction
  // after the branch was already fetched and is incorrect.
  //
  // Suppress prediction flush when stalling, since the predicted instruction
  // in ID hasn't advanced yet.
  //
  // id_ex_flush: For data hazards, use flush (insert bubble) unless a
  // multi-cycle operation is active (then use stall to preserve EX state).
  //
  logic pc_redirect;
  logic pc_predicted;

  //
  // Prediction flush: ID stage predicted a branch/jump
  //
  // Flush is needed when the instruction from the sequential PC (already
  // fetched in IF stage) must be discarded due to a prediction redirect:
  //
  // - Static: ID decodes JAL or makes BTFNT prediction (flush needed)
  // - RAS: Return Address Stack predicts JALR return (flush needed)
  // - BTB: Branch Target Buffer predicts early in IF (NO flush needed)
  //
  // BTB predictions happen early enough that the sequential instruction hasn't
  // been fetched yet. But RAS predictions happen when JALR is in ID, after
  // the sequential instruction is already in the pipeline.
  //
  // Only flush if pipeline is advancing (!data_hazard && !op_active_ex).
  //
  logic pred_flush;

  assign pc_redirect = (pc_sel == PC_SEL_REDIRECT);
  assign pc_predicted = (pc_sel == PC_SEL_PREDICTED);
  assign pred_flush = (pc_predicted && (!btb_pred_taken || ras_pred_taken) &&
                       !data_hazard && !op_active_ex);

  assign if_id_flush = (pc_redirect || mispredicted_ex || pred_flush);
  assign id_ex_flush = ((data_hazard && !op_active_ex) || pc_redirect ||
                        mispredicted_ex);

endmodule

`endif
