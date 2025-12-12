`ifndef SVC_RV_HAZARD_SV
`define SVC_RV_HAZARD_SV

`include "svc.sv"
`include "svc_unused.sv"

// Hazard detection unit for RISC-V pipeline
//
// Detects data and control hazards and sets control flags for resolution.
//
// Control hazards are resolved by flushing the pipeline. For data hazards
// (RAW dependencies), this unit outputs the data_hazard_id signal which the ID
// stage uses to gate m_valid and s_ready. This implements backpressure-based
// stalling through the ready/valid interface rather than centralized stall
// signals. Actual data forwarding, when enabled, is handled by a separate
// forwarding unit in the EX stage.
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
    parameter int FWD_REGFILE,
    parameter int FWD,
    parameter int MEM_TYPE,
    parameter int PC_REG      = 0
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

    // Branch/JALR misprediction redirect (MEM stage)
    input logic redirect_valid_mem,

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

    //
    // Registered redirect pending (from stage_pc)
    //
    input logic redirect_pending_if,

    // Hazard control outputs
    output logic data_hazard_id,
    output logic if_id_flush,
    output logic id_ex_flush,
    output logic ex_mem_flush
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
  // Data hazard output and flush signal generation
  //
  // Data hazards: Detection depends on FWD parameter:
  // - FWD=0: Detect all RAW hazards (EX, MEM, WB stages)
  // - FWD=1: Only detect unavoidable hazards (load-use, CSR-use, and WB if
  //          regfile lacks internal forwarding)
  //
  // The data_hazard_id signal is output to the ID stage, which uses it to:
  // - Gate m_valid low (don't present dependent instruction to EX)
  // - Gate s_ready low (backpressure IF to prevent new fetches)
  //
  // On control flow changes (redirect, misprediction), data_hazard_id is cleared
  // because the instruction causing the hazard is being flushed. This allows
  // the pipeline to take the redirect without being blocked by stall.
  //
  // Control hazards: When a branch/jump is taken (pc_sel asserted in EX stage),
  // we need to flush the instructions already in the pipeline:
  // - Flush IF/ID (the instruction we just fetched shouldn't execute)
  // - Flush ID/EX (the instruction we just decoded shouldn't execute)
  //
  `include "svc_rv_defs.svh"

  //
  // Control flow change detection (defined early for use in data_hazard_id gating)
  //
  logic pc_redirect;
  logic control_flush;

  assign pc_redirect   = (pc_sel == PC_SEL_REDIRECT);
  assign control_flush = pc_redirect || redirect_valid_mem;

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
    // On control_flush, clear data_hazard_id so redirect can proceed.
    //
    assign data_hazard_id = (load_use_hazard || wb_hazard) && !control_flush;

    `SVC_UNUSED({ex_hazard, mem_hazard});
  end else begin : g_no_forwarding
    //
    // Non-forwarding: stall on all hazards
    //
    // On control_flush, clear data_hazard_id so redirect can proceed.
    //
    assign data_hazard_id = (ex_hazard || mem_hazard || wb_hazard) &&
        !control_flush;
    `SVC_UNUSED({is_load_ex, is_csr_ex, is_m_ex, mem_read_mem, res_src_mem});
  end


  //
  // Flush logic
  //
  // if_id_flush: Flush when PC redirection occurs (branches/jumps or prediction)
  //
  // For BTB predictions (IF stage): Do NOT flush - the branch instruction must
  // flow through the pipeline to EX for validation.
  //
  // For static predictions (ID stage): DO flush - the sequential instruction
  // after the branch was already fetched and is incorrect.
  //
  // Suppress prediction flush when stalling (data_hazard_id or op_active_ex),
  // since the predicted instruction in ID hasn't advanced yet.
  //
  // id_ex_flush: Flush on control flow changes (redirects, mispredictions).
  // Data hazards no longer cause flush - ID stage gates m_valid instead.
  //
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
  // Only flush if pipeline is advancing (!data_hazard_id && !op_active_ex).
  //
  logic pred_flush;

  assign pc_predicted = (pc_sel == PC_SEL_PREDICTED);
  assign pred_flush = (pc_predicted && (!btb_pred_taken || ras_pred_taken) &&
                       !data_hazard_id && !op_active_ex);

  if (PC_REG != 0) begin : g_registered_flush
    //
    // Extended flush for registered redirect
    //
    // When PC_REG=1, the redirect takes effect one cycle late.
    // The instruction fetched during the redirect cycle (wrong path) must
    // be flushed when redirect_pending_if is asserted.
    //
    assign if_id_flush = control_flush || pred_flush || redirect_pending_if;
    assign id_ex_flush = control_flush || redirect_pending_if;

  end else begin : g_immediate_flush
    //
    // Current logic unchanged
    //
    assign if_id_flush = control_flush || pred_flush;
    assign id_ex_flush = control_flush;

    `SVC_UNUSED(redirect_pending_if);
  end

  assign ex_mem_flush = redirect_valid_mem || op_active_ex;

endmodule

`endif
