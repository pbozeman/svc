`ifndef SVC_RV_HAZARD_SV
`define SVC_RV_HAZARD_SV

`include "svc.sv"
`include "svc_unused.sv"

// Hazard detection unit for RISC-V pipeline
//
// Detects data and control hazards and sets control flags for resolution.
//
// For control hazards, this requires flushing. For data hazards, i.e. RAW,
// forwarding is a possibility, but on some fpga (e.g. hx8k), the combinatorial
// path is too long to get from WB to EX that there is a large fmax hit.
// Therefor, the hazard unit can optionally forward, or else, stall, dependent
// ops until the write has settled.
//
// In early tests on an hx8k, forwarding dropped fmax by almost 40% compared to
// stalling. Overall perf (CPI * clock_rate) is TBD for optimal tuning.
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
    parameter int MEM_TYPE    = 0,
    parameter int BPRED       = 0
) (
    // ID stage input registers
    input logic [4:0] rs1_id,
    input logic [4:0] rs2_id,
    input logic       rs1_used,
    input logic       rs2_used,
    input logic       is_branch_id,

    // EX stage control signals and destination
    input logic [4:0] rd_ex,
    input logic       reg_write_ex,
    input logic       is_load_ex,
    input logic       is_csr_ex,

    // MEM stage control signals and destination
    input logic [4:0] rd_mem,
    input logic       reg_write_mem,
    input logic       is_load_mem,
    input logic       is_csr_mem,

    // WB stage control signals and destination
    input logic [4:0] rd_wb,
    input logic       reg_write_wb,

    // Control flow changes (branches/jumps taken in EX stage)
    input logic pc_sel,

    // Branch prediction taken (ID stage)
    input logic pred_taken_id,

    // Branch misprediction (EX stage)
    input logic mispredicted_ex,

    // Hazard control outputs
    output logic pc_stall,
    output logic if_id_stall,
    output logic if_id_flush,
    output logic id_ex_stall,
    output logic id_ex_flush
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
      ex_hazard_rs1 = rs1_used && (rd_ex == rs1_id);
      ex_hazard_rs2 = rs2_used && (rd_ex == rs2_id);
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
      mem_hazard_rs1 = rs1_used && (rd_mem == rs1_id);
      mem_hazard_rs2 = rs2_used && (rd_mem == rs2_id);
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
        wb_hazard_rs1 = rs1_used && (rd_wb == rs1_id);
        wb_hazard_rs2 = rs2_used && (rd_wb == rs2_id);
      end
    end

    assign wb_hazard = wb_hazard_rs1 || wb_hazard_rs2;
  end

  //
  // Generate stall and flush signals
  //
  // Data hazards: We need to stall if there's a RAW hazard in EX, MEM, or
  // WB stage (unless regfile has internal forwarding for WB).
  //
  // When a data hazard is detected:
  // - Stall PC to prevent fetching new instructions
  // - Stall IF/ID to hold current instruction in decode
  // - Flush ID/EX to insert a bubble (NOP) in execute stage
  //
  // Control hazards: When a branch/jump is taken (pc_sel asserted in EX stage),
  // we need to flush the instructions already in the pipeline:
  // - Flush IF/ID (the instruction we just fetched shouldn't execute)
  // - Flush ID/EX (the instruction we just decoded shouldn't execute)
  //
  `include "svc_rv_defs.svh"

  logic data_hazard;

  if (FWD != 0) begin : g_forwarding
    //
    // Load-use hazard detection
    //
    // Load instructions produce result in MEM stage, but consumer
    // needs it in EX stage.
    //
    // For BRAM: Cannot forward (data not ready), must stall
    // For SRAM: Can forward (data ready in MEM), no stall needed
    //
    // CSR instructions produce result in WB stage, so we also cannot
    // forward from MEM→EX for CSR hazards. Stall for CSR-use too.
    //
    logic load_use_hazard;

    if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_bram_stall
      //
      // BRAM: Must stall on load-use hazards
      //
      assign load_use_hazard = ((is_load_ex || is_csr_ex) &&
                                (ex_hazard_rs1 || ex_hazard_rs2));
    end else begin : g_sram_no_stall
      //
      // SRAM: Load data forwarded, only stall on CSR-use
      //
      assign load_use_hazard = (is_csr_ex && (ex_hazard_rs1 || ex_hazard_rs2));
      `SVC_UNUSED({is_load_ex});
    end

    //
    // With forwarding enabled: only stall on unavoidable hazards
    //
    // - load_use_hazard: Load/CSR in EX can't forward to consumer in ID
    // - wb_hazard: Only if regfile doesn't have internal forwarding
    //
    // EX and MEM hazards (including branches) are resolved by forwarding
    //
    assign data_hazard = load_use_hazard || wb_hazard;

    `SVC_UNUSED({is_load_mem, is_csr_mem, is_branch_id, ex_hazard, mem_hazard});
  end else begin : g_no_forwarding
    //
    // Non-forwarding: stall on all hazards
    //
    assign data_hazard = ex_hazard || mem_hazard || wb_hazard;
    `SVC_UNUSED({is_load_ex, is_csr_ex, is_load_mem, is_csr_mem, is_branch_id});
  end

  assign pc_stall = data_hazard;
  assign if_id_stall = data_hazard;
  assign id_ex_stall = 1'b0;
  assign if_id_flush = pc_sel || mispredicted_ex ||
      (pred_taken_id && !data_hazard);
  assign id_ex_flush = data_hazard || pc_sel || mispredicted_ex;

  `SVC_UNUSED({BPRED});

endmodule

`endif
