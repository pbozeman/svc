`ifndef SVC_RV_HAZARD_SV
`define SVC_RV_HAZARD_SV

`include "svc.sv"

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
module svc_rv_hazard (

    // ID stage input registers
    input logic [4:0] rs1_id,
    input logic [4:0] rs2_id,

    // EX stage control signals and destination
    input logic [4:0] rd_ex,
    input logic       reg_write_ex,

    // MEM stage control signals and destination
    input logic [4:0] rd_mem,
    input logic       reg_write_mem,

    // WB stage control signals and destination
    input logic [4:0] rd_wb,
    input logic       reg_write_wb,

    // Control flow changes (branches/jumps taken in EX stage)
    input logic pc_sel,

    // Hazard control outputs
    output logic pc_stall,
    output logic if_id_stall,
    output logic if_id_flush,
    output logic id_ex_flush
);

  //
  // Detect if ID stage reads from EX stage destination
  //
  logic ex_hazard_rs1;
  logic ex_hazard_rs2;
  logic ex_hazard;

  assign ex_hazard_rs1 = reg_write_ex && (rd_ex != 5'd0) && (rd_ex == rs1_id);
  assign ex_hazard_rs2 = reg_write_ex && (rd_ex != 5'd0) && (rd_ex == rs2_id);
  assign ex_hazard     = ex_hazard_rs1 || ex_hazard_rs2;

  //
  // Detect if ID stage reads from MEM stage destination
  //
  logic mem_hazard_rs1;
  logic mem_hazard_rs2;
  logic mem_hazard;

  assign mem_hazard_rs1 = (reg_write_mem && (rd_mem != 5'd0) &&
                           (rd_mem == rs1_id));
  assign mem_hazard_rs2 = (reg_write_mem && (rd_mem != 5'd0) &&
                           (rd_mem == rs2_id));
  assign mem_hazard = mem_hazard_rs1 || mem_hazard_rs2;

  //
  // Detect if ID stage reads from WB stage destination
  //
  logic wb_hazard_rs1;
  logic wb_hazard_rs2;
  logic wb_hazard;

  assign wb_hazard_rs1 = reg_write_wb && (rd_wb != 5'd0) && (rd_wb == rs1_id);
  assign wb_hazard_rs2 = reg_write_wb && (rd_wb != 5'd0) && (rd_wb == rs2_id);
  assign wb_hazard     = wb_hazard_rs1 || wb_hazard_rs2;

  //
  // Generate stall and flush signals
  //
  // Data hazards: We need to stall if there's a RAW hazard in EX, MEM, or WB stage.
  // WB stage also causes hazards because the regfile write is synchronous
  // and the data won't be visible to ID stage reads in the same cycle.
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
  logic data_hazard;

  assign data_hazard = ex_hazard || mem_hazard || wb_hazard;

  assign pc_stall    = data_hazard;
  assign if_id_stall = data_hazard;
  assign if_id_flush = pc_sel;
  assign id_ex_flush = data_hazard || pc_sel;

endmodule

`endif
