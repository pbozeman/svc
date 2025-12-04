`ifndef SVC_RV_IF_BRAM_SV
`define SVC_RV_IF_BRAM_SV

`include "svc.sv"

//
// BRAM instruction fetch pipeline adapter
//
// Handles timing adjustments needed for BRAM's 1-cycle read latency:
// 1. PC buffering: Extra register stage to align PC with 2-cycle instruction latency
// 2. Extended flush: Delays flush signal to handle stale BRAM output after branches
//
// BRAM timing:
// - Cycle 0: PC sent to BRAM
// - Cycle 1: BRAM outputs instruction (registered)
// - Cycle 2: Instruction captured in instr_id
//
// Total instruction latency = 2 cycles, but IF/ID register provides only 1 cycle
// of PC delay, so this module adds one more cycle of PC buffering.
//
module svc_rv_if_bram #(
    parameter int XLEN
) (
    input logic clk,
    input logic rst_n,

    //
    // Flush control
    //
    input logic if_id_flush,

    //
    // Ready/valid interface
    //
    input logic m_ready,

    //
    // PC inputs from fetch stage
    //
    input logic [XLEN-1:0] pc,
    input logic [XLEN-1:0] pc_plus4,

    //
    // Instruction input from BRAM
    //
    input logic [31:0] instr_bram,

    //
    // Outputs to decode stage
    //
    output logic [XLEN-1:0] pc_to_if_id,
    output logic [XLEN-1:0] pc_plus4_to_if_id,
    output logic [    31:0] instr_id
);

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc_buf;
  logic [XLEN-1:0] pc_plus4_buf;
  logic            flush_extend;

  //
  // PC buffering to match instruction latency
  //
  // BRAM has 2 cycles of instruction latency (BRAM output + instr_id register)
  // but IF/ID register only provides 1 cycle for PC
  // So we need to add one more cycle of PC buffering
  //
  // NOTE: PC buffer continues tracking even during flushes. Only instructions
  // are flushed to NOP, PC values must remain correct for pipeline tracking.
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc_buf       <= '0;
      pc_plus4_buf <= '0;
    end else if (m_ready) begin
      pc_buf       <= pc;
      pc_plus4_buf <= pc_plus4;
    end
  end

  //
  // Output buffered PC values
  //
  assign pc_to_if_id       = pc_buf;
  assign pc_plus4_to_if_id = pc_plus4_buf;

  //
  // Extended flush for BRAM
  //
  // With BRAM's 1-cycle latency, when a branch is taken the BRAM output
  // contains a stale instruction for one more cycle. We need to extend the
  // flush signal to cover this case and insert NOPs for 2 cycles total.
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      flush_extend <= 1'b0;
    end else begin
      flush_extend <= if_id_flush;
    end
  end

  //
  // Instruction path with stall support and extended flush
  //
  always_ff @(posedge clk) begin
    if (!rst_n || if_id_flush || flush_extend) begin
      instr_id <= I_NOP;
    end else if (m_ready) begin
      instr_id <= instr_bram;
    end
  end

endmodule

`endif
