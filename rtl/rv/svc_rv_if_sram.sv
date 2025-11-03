`ifndef SVC_RV_IF_SRAM_SV
`define SVC_RV_IF_SRAM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// SRAM instruction fetch pipeline adapter
//
// Handles instruction registration for SRAM's 0-cycle read latency:
// - PIPELINED=1: Register instruction with stall/flush support
// - PIPELINED=0: Pass through combinationally
//
// SRAM timing:
// - Cycle 0: PC sent to SRAM, instruction available same cycle (combinational)
//
module svc_rv_if_sram #(
    parameter int XLEN      = 32,
    parameter int PIPELINED = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // Stall and flush controls
    //
    input logic if_id_stall,
    input logic if_id_flush,

    //
    // PC inputs from fetch stage (pass through to IF/ID register)
    //
    input logic [XLEN-1:0] pc,
    input logic [XLEN-1:0] pc_plus4,

    //
    // Instruction input from SRAM
    //
    input logic [31:0] instr_sram,

    //
    // Outputs to decode stage
    //
    output logic [XLEN-1:0] pc_to_if_id,
    output logic [XLEN-1:0] pc_plus4_to_if_id,
    output logic [    31:0] instr_id
);

  `include "svc_rv_defs.svh"

  //
  // For SRAM: Pass PC directly to IF/ID register
  //
  assign pc_to_if_id       = pc;
  assign pc_plus4_to_if_id = pc_plus4;

  //
  // Instruction path
  //
  if (PIPELINED != 0) begin : g_registered
    always_ff @(posedge clk) begin
      if (!rst_n || if_id_flush) begin
        instr_id <= I_NOP;
      end else if (!if_id_stall) begin
        instr_id <= instr_sram;
      end
    end
  end else begin : g_passthrough
    assign instr_id = instr_sram;

    `SVC_UNUSED({clk, rst_n, if_id_stall, if_id_flush});
  end

endmodule

`endif
