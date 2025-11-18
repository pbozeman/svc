`ifndef SVC_RV_STAGE_IF_SRAM_SV
`define SVC_RV_STAGE_IF_SRAM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Instruction Fetch - SRAM Implementation
//
// SRAM has 0-cycle read latency. Instructions are available immediately
// in the same cycle the address is presented. No PC or BTB buffering needed.
//
module svc_rv_stage_if_sram #(
    parameter int XLEN      = 32,
    parameter int PIPELINED = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // PC input (from wrapper)
    //
    input logic [XLEN-1:0] pc,

    //
    // Hazard control
    //
    input logic if_id_stall,
    input logic if_id_flush,

    //
    // BTB prediction signals
    //
    input logic            btb_hit_if,
    input logic            btb_pred_taken_if,
    input logic [XLEN-1:0] btb_target_if,

    //
    // RAS prediction signals
    //
    input logic            ras_valid_if,
    input logic [XLEN-1:0] ras_target_if,

    //
    // Instruction memory interface
    //
    output logic        imem_ren,
    output logic [31:0] imem_raddr,
    input  logic [31:0] imem_rdata,

    //
    // Outputs (instr_id drives module output directly, others to IF/ID register)
    //
    output logic [    31:0] instr_id,
    output logic [XLEN-1:0] pc_to_if_id,
    output logic [XLEN-1:0] pc_plus4_to_if_id,
    output logic            btb_hit_to_if_id,
    output logic            btb_pred_taken_to_if_id,
    output logic [XLEN-1:0] btb_target_to_if_id,
    output logic            ras_valid_to_if_id,
    output logic [XLEN-1:0] ras_target_to_if_id
);

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc_plus4;
  logic [    31:0] instr;

  assign pc_plus4   = pc + 4;

  //
  // Instruction memory interface
  //
  // SRAM: Always enabled
  //
  assign imem_raddr = pc;
  assign instr      = imem_rdata;
  assign imem_ren   = 1'b1;

  //
  // Instruction path
  //
  // Optional instruction buffering for pipelined mode
  //
  if (PIPELINED != 0) begin : g_registered
    logic [31:0] instr_buf;

    always_ff @(posedge clk) begin
      if (!rst_n || if_id_flush) begin
        instr_buf <= I_NOP;
      end else if (!if_id_stall) begin
        instr_buf <= instr;
      end
    end

    assign instr_id = instr_buf;
  end else begin : g_passthrough
    assign instr_id = instr;

    `SVC_UNUSED({clk, rst_n, if_id_stall, if_id_flush})
  end

  //
  // PC, BTB, and RAS passthrough
  //
  // SRAM: No buffering needed, values align with instruction
  //
  assign pc_to_if_id             = pc;
  assign pc_plus4_to_if_id       = pc_plus4;
  assign btb_hit_to_if_id        = btb_hit_if;
  assign btb_pred_taken_to_if_id = btb_pred_taken_if;
  assign btb_target_to_if_id     = btb_target_if;
  assign ras_valid_to_if_id      = ras_valid_if;
  assign ras_target_to_if_id     = ras_target_if;

endmodule

`endif
