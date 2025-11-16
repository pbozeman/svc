`ifndef SVC_RV_STAGE_IF_BRAM_SV
`define SVC_RV_STAGE_IF_BRAM_SV

`include "svc.sv"

//
// RISC-V Instruction Fetch - BRAM Implementation
//
// BRAM has 1-cycle read latency. Instructions become available one cycle
// after the address is presented. This requires PC and BTB prediction
// buffering to align with the delayed instruction.
//
module svc_rv_stage_if_bram #(
    parameter int XLEN = 32
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
    input logic pc_stall,
    input logic if_id_stall,
    input logic if_id_flush,

    //
    // BTB prediction signals
    //
    input logic            btb_hit_if,
    input logic            btb_pred_taken_if,
    input logic [XLEN-1:0] btb_target_if,

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
    output logic [XLEN-1:0] btb_target_to_if_id
);

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc_plus4;
  logic [XLEN-1:0] pc_buf;
  logic [XLEN-1:0] pc_plus4_buf;
  logic            btb_hit_buf;
  logic            btb_pred_taken_buf;
  logic [XLEN-1:0] btb_target_buf;
  logic            flush_extend;
  logic [    31:0] instr;
  logic [    31:0] instr_buf;

  assign pc_plus4   = pc + 4;

  //
  // Instruction memory interface
  //
  // BRAM: Gated with PC stall to hold output
  //
  assign imem_raddr = pc;
  assign instr      = imem_rdata;
  assign imem_ren   = !pc_stall;

  //
  // PC and BTB prediction buffering to match instruction latency
  //
  // BRAM has 1-cycle latency, so we buffer PC and BTB prediction by one
  // cycle to align with the instruction coming out of memory.
  //
  // NOTE: PC buffer continues tracking even during flushes. Only instructions
  // are flushed to NOP, PC values must remain correct for pipeline tracking.
  // BTB prediction must track with PC, so it also continues during flushes.
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc_buf             <= '0;
      pc_plus4_buf       <= '0;
      btb_hit_buf        <= 1'b0;
      btb_pred_taken_buf <= 1'b0;
      btb_target_buf     <= '0;
    end else if (!if_id_stall) begin
      pc_buf             <= pc;
      pc_plus4_buf       <= pc_plus4;
      btb_hit_buf        <= btb_hit_if;
      btb_pred_taken_buf <= btb_pred_taken_if;
      btb_target_buf     <= btb_target_if;
    end
  end

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
  // Instruction buffering with stall support and extended flush
  //
  always_ff @(posedge clk) begin
    if (!rst_n || if_id_flush || flush_extend) begin
      instr_buf <= I_NOP;
    end else if (!if_id_stall) begin
      instr_buf <= instr;
    end
  end

  //
  // Outputs (buffered to align with BRAM latency)
  //
  assign instr_id                = instr_buf;
  assign pc_to_if_id             = pc_buf;
  assign pc_plus4_to_if_id       = pc_plus4_buf;
  assign btb_hit_to_if_id        = btb_hit_buf;
  assign btb_pred_taken_to_if_id = btb_pred_taken_buf;
  assign btb_target_to_if_id     = btb_target_buf;

endmodule

`endif
