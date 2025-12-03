`ifndef SVC_RV_BPRED_IF_SV
`define SVC_RV_BPRED_IF_SV

`include "svc.sv"

//
// RISC-V Branch Prediction - IF Stage
//
// Handles BTB and RAS signal buffering for pipeline registers.
//
// Different memory types require different buffering strategies:
// - SRAM (0-cycle latency): BTB/RAS signals need buffering in IF/ID register
// - BRAM (1-cycle latency): BTB/RAS signals already buffered, passthrough
// - Non-pipelined: Passthrough
//
// Signal naming convention:
// - Inputs use `_to_if_id` suffix: These are "backward-flowing" signals that
//   originate from top-level (PC selection) and flow through the IF stage
//   memory modules (which buffer them) before arriving here. The suffix
//   indicates they're destined for the IF/ID pipeline boundary.
// - Outputs use `_id` suffix: Final buffered signals going to ID stage.
//
module svc_rv_bpred_if #(
    parameter int XLEN,
    parameter int PIPELINED,
    parameter int MEM_TYPE
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic if_id_stall,
    input logic if_id_flush,

    //
    // BTB prediction from IF stage memory modules
    //
    input logic            btb_hit_to_if_id,
    input logic            btb_pred_taken_to_if_id,
    input logic [XLEN-1:0] btb_target_to_if_id,
    input logic            btb_is_return_to_if_id,

    //
    // RAS prediction from IF stage memory modules
    //
    input logic            ras_valid_to_if_id,
    input logic [XLEN-1:0] ras_target_to_if_id,

    //
    // Buffered outputs to ID stage
    //
    output logic            btb_hit_id,
    output logic            btb_pred_taken_id,
    output logic [XLEN-1:0] btb_target_id,
    output logic            btb_is_return_id,
    output logic            ras_valid_id,
    output logic [XLEN-1:0] ras_target_id
);

  `include "svc_rv_defs.svh"

  //
  // BTB and RAS signal buffering: conditional on pipelined mode and memory type
  //
  // Two cases:
  // 1. SRAM + pipelined: Buffer signals for IF/ID pipeline register
  // 2. BRAM + pipelined OR non-pipelined: Passthrough (already buffered)
  //
  if (PIPELINED != 0 && MEM_TYPE == MEM_TYPE_SRAM) begin : g_buffered
    //
    // SRAM pipelined: Signals from IF memory modules need buffering here
    //
    logic            btb_hit_id_buf;
    logic            btb_pred_taken_id_buf;
    logic [XLEN-1:0] btb_target_id_buf;
    logic            btb_is_return_id_buf;
    logic            ras_valid_id_buf;
    logic [XLEN-1:0] ras_target_id_buf;

    //
    // Control signals: need reset for correct behavior
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        btb_hit_id_buf        <= 1'b0;
        btb_pred_taken_id_buf <= 1'b0;
        btb_is_return_id_buf  <= 1'b0;
        ras_valid_id_buf      <= 1'b0;
      end else if (if_id_flush) begin
        btb_hit_id_buf        <= 1'b0;
        btb_pred_taken_id_buf <= 1'b0;
        btb_is_return_id_buf  <= 1'b0;
        ras_valid_id_buf      <= 1'b0;
      end else if (!if_id_stall) begin
        btb_hit_id_buf        <= btb_hit_to_if_id;
        btb_pred_taken_id_buf <= btb_pred_taken_to_if_id;
        btb_is_return_id_buf  <= btb_is_return_to_if_id;
        ras_valid_id_buf      <= ras_valid_to_if_id;
      end
    end

    //
    // Datapath registers: no reset needed (don't care when valid flags == 0)
    //
    always_ff @(posedge clk) begin
      if (!if_id_stall) begin
        btb_target_id_buf <= btb_target_to_if_id;
        ras_target_id_buf <= ras_target_to_if_id;
      end
    end

    assign btb_hit_id        = btb_hit_id_buf;
    assign btb_pred_taken_id = btb_pred_taken_id_buf;
    assign btb_target_id     = btb_target_id_buf;
    assign btb_is_return_id  = btb_is_return_id_buf;
    assign ras_valid_id      = ras_valid_id_buf;
    assign ras_target_id     = ras_target_id_buf;

  end else begin : g_passthrough
    //
    // BRAM pipelined: Already buffered by IF memory modules
    // Non-pipelined: No buffering needed
    //
    assign btb_hit_id        = btb_hit_to_if_id;
    assign btb_pred_taken_id = btb_pred_taken_to_if_id;
    assign btb_target_id     = btb_target_to_if_id;
    assign btb_is_return_id  = btb_is_return_to_if_id;
    assign ras_valid_id      = ras_valid_to_if_id;
    assign ras_target_id     = ras_target_to_if_id;

    // verilog_format: off
    `include "svc_unused.sv"
    `SVC_UNUSED({clk, rst_n, if_id_stall, if_id_flush});
    // verilog_format: on
  end

endmodule

`endif
