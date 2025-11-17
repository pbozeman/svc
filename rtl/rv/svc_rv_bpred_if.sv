`ifndef SVC_RV_BPRED_IF_SV
`define SVC_RV_BPRED_IF_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Branch Prediction - IF Stage
//
// Handles BTB signal buffering for pipeline registers.
//
// Different memory types require different buffering strategies:
// - SRAM (0-cycle latency): BTB signals need buffering in IF/ID register
// - BRAM (1-cycle latency): BTB signals already buffered, passthrough
// - Non-pipelined: Passthrough
//
module svc_rv_bpred_if #(
    parameter int XLEN      = 32,
    parameter int PIPELINED = 0,
    parameter int MEM_TYPE  = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic if_id_stall,
    input logic if_id_flush,

    //
    // BTB prediction from IF stage (current PC lookup)
    //
    input logic            btb_hit_if,
    input logic            btb_pred_taken_if,
    input logic [XLEN-1:0] btb_target_if,

    //
    // Buffered outputs to ID stage
    //
    output logic            btb_hit_id,
    output logic            btb_pred_taken_id,
    output logic [XLEN-1:0] btb_target_id
);

  `include "svc_rv_defs.svh"

  //
  // BTB signal buffering: conditional on pipelined mode and memory type
  //
  if (PIPELINED != 0) begin : g_pipelined

    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_btb_buffered
      //
      // SRAM (0-cycle latency): BTB signals passthrough from BTB lookup,
      // need buffering here for IF/ID pipeline register
      //
      logic            btb_hit_id_buf;
      logic            btb_pred_taken_id_buf;
      logic [XLEN-1:0] btb_target_id_buf;

      always_ff @(posedge clk) begin
        if (!rst_n || if_id_flush) begin
          btb_hit_id_buf        <= 1'b0;
          btb_pred_taken_id_buf <= 1'b0;
          btb_target_id_buf     <= '0;
        end else if (!if_id_stall) begin
          btb_hit_id_buf        <= btb_hit_if;
          btb_pred_taken_id_buf <= btb_pred_taken_if;
          btb_target_id_buf     <= btb_target_if;
        end
      end

      assign btb_hit_id        = btb_hit_id_buf;
      assign btb_pred_taken_id = btb_pred_taken_id_buf;
      assign btb_target_id     = btb_target_id_buf;

    end else begin : g_btb_passthrough
      //
      // BRAM (1-cycle latency): BTB signals already buffered by BRAM read
      // latency and stage-specific buffering, passthrough here to avoid
      // double-buffering
      //
      assign btb_hit_id        = btb_hit_if;
      assign btb_pred_taken_id = btb_pred_taken_if;
      assign btb_target_id     = btb_target_if;

      `SVC_UNUSED({clk, rst_n, if_id_stall, if_id_flush});
    end

  end else begin : g_not_pipelined
    //
    // Non-pipelined: Passthrough
    //
    assign btb_hit_id        = btb_hit_if;
    assign btb_pred_taken_id = btb_pred_taken_if;
    assign btb_target_id     = btb_target_if;

    `SVC_UNUSED({clk, rst_n, if_id_stall, if_id_flush});
  end

endmodule

`endif
