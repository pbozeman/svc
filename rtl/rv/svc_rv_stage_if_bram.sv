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
    parameter int XLEN,
    parameter int BPRED
) (
    input logic clk,
    input logic rst_n,

    //
    // PC input (from wrapper)
    //
    input logic [XLEN-1:0] pc,
    input logic [XLEN-1:0] pc_next,

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
    input logic            btb_is_return_if,

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
    output logic            btb_is_return_to_if_id,
    output logic            ras_valid_to_if_id,
    output logic [XLEN-1:0] ras_target_to_if_id,

    //
    // Instruction validity
    //
    output logic valid_to_if_id
);

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc_buf;
  logic [XLEN-1:0] pc_plus4_buf;
  logic            btb_hit_buf;
  logic            btb_pred_taken_buf;
  logic [XLEN-1:0] btb_target_buf;
  logic            btb_is_return_buf;
  logic            ras_valid_buf;
  logic [XLEN-1:0] ras_target_buf;
  logic            flush_extend;
  logic [    31:0] instr;
  logic [    31:0] instr_buf;
  logic            valid_buf;

  //
  // Instruction memory interface
  //
  // BRAM with BPRED: Use pc_next for early speculative fetch
  // BRAM without BPRED: Use pc for normal fetch
  //
  if (BPRED != 0) begin : g_bpred_imem
    //
    // Early fetch: Address with pc_next to fetch target in same cycle as prediction
    //
    assign imem_raddr = pc_next;
    assign instr      = imem_rdata;
    assign imem_ren   = !rst_n || !pc_stall;

    `SVC_UNUSED({pc});
  end else begin : g_no_bpred_imem
    //
    // Normal fetch: Address with current PC
    //
    assign imem_raddr = pc;
    assign instr      = imem_rdata;
    assign imem_ren   = !pc_stall;

    `SVC_UNUSED({pc_next})
  end

  //
  // PC, BTB, and RAS prediction buffering to match instruction latency
  //
  // BRAM has 1-cycle latency, so we buffer PC, BTB, and RAS predictions by one
  // cycle to align with the instruction coming out of memory.
  //
  // We buffer imem_raddr (the actual fetch address):
  // - With BPRED: imem_raddr = pc_next (early speculative fetch)
  // - Without BPRED: imem_raddr = pc (normal fetch)
  //
  // This ensures the buffered PC always matches the instruction address,
  // even during stalls when pc might not have advanced to match pc_next.
  //
  // NOTE: PC buffer continues tracking even during flushes. Only instructions
  // are flushed to NOP, PC values must remain correct for pipeline tracking.
  // BTB and RAS predictions must track with PC, so they also continue during flushes.
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc_buf             <= '0;
      pc_plus4_buf       <= 32'd4;
      btb_hit_buf        <= 1'b0;
      btb_pred_taken_buf <= 1'b0;
      btb_target_buf     <= '0;
      btb_is_return_buf  <= 1'b0;
      ras_valid_buf      <= 1'b0;
      ras_target_buf     <= '0;
    end else if (!if_id_stall) begin
      pc_buf             <= imem_raddr;
      pc_plus4_buf       <= imem_raddr + 4;
      btb_hit_buf        <= btb_hit_if;
      btb_pred_taken_buf <= btb_pred_taken_if;
      btb_target_buf     <= btb_target_if;
      btb_is_return_buf  <= btb_is_return_if;
      ras_valid_buf      <= ras_valid_if;
      ras_target_buf     <= ras_target_if;
    end
  end

  //
  // Extended flush for BRAM
  //
  if (BPRED != 0) begin : g_no_flush_extend
    // Without BPRED: Sequential instruction is already fetched before redirect
    // is detected, so we need flush_extend to clear the stale instruction.
    assign flush_extend = 1'b0;

  end else begin : g_flush_extend
    // With BPRED and pc_next early fetch: Target is fetched immediately when
    // prediction happens, so flush_extend would incorrectly flush the CORRECT
    // target instruction. Must disable.
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        flush_extend <= 1'b0;
      end else begin
        flush_extend <= if_id_flush;
      end
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
  // Instruction validity tracking
  //
  // Tracks when pipeline slot contains a real instruction.
  // Starts at 0 during reset, becomes 1 when first non-flushed instruction
  // arrives (one cycle after reset due to BRAM latency).
  //
  // The started flag ensures we wait one extra cycle after reset before
  // marking instructions as valid. This accounts for BRAM latency - the
  // first cycle after reset, valid_buf stays 0 even though the pipeline
  // is running, because the BRAM hasn't output the first real instruction yet.
  //
  logic started;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      started   <= 1'b0;
      valid_buf <= 1'b0;
    end else if (!if_id_stall) begin
      started   <= 1'b1;
      valid_buf <= started && !if_id_flush && !flush_extend;
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
  assign btb_is_return_to_if_id  = btb_is_return_buf;
  assign ras_valid_to_if_id      = ras_valid_buf;
  assign ras_target_to_if_id     = ras_target_buf;
  assign valid_to_if_id          = valid_buf;

endmodule

`endif
