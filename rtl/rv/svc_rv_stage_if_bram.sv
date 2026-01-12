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
    // Valid from PC stage
    //
    input logic valid_if,

    //
    // PC input (from wrapper)
    //
    input logic [XLEN-1:0] pc,
    input logic [XLEN-1:0] pc_next,

    //
    // Hazard control
    //
    input logic if_id_flush,

    //
    // Pipeline advance signal
    //
    input logic advance,

    //
    // BTB prediction signals
    //
    input logic            btb_hit_if,
    input logic            btb_pred_taken_if,
    input logic [XLEN-1:0] btb_tgt_if,
    input logic            btb_is_return_if,

    //
    // RAS prediction signals
    //
    input logic            ras_valid_if,
    input logic [XLEN-1:0] ras_tgt_if,

    //
    // Instruction memory interface
    //
    // max_fanout to reduce routing delay on timing-critical signal
    (* max_fanout = 16 *) output logic        imem_ren,
                          output logic [31:0] imem_raddr,
                          input  logic [31:0] imem_rdata,

    //
    // Outputs to ID stage
    //
    output logic [    31:0] instr_id,
    output logic [XLEN-1:0] pc_ram,
    output logic [XLEN-1:0] pc_plus4_ram,
    output logic            btb_hit_id,
    output logic            btb_pred_taken_id,
    output logic [XLEN-1:0] btb_tgt_id,
    output logic            btb_is_return_id,
    output logic            ras_valid_id,
    output logic [XLEN-1:0] ras_tgt_id,

    //
    // Instruction validity
    //
    output logic valid_ram
);

  `include "svc_rv_defs.svh"

  (* max_fanout = 32 *)logic [XLEN-1:0] pc_buf;
  (* max_fanout = 32 *)logic [XLEN-1:0] pc_plus4_buf;

  logic            btb_hit_buf;
  logic            btb_pred_taken_buf;
  logic [XLEN-1:0] btb_tgt_buf;
  logic            btb_is_return_buf;
  logic            ras_valid_buf;
  logic [XLEN-1:0] ras_tgt_buf;
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
    assign imem_ren   = valid_if && advance;

    `SVC_UNUSED({pc});
  end else begin : g_no_bpred_imem
    //
    // Normal fetch: Address with current PC
    //
    assign imem_raddr = pc;
    assign instr      = imem_rdata;
    assign imem_ren   = valid_if && advance;

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
  // Control signals: need reset for correct behavior
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      btb_hit_buf        <= 1'b0;
      btb_pred_taken_buf <= 1'b0;
      btb_is_return_buf  <= 1'b0;
      ras_valid_buf      <= 1'b0;
    end else if (advance) begin
      btb_hit_buf        <= btb_hit_if;
      btb_pred_taken_buf <= btb_pred_taken_if;
      btb_is_return_buf  <= btb_is_return_if;
      ras_valid_buf      <= ras_valid_if;
    end
  end

  //
  // Datapath registers: no reset needed (don't care until valid_buf becomes 1)
  //
  always_ff @(posedge clk) begin
    if (advance) begin
      pc_buf       <= imem_raddr;
      pc_plus4_buf <= imem_raddr + 4;
      btb_tgt_buf  <= btb_tgt_if;
      ras_tgt_buf  <= ras_tgt_if;
    end
  end

  //
  // Extended flush for BRAM
  //
  if (BPRED != 0) begin : g_no_flush_extend
    //
    // With BPRED, early fetch targets pc_next and avoids fetching stale
    // sequential instructions before redirects are known.
    //
    // However, a flush can still arrive while stalled (advance=0), e.g. when
    // a redirect occurs during an instruction cache miss. In that case we
    // need a single-cycle extended flush when the stall clears to prevent
    // capturing a stale held response.
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        flush_extend <= 1'b0;
      end else if (if_id_flush && !advance) begin
        flush_extend <= 1'b1;
      end else if (advance) begin
        flush_extend <= 1'b0;
      end
      // During stall (advance=0), flush_extend holds its value
    end

  end else begin : g_flush_extend
    //
    // Without BPRED: Sequential instruction is already fetched before redirect
    // is detected, so we need flush_extend to discard the stale instruction.
    //
    // flush_extend stays active while stalled after a flush. This ensures
    // we don't capture stale data when stalls delay the new fetch. It clears
    // only when advance=1 (pipeline advancing), at which point a new fetch
    // was issued and its data will arrive on the next cycle.
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        flush_extend <= 1'b0;
      end else if (if_id_flush) begin
        flush_extend <= 1'b1;
      end else if (advance) begin
        flush_extend <= 1'b0;
      end
      // During stall (advance=0), flush_extend holds its value
    end
  end

  //
  // Instruction buffering with stall support and extended flush
  //
  always_ff @(posedge clk) begin
    if (!rst_n || if_id_flush || flush_extend) begin
      instr_buf <= I_NOP;
    end else if (advance) begin
      instr_buf <= instr;
    end
  end

  //
  // Instruction validity tracking
  //
  // Two-part validity:
  // 1. fetch_started: Sticky flag for startup - first fetch hasn't completed yet
  // 2. valid_fetch_buf: Per-cycle tracking - was a valid fetch issued last cycle?
  //
  // When PC stage bubbles (valid_if low), imem_ren goes low, so valid_fetch_buf
  // goes low on the next cycle, preventing the stale instruction from being
  // marked as valid.
  //
  logic fetch_started;
  logic valid_fetch_buf;
  logic hold_fetch_buf;

  assign hold_fetch_buf = !valid_if && (if_id_flush || flush_extend);

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      fetch_started <= 1'b0;
    end else if (imem_ren && advance) begin
      fetch_started <= 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      valid_fetch_buf <= 1'b0;
    end else if (advance && !hold_fetch_buf) begin
      valid_fetch_buf <= imem_ren;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      valid_buf <= 1'b0;
    end else if (advance) begin
      valid_buf <=
          (fetch_started && valid_fetch_buf && !if_id_flush && !flush_extend);
    end
  end

  //
  // Outputs (buffered to align with BRAM latency)
  //
  assign instr_id          = instr_buf;
  assign pc_ram            = pc_buf;
  assign pc_plus4_ram      = pc_plus4_buf;
  assign btb_hit_id        = btb_hit_buf;
  assign btb_pred_taken_id = btb_pred_taken_buf;
  assign btb_tgt_id        = btb_tgt_buf;
  assign btb_is_return_id  = btb_is_return_buf;
  assign ras_valid_id      = ras_valid_buf;
  assign ras_tgt_id        = ras_tgt_buf;
  assign valid_ram         = valid_buf;

endmodule

`endif
