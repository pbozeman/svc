`ifndef SVC_RV_STAGE_IF_SV
`define SVC_RV_STAGE_IF_SV

`include "svc.sv"
`include "svc_unused.sv"
`include "svc_rv_stage_if_sram.sv"
`include "svc_rv_stage_if_bram.sv"

//
// RISC-V Instruction Fetch (IF) Stage
//
// Wrapper that handles shared logic:
// - Instantiation of memory-type-specific fetch logic (BRAM or SRAM)
// - IF/ID pipeline registers for PC
//
// BTB/RAS buffering is handled by the memory-type-specific submodules.
// PC logic is handled by svc_rv_stage_pc.
//
module svc_rv_stage_if #(
    parameter int XLEN      = 32,
    parameter int PIPELINED = 1,
    parameter int MEM_TYPE  = 0,
    parameter int BPRED     = 0
) (
    input logic clk,
    input logic rst_n,

    // Hazard & stall control
    input logic if_id_flush,
    input logic stall_i,

    // inputs from stage_pc
    input logic            instr_valid_if,
    input logic [XLEN-1:0] pc_if,
    input logic [XLEN-1:0] pc_next_if,

    // BTB prediction signals
    input logic            btb_hit_if,
    input logic            btb_pred_taken_if,
    input logic [XLEN-1:0] btb_tgt_if,
    input logic            btb_is_return_if,

    // RAS prediction signals
    input logic            ras_valid_if,
    input logic [XLEN-1:0] ras_tgt_if,

    // Instruction memory interface
    output logic        imem_ren,
    output logic [31:0] imem_raddr,
    input  logic [31:0] imem_rdata,

    // Outputs to ID stage
    output logic instr_valid_id,

    output logic [    31:0] instr_id,
    output logic [XLEN-1:0] pc_id,
    output logic [XLEN-1:0] pc_plus4_id,
    output logic            btb_hit_id,
    output logic            btb_pred_taken_id,
    output logic [XLEN-1:0] btb_tgt_id,
    output logic            btb_is_return_id,
    output logic            ras_valid_id,
    output logic [XLEN-1:0] ras_tgt_id
);

  `include "svc_rv_defs.svh"

  // Internal signals from RAM submodule
  logic [XLEN-1:0] pc_ram;
  logic [XLEN-1:0] pc_plus4_ram;
  logic            valid_ram;

  // Pipeline advance signal
  (* max_fanout = 32 *)logic            advance;
  assign advance = !stall_i;

  // Memory-type specific fetch logic
  if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_bram
    svc_rv_stage_if_bram #(
        .XLEN (XLEN),
        .BPRED(BPRED)
    ) stage (
        .clk              (clk),
        .rst_n            (rst_n),
        .valid_if         (instr_valid_if),
        .pc               (pc_if),
        .pc_next          (pc_next_if),
        .if_id_flush      (if_id_flush),
        .advance          (advance),
        .btb_hit_if       (btb_hit_if),
        .btb_pred_taken_if(btb_pred_taken_if),
        .btb_tgt_if       (btb_tgt_if),
        .btb_is_return_if (btb_is_return_if),
        .ras_valid_if     (ras_valid_if),
        .ras_tgt_if       (ras_tgt_if),
        .imem_ren         (imem_ren),
        .imem_raddr       (imem_raddr),
        .imem_rdata       (imem_rdata),
        .instr_id         (instr_id),
        .pc_ram           (pc_ram),
        .pc_plus4_ram     (pc_plus4_ram),
        .btb_hit_id       (btb_hit_id),
        .btb_pred_taken_id(btb_pred_taken_id),
        .btb_tgt_id       (btb_tgt_id),
        .btb_is_return_id (btb_is_return_id),
        .ras_valid_id     (ras_valid_id),
        .ras_tgt_id       (ras_tgt_id),
        .valid_ram        (valid_ram)
    );

  end else begin : g_sram
    svc_rv_stage_if_sram #(
        .XLEN     (XLEN),
        .PIPELINED(PIPELINED)
    ) stage (
        .clk              (clk),
        .rst_n            (rst_n),
        .valid_if         (instr_valid_if),
        .pc               (pc_if),
        .if_id_flush      (if_id_flush),
        .advance          (advance),
        .btb_hit_if       (btb_hit_if),
        .btb_pred_taken_if(btb_pred_taken_if),
        .btb_tgt_if       (btb_tgt_if),
        .btb_is_return_if (btb_is_return_if),
        .ras_valid_if     (ras_valid_if),
        .ras_tgt_if       (ras_tgt_if),
        .imem_ren         (imem_ren),
        .imem_raddr       (imem_raddr),
        .imem_rdata       (imem_rdata),
        .instr_id         (instr_id),
        .pc_ram           (pc_ram),
        .pc_plus4_ram     (pc_plus4_ram),
        .btb_hit_id       (btb_hit_id),
        .btb_pred_taken_id(btb_pred_taken_id),
        .btb_tgt_id       (btb_tgt_id),
        .btb_is_return_id (btb_is_return_id),
        .ras_valid_id     (ras_valid_id),
        .ras_tgt_id       (ras_tgt_id),
        .valid_ram        (valid_ram)
    );

    `SVC_UNUSED({pc_next_if})
  end

  // IF/ID Pipeline Register
  if (PIPELINED != 0) begin : g_registered
    logic [XLEN-1:0] pc_id_buf;
    logic [XLEN-1:0] pc_plus4_id_buf;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        pc_id_buf       <= '0;
        pc_plus4_id_buf <= '0;
      end else if (advance) begin
        pc_id_buf       <= pc_ram;
        pc_plus4_id_buf <= pc_plus4_ram;
      end
    end

    assign pc_id       = pc_id_buf;
    assign pc_plus4_id = pc_plus4_id_buf;

  end else begin : g_passthrough
    assign pc_id       = pc_ram;
    assign pc_plus4_id = pc_plus4_ram;
  end

  // Valid output
  assign instr_valid_id = valid_ram;

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_STAGE_IF
  `define FASSERT(label, a) label: assert(a)
  `define FASSUME(label, a) label: assume(a)
  `define FCOVER(label, a) label: cover(a)
`else
  `define FASSERT(label, a) label: assume(a)
  `define FASSUME(label, a) label: assert(a)
  `define FCOVER(label, a)
`endif

  logic f_past_valid = 1'b0;

  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  //
  // Once reset deasserts, it must stay deasserted
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      assume (rst_n);
    end
  end

  //
  // Stall behavior assertions (output interface)
  //
  // Pipeline flush is allowed to drop instr_valid_id even when stalled.
  // This is intentional - flush creates bubbles.
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(instr_valid_id && stall_i && !if_id_flush)) begin
        //
        // Valid must remain asserted until not stalled (unless flushed)
        //
        `FASSERT(a_valid_stable, instr_valid_id || if_id_flush);

        //
        // Payload signals must remain stable
        //
        `FASSERT(a_instr_stable, instr_id == $past(instr_id));
        `FASSERT(a_pc_stable, pc_id == $past(pc_id));
        `FASSERT(a_pc_plus4_stable, pc_plus4_id == $past(pc_plus4_id));
        `FASSERT(a_btb_hit_stable, btb_hit_id == $past(btb_hit_id));
        `FASSERT(a_btb_pred_taken_stable, btb_pred_taken_id == $past(
                 btb_pred_taken_id));
        `FASSERT(a_btb_tgt_stable, btb_tgt_id == $past(btb_tgt_id));
        `FASSERT(a_btb_is_return_stable, btb_is_return_id == $past(
                 btb_is_return_id));
        `FASSERT(a_ras_valid_stable, ras_valid_id == $past(ras_valid_id));
        `FASSERT(a_ras_tgt_stable, ras_tgt_id == $past(ras_tgt_id));
      end
    end
  end

  //
  // Input stability: data must be held when stalled
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(stall_i)) begin
        `FASSUME(a_in_pc_stable, pc_if == $past(pc_if));
        `FASSUME(a_in_btb_hit_stable, btb_hit_if == $past(btb_hit_if));
        `FASSUME(a_in_btb_pred_taken_stable, btb_pred_taken_if == $past(
                 btb_pred_taken_if));
        `FASSUME(a_in_btb_tgt_stable, btb_tgt_if == $past(btb_tgt_if));
        `FASSUME(a_in_btb_is_return_stable, btb_is_return_if == $past(
                 btb_is_return_if));
        `FASSUME(a_in_ras_valid_stable, ras_valid_if == $past(ras_valid_if));
        `FASSUME(a_in_ras_tgt_stable, ras_tgt_if == $past(ras_tgt_if));
      end
    end
  end

  //
  // Verify imem_raddr matches expected value based on BPRED parameter
  //
  // With BPRED: Use pc_next_if for speculative fetch (follow prediction)
  // Without BPRED: Use pc_if for normal fetch
  //
  if (PIPELINED != 0) begin : g_f_imem_check
    always_ff @(posedge clk) begin
      if (f_past_valid && rst_n && imem_ren) begin
        if (BPRED != 0) begin
          `FASSERT(a_imem_addr_bpred, imem_raddr == pc_next_if);
        end else begin
          `FASSERT(a_imem_addr_no_bpred, imem_raddr == pc_if);
        end
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cover back-to-back valid transfers (not stalled)
      `FCOVER(c_back_to_back, $past(instr_valid_id && !stall_i
              ) && instr_valid_id);

      // Cover stalled cycle followed by non-stalled cycle
      `FCOVER(c_stalled, $past(instr_valid_id && stall_i
              ) && instr_valid_id && !stall_i);

      // Cover stall condition
      `FCOVER(c_stall, $past(stall_i));
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
