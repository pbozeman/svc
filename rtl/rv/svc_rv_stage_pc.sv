`ifndef SVC_RV_STAGE_PC_SV
`define SVC_RV_STAGE_PC_SV

`include "svc.sv"
`include "svc_unused.sv"
`include "svc_rv_pipe_ctrl.sv"
`include "svc_rv_pipe_data.sv"

//
// RISC-V PC Stage
//
// Owns the program counter register and next-PC calculation.
// Issues PC to the IF stage via ready/valid handshake.
//
// This stage is intentionally simple - all PC source arbitration
// (misprediction, BTB, RAS, static prediction) is handled by
// svc_rv_pc_sel.sv which produces the pc_sel and target inputs.
//
module svc_rv_stage_pc #(
    parameter int          XLEN     = 32,
    parameter int          MEM_TYPE = 0,
    parameter int          BPRED    = 0,
    parameter int          PC_REG   = 0,
    parameter logic [31:0] RESET_PC = 32'h0000_0000
) (
    input logic clk,
    input logic rst_n,

    //
    // PC selection inputs (from pc_sel arbiter)
    //
    input logic [     1:0] pc_sel,
    input logic [XLEN-1:0] pc_redir_tgt,
    input logic [XLEN-1:0] pred_tgt,

    //
    // BTB early prediction indicator
    //
    // When btb_pred_taken is set, the prediction happened early in IF stage
    // and no extended flush is needed (the sequential instruction wasn't
    // fetched yet). When clear, the prediction happened late (ID stage static
    // or RAS) and requires extended flush via redir_pending_if.
    //
    input logic btb_pred_taken,

    //
    // BTB/RAS prediction inputs (from pc_sel arbiter)
    //
    input logic            btb_hit_pc,
    input logic            btb_pred_taken_pc,
    input logic [XLEN-1:0] btb_tgt_pc,
    input logic            btb_is_return_pc,
    input logic            ras_valid_pc,
    input logic [XLEN-1:0] ras_tgt_pc,

    //
    // Valid output to IF stage (ready removed, stall controls flow)
    //
    output logic m_valid,

    //
    // Stall signal
    //
    input logic stall_pc,

    //
    // Instruction memory stall (for cache miss)
    //
    input logic imem_stall,

    //
    // PC output (directly from PC register, for BTB lookup)
    //
    output logic [XLEN-1:0] pc,

    //
    // PC outputs to IF stage (optionally registered for timing)
    //
    output logic [XLEN-1:0] pc_if,
    output logic [XLEN-1:0] pc_next_if,

    //
    // BTB/RAS prediction outputs to IF stage (optionally registered)
    //
    output logic            btb_hit_if,
    output logic            btb_pred_taken_if,
    output logic [XLEN-1:0] btb_tgt_if,
    output logic            btb_is_return_if,
    output logic            ras_valid_if,
    output logic [XLEN-1:0] ras_tgt_if,

    //
    // Registered redirect pending (for hazard unit)
    //
    output logic redir_pending_if
);

  `include "svc_rv_defs.svh"

  //
  // PC initialization
  //
  // For BRAM with BPRED, PC starts at RESET_PC-4 so that pc_next = RESET_PC
  // on first cycle (BRAM speculative fetch uses pc_next_if).
  //
  // For SRAM with BPRED, PC starts at RESET_PC (SRAM fetches from pc_if).
  //
  localparam logic [XLEN-1:0] PC_INIT =
      ((MEM_TYPE == MEM_TYPE_BRAM && BPRED != 0) ? RESET_PC - 4 : RESET_PC);

  localparam logic [2*XLEN-1:0]
      PC_INIT_2X = (((2 * XLEN)'(PC_INIT) << XLEN) | (2 * XLEN)'(PC_INIT));

  //
  // Internal pc_next signal
  //
  logic [XLEN-1:0] pc_next;

  //
  // Redirect hold (BRAM + BPRED + I$ stall)
  //
  // When a redirect occurs while imem is stalled, the target fetch cannot be
  // issued immediately. Hold pc_next at the redirect target until the stall
  // clears so the target instruction is not skipped.
  //
  logic            redir_hold;
  logic [XLEN-1:0] redir_hold_tgt;

  //
  // Prediction hold (BPRED + imem_stall)
  //
  // With static (ID-stage) prediction, pc_sel can change back to sequential
  // while the front end is stalled on an outstanding miss for the sequential
  // path. Hold the predicted target until the stall clears so the prediction
  // isn't lost.
  //
  logic            pred_hold;
  logic [XLEN-1:0] pred_hold_tgt;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      redir_hold <= 1'b0;
    end else begin
      if ((MEM_TYPE == MEM_TYPE_BRAM) && (BPRED != 0) &&
          (pc_sel == PC_SEL_REDIRECT) && imem_stall) begin
        redir_hold <= 1'b1;
      end else if (redir_hold && !imem_stall && !stall_pc) begin
        redir_hold <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      redir_hold_tgt <= '0;
    end else if ((MEM_TYPE == MEM_TYPE_BRAM) && (BPRED != 0) &&
                 (pc_sel == PC_SEL_REDIRECT) && imem_stall) begin
      redir_hold_tgt <= pc_redir_tgt;
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pred_hold <= 1'b0;
    end else begin
      if (pc_sel == PC_SEL_REDIRECT) begin
        pred_hold <= 1'b0;
      end else
          if ((BPRED != 0) && (pc_sel == PC_SEL_PREDICTED) && imem_stall) begin
        pred_hold <= 1'b1;
      end else if (pred_hold && !imem_stall && !stall_pc) begin
        pred_hold <= 1'b0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pred_hold_tgt <= '0;
    end else
        if ((BPRED != 0) && (pc_sel == PC_SEL_PREDICTED) && imem_stall) begin
      pred_hold_tgt <= pred_tgt;
    end
  end

  //
  // PC next calculation
  //
  // - PC_SEL_REDIRECT: Actual branch/jump or misprediction
  // - PC_SEL_PREDICTED: Predicted branch taken (speculative fetch)
  // - PC_SEL_SEQUENTIAL: Normal sequential execution (pc + 4)
  //
  always_comb begin
    if (redir_hold) begin
      pc_next = redir_hold_tgt;
    end else if (pc_sel == PC_SEL_REDIRECT) begin
      pc_next = pc_redir_tgt;
    end else if (pred_hold) begin
      pc_next = pred_hold_tgt;
    end else begin
      case (pc_sel)
        PC_SEL_PREDICTED:  pc_next = pred_tgt;
        PC_SEL_SEQUENTIAL: pc_next = pc + 4;
        default:           pc_next = pc + 4;
      endcase
    end
  end

  //
  // PC register
  //
  // Advances when not stalled (stall_pc controls flow)
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= PC_INIT;
    end else if (!stall_pc) begin
      pc <= pc_next;
    end
  end

  //
  // PC/IF pipeline register and BTB/RAS metadata
  //
  // When PC_REG=1, all signals to IF stage are registered for timing.
  // This aligns the BTB/RAS metadata with the instruction fetch.
  //

  //
  // Pipeline control
  //
  logic pipe_advance;
  logic pipe_flush;
  logic pipe_bubble;

  //
  // Pipeline stale bubble (PC_REG only)
  //
  // With PC_REG=1, pc_if is stale for one cycle in two scenarios:
  // 1. Stall release: After any stall releases, the registered pc_if still
  //    has the old value for one cycle before updating.
  // 2. Reset release: After reset, pc_if has reset garbage for one cycle
  //    before the first valid PC is registered.
  //
  // We bubble these cycles to prevent duplicate instructions.
  //
  // Must use stall_pc (not just stall_cpu) because data hazard stalls also
  // cause pc_if to become stale when the pipeline register delays updates.
  //
  // See docs/pc-regstall-fix.md for details.
  //
  logic pipe_stale;

  if (PC_REG != 0) begin : g_pipe_stale
    logic was_stalled_or_reset;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        was_stalled_or_reset <= 1'b1;
      end else begin
        was_stalled_or_reset <= stall_pc;
      end
    end

    assign pipe_stale = was_stalled_or_reset && !stall_pc;
  end else begin : g_no_pipe_stale
    assign pipe_stale = 1'b0;
  end

  svc_rv_pipe_ctrl #(
      .REG(PC_REG)
  ) pipe_ctrl (
      .clk      (clk),
      .rst_n    (rst_n),
      .valid_i  (!stall_pc),
      .valid_o  (m_valid),
      .stall_i  (stall_pc),
      .flush_i  (1'b0),
      .bubble_i (1'b0),
      .advance_o(pipe_advance),
      .flush_o  (pipe_flush),
      .bubble_o (pipe_bubble)
  );

  `SVC_UNUSED({pipe_stale})

  //
  // Extended flush for registered PC changes
  //
  // Only set redir_pending for PC changes that require an extended flush:
  // - PC_SEL_REDIRECT: Misprediction recovery (always needs flush)
  // - PC_SEL_PREDICTED with !btb_pred_taken: Late prediction (ID stage
  //   static or RAS) where the sequential instruction was already
  //   fetched and must be discarded
  //
  // Do NOT set for BTB early predictions (btb_pred_taken) because the
  // sequential instruction was never fetched - BTB redirs in IF
  // stage before the instruction arrives.
  //
  logic redir_pending_next;

  if (PC_REG != 0) begin : g_redir_pending
    assign
        redir_pending_next = ((pc_sel == PC_SEL_REDIRECT) ||
                              (pc_sel == PC_SEL_PREDICTED && !btb_pred_taken));
  end else begin : g_no_redir_pending
    assign redir_pending_next = 1'b0;
    `SVC_UNUSED({btb_pred_taken})
  end

  //
  // PC values to IF stage
  //
  // With s_valid gating in IF stage, we don't fetch during bubbles (reset
  // release, stall release). So BUBBLE_REG=0 lets the data advance while
  // the bubble suppresses m_valid. This ensures pc_next_if is correct when
  // we start fetching.
  //
  // RESET_VAL is set to PC_INIT_2X so formal verification sees consistent
  // values during reset.
  //
  svc_rv_pipe_data #(
      .WIDTH     (2 * XLEN),
      .REG       (PC_REG),
      .BUBBLE_REG(0),
      .RESET_VAL (PC_INIT_2X)
  ) pipe_pc (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance),
      .flush  (pipe_flush),
      .bubble (pipe_bubble),
`ifdef FORMAL
      .s_valid(1'b1),
      .s_ready(1'b1),
`endif
      .data_i ({pc, pc_next}),
      .data_o ({pc_if, pc_next_if})
  );

  //
  // Control signals to IF stage (need proper reset values)
  //
  svc_rv_pipe_data #(
      .WIDTH     (5),
      .REG       (PC_REG),
      .BUBBLE_REG(1)
  ) pipe_ctrl_signals (
      .clk(clk),
      .rst_n(rst_n),
      .advance(pipe_advance),
      .flush(pipe_flush),
      .bubble(pipe_bubble),
`ifdef FORMAL
      .s_valid(1'b1),
      .s_ready(1'b1),
`endif
      .data_i({
        redir_pending_next,
        btb_hit_pc,
        btb_pred_taken_pc,
        btb_is_return_pc,
        ras_valid_pc
      }),
      .data_o({
        redir_pending_if,
        btb_hit_if,
        btb_pred_taken_if,
        btb_is_return_if,
        ras_valid_if
      })
  );

  //
  // Payload signals to IF stage (tgts, no reset needed)
  //
  svc_rv_pipe_data #(
      .WIDTH     (2 * XLEN),
      .REG       (PC_REG),
      .BUBBLE_REG(1)
  ) pipe_payload (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance),
      .flush  (1'b0),
      .bubble (pipe_bubble),
`ifdef FORMAL
      .s_valid(1'b1),
      .s_ready(1'b1),
`endif
      .data_i ({btb_tgt_pc, ras_tgt_pc}),
      .data_o ({btb_tgt_if, ras_tgt_if})
  );

`ifdef FORMAL
`ifdef FORMAL_SVC_RV_STAGE_PC
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

  always @(*) begin
    assume (rst_n == f_past_valid);
  end

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(stall_pc)) begin
        // inputs are stable when stalled (upstream contract)
        `FASSUME(a_pc_sel_stable, pc_sel == $past(pc_sel));
        `FASSUME(a_redir_tgt_stable, pc_redir_tgt == $past(pc_redir_tgt));
        `FASSUME(a_pred_tgt_stable, pred_tgt == $past(pred_tgt));
        `FASSUME(a_btb_pred_taken_stable, btb_pred_taken == $past(btb_pred_taken
                 ));
        `FASSUME(a_btb_hit_pc_stable, btb_hit_pc == $past(btb_hit_pc));
        `FASSUME(a_btb_pred_taken_pc_stable, btb_pred_taken_pc == $past(
                 btb_pred_taken_pc));
        `FASSUME(a_btb_tgt_pc_stable, btb_tgt_pc == $past(btb_tgt_pc));
        `FASSUME(a_btb_is_return_pc_stable, btb_is_return_pc == $past(
                 btb_is_return_pc));
        `FASSUME(a_ras_valid_pc_stable, ras_valid_pc == $past(ras_valid_pc));
        `FASSUME(a_ras_tgt_pc_stable, ras_tgt_pc == $past(ras_tgt_pc));
      end
    end
  end

  //
  // Stall behavior assertions (output interface) - registered mode only
  //
  // Flow control is done via stall_pc signal.
  // When stalled, outputs must remain stable.
  // In passthrough mode (PC_REG=0), outputs change combinationally.
  //
  if (PC_REG != 0) begin : g_stall_assertions
    always_ff @(posedge clk) begin
      if (f_past_valid && $past(rst_n) && rst_n) begin
        if ($past(stall_pc)) begin
          // Valid must remain stable when stalled
          `FASSERT(a_valid_stable, m_valid == $past(m_valid));

          // Payload signals must remain stable when stalled
          `FASSERT(a_pc_stable, pc_if == $past(pc_if));

          // output is stable (follows from above)
          `FASSERT(a_pc_next_stable, pc_next_if == $past(pc_next_if));
        end
      end
    end
  end

  //
  // Redirect correctness assertions
  //
  // When redirect occurs and not stalled, PC should take redirect target
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(!stall_pc) && $past(pc_sel == PC_SEL_REDIRECT)) begin
        `FASSERT(a_redirect_target, pc == $past(pc_redir_tgt));
      end
    end
  end

  //
  // Stall release assertions
  //
  // Check pc_next (not pc) because pc hasn't updated yet at the clock edge.
  // Use current pc_sel/targets since stability assumptions guarantee they
  // equal their $past values when $past(stall_pc) is true.
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(stall_pc) && !stall_pc) begin
        case (pc_sel)
          PC_SEL_REDIRECT:
          `FASSERT(a_stall_release_redirect, pc_next == pc_redir_tgt);
          PC_SEL_PREDICTED:
          `FASSERT(a_stall_release_predicted, pc_next == pred_tgt);
          default: `FASSERT(a_stall_release_sequential, pc_next == pc + 4);
        endcase
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // back-to-back valid transfers (not stalled)
      `FCOVER(c_back_to_back, $past(!stall_pc) && !stall_pc);

      // stalled cycle followed by non-stalled cycle
      `FCOVER(c_stalled, $past(stall_pc) && !stall_pc);

      // redirect while stalled, then stall releases
      `FCOVER(c_redirect_during_stall, $past(stall_pc, 2) && $past(
              pc_sel == PC_SEL_REDIRECT) && $past(!stall_pc) && !stall_pc);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
