`ifndef SVC_RV_STAGE_PC_SV
`define SVC_RV_STAGE_PC_SV

`include "svc.sv"
`include "svc_unused.sv"

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
    parameter int          XLEN      = 32,
    parameter int          PIPELINED = 1,
    parameter int          BPRED     = 0,
    parameter int          PC_REG    = 0,
    parameter logic [31:0] RESET_PC  = 32'h0000_0000
) (
    input logic clk,
    input logic rst_n,

    //
    // PC selection inputs (from pc_sel arbiter)
    //
    input logic [     1:0] pc_sel,
    input logic [XLEN-1:0] pc_redirect_target,
    input logic [XLEN-1:0] pred_target,

    //
    // BTB early prediction indicator
    //
    // When btb_pred_taken is set, the prediction happened early in IF stage
    // and no extended flush is needed (the sequential instruction wasn't
    // fetched yet). When clear, the prediction happened late (ID stage static
    // or RAS) and requires extended flush via redirect_pending_if.
    //
    input logic btb_pred_taken,

    //
    // BTB/RAS prediction inputs (from pc_sel arbiter)
    //
    input logic            btb_hit_pc,
    input logic            btb_pred_taken_pc,
    input logic [XLEN-1:0] btb_target_pc,
    input logic            btb_is_return_pc,
    input logic            ras_valid_pc,
    input logic [XLEN-1:0] ras_target_pc,

    //
    // Ready/valid interface to IF stage
    //
    output logic m_valid,
    input  logic m_ready,

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
    output logic [XLEN-1:0] btb_target_if,
    output logic            btb_is_return_if,
    output logic            ras_valid_if,
    output logic [XLEN-1:0] ras_target_if,

    //
    // Registered redirect pending (for hazard unit)
    //
    output logic redirect_pending_if
);

  `include "svc_rv_defs.svh"

  //
  // PC initialization
  //
  // For pipelined mode with BPRED, PC starts at RESET_PC-4 so that
  // pc_next = RESET_PC on first cycle (early speculative fetch uses pc_next)
  //
  localparam logic [XLEN-1:0]
      PC_INIT = ((PIPELINED != 0 && BPRED != 0) ? RESET_PC - 4 : RESET_PC);

  //
  // Internal pc_next signal
  //
  logic [XLEN-1:0] pc_next;

  //
  // PC next calculation
  //
  // - PC_SEL_REDIRECT: Actual branch/jump or misprediction
  // - PC_SEL_PREDICTED: Predicted branch taken (speculative fetch)
  // - PC_SEL_SEQUENTIAL: Normal sequential execution (pc + 4)
  //
  always_comb begin
    case (pc_sel)
      PC_SEL_REDIRECT:   pc_next = pc_redirect_target;
      PC_SEL_PREDICTED:  pc_next = pred_target;
      PC_SEL_SEQUENTIAL: pc_next = pc + 4;
      default:           pc_next = pc + 4;
    endcase
  end

  //
  // PC register
  //
  // Advances when downstream stage accepts (m_ready)
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= PC_INIT;
    end else if (m_ready) begin
      pc <= pc_next;
    end
  end

  //
  // PC/IF pipeline register and BTB/RAS metadata
  //
  // When PC_REG=1, all signals to IF stage are registered for timing.
  // This aligns the BTB/RAS metadata with the instruction fetch.
  //
  if (PC_REG != 0) begin : g_pc_if_reg
    //
    // Control signals: need reset
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        pc_if               <= PC_INIT;
        pc_next_if          <= PC_INIT + 4;
        redirect_pending_if <= 1'b0;
        btb_hit_if          <= 1'b0;
        btb_pred_taken_if   <= 1'b0;
        btb_is_return_if    <= 1'b0;
        ras_valid_if        <= 1'b0;
      end else if (m_ready) begin
        pc_if <= pc;
        pc_next_if <= pc_next;
        btb_hit_if <= btb_hit_pc;
        btb_pred_taken_if <= btb_pred_taken_pc;
        btb_is_return_if <= btb_is_return_pc;
        ras_valid_if <= ras_valid_pc;
        //
        // Extended flush for registered PC changes
        //
        // Only set redirect_pending_if for PC changes that require an
        // extended flush:
        // - PC_SEL_REDIRECT: Misprediction recovery (always needs flush)
        // - PC_SEL_PREDICTED with !btb_pred_taken: Late prediction (ID stage
        //   static or RAS) where the sequential instruction was already
        //   fetched and must be discarded
        //
        // Do NOT set for BTB early predictions (btb_pred_taken) because the
        // sequential instruction was never fetched - BTB redirects in IF
        // stage before the instruction arrives.
        //
        redirect_pending_if <= (pc_sel == PC_SEL_REDIRECT) ||
            (pc_sel == PC_SEL_PREDICTED && !btb_pred_taken);
      end
    end

    //
    // Datapath signals: no reset needed
    //
    always_ff @(posedge clk) begin
      if (m_ready) begin
        btb_target_if <= btb_target_pc;
        ras_target_if <= ras_target_pc;
      end
    end

  end else begin : g_pc_if_comb
    assign pc_if               = pc;
    assign pc_next_if          = pc_next;
    assign redirect_pending_if = 1'b0;
    assign btb_hit_if          = btb_hit_pc;
    assign btb_pred_taken_if   = btb_pred_taken_pc;
    assign btb_target_if       = btb_target_pc;
    assign btb_is_return_if    = btb_is_return_pc;
    assign ras_valid_if        = ras_valid_pc;
    assign ras_target_if       = ras_target_pc;

    //
    // btb_pred_taken only used in PC_REG mode for redirect_pending_if
    //
    `SVC_UNUSED({btb_pred_taken})
  end

  //
  // Always valid after reset - we always have a PC to issue
  //
  assign m_valid = 1'b1;

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

  //
  // m_valid/m_ready handshake assertions (output interface)
  //
  // PC stage has no flush - it always has a valid PC to issue.
  // m_valid is constant 1, so stability is trivially satisfied.
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(m_valid && !m_ready)) begin
        //
        // Valid must remain asserted until ready
        //
        `FASSERT(a_valid_stable, m_valid);

        //
        // Payload signals must remain stable when stalled
        //
        `FASSERT(a_pc_stable, pc_if == $past(pc_if));

        //
        // Assume inputs are stable when stalled (upstream contract)
        //
        `FASSUME(a_pc_sel_stable, pc_sel == $past(pc_sel));
        `FASSUME(a_redirect_target_stable, pc_redirect_target == $past(
                 pc_redirect_target));
        `FASSUME(a_pred_target_stable, pred_target == $past(pred_target));

        //
        // Assert output is stable (follows from above)
        //
        `FASSERT(a_pc_next_stable, pc_next_if == $past(pc_next_if));
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      //
      // Cover back-to-back valid transfers
      //
      `FCOVER(c_back_to_back, $past(m_valid && m_ready) && m_valid);

      //
      // Cover stalled transfer (valid high, ready low for a cycle)
      //
      `FCOVER(c_stalled, $past(m_valid && !m_ready) && m_valid && m_ready);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
