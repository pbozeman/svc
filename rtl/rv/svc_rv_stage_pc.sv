`ifndef SVC_RV_STAGE_PC_SV
`define SVC_RV_STAGE_PC_SV

`include "svc.sv"

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
    // Ready/valid interface to IF stage
    //
    output logic m_valid,
    input  logic m_ready,

    //
    // PC outputs
    //
    output logic [XLEN-1:0] pc,
    output logic [XLEN-1:0] pc_next
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
  // PC next calculation with 3-way mux
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
        `FASSERT(a_pc_stable, pc == $past(pc));

        //
        // Assume inputs are stable when stalled (upstream contract)
        //
        `FASSUME(a_pc_sel_stable, pc_sel == $past(pc_sel));
        `FASSUME(a_redirect_target_stable, pc_redirect_target == $past(
                 pc_redirect_target));
        `FASSUME(a_pred_target_stable, pred_target == $past(pred_target));

        //
        // Assert combinational output is stable (follows from above)
        //
        `FASSERT(a_pc_next_stable, pc_next == $past(pc_next));
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
