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
  localparam logic [XLEN-1:0] PC_INIT =
      ((PIPELINED != 0 && BPRED != 0) ? RESET_PC - 4 : RESET_PC);

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

endmodule

`endif
