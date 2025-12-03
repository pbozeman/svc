`ifndef SVC_RV_STAGE_IF_SV
`define SVC_RV_STAGE_IF_SV

`include "svc.sv"
`include "svc_unused.sv"
`include "svc_rv_bpred_if.sv"
`include "svc_rv_stage_if_sram.sv"
`include "svc_rv_stage_if_bram.sv"

//
// RISC-V Instruction Fetch (IF) Stage
//
// Thin wrapper that handles shared logic:
// - PC next calculation and PC register
// - IF/ID pipeline registers
// - Instantiation of memory-type-specific fetch logic
//
module svc_rv_stage_if #(
    parameter int          XLEN      = 32,
    parameter int          PIPELINED = 1,
    parameter int          MEM_TYPE  = 0,
    parameter int          BPRED     = 0,
    parameter logic [31:0] RESET_PC  = 32'h0000_0000
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic pc_stall,
    input logic if_id_stall,
    input logic if_id_flush,

    //
    // Final PC selection and redirect target
    //
    input logic [     1:0] pc_sel,
    input logic [XLEN-1:0] pc_redirect_target,

    //
    // Branch prediction from ID stage
    //
    input logic [XLEN-1:0] pred_target,

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
    // PC for BTB lookup
    //
    output logic [XLEN-1:0] pc,

    //
    // Outputs to ID stage
    //
    output logic [    31:0] instr_id,
    output logic [XLEN-1:0] pc_id,
    output logic [XLEN-1:0] pc_plus4_id,
    output logic            btb_hit_id,
    output logic            btb_pred_taken_id,
    output logic [XLEN-1:0] btb_target_id,
    output logic            btb_is_return_id,
    output logic            ras_valid_id,
    output logic [XLEN-1:0] ras_target_id,

    //
    // Ready/valid interface to ID stage
    //
    output logic m_valid,
    input  logic m_ready
);

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc_next;
  logic [XLEN-1:0] pc_to_if_id;
  logic [XLEN-1:0] pc_plus4_to_if_id;
  logic            btb_hit_to_if_id;
  logic            btb_pred_taken_to_if_id;
  logic [XLEN-1:0] btb_target_to_if_id;
  logic            btb_is_return_to_if_id;
  logic            ras_valid_to_if_id;
  logic [XLEN-1:0] ras_target_to_if_id;
  logic            valid_to_if_id;

  //
  // PC initialization
  //
  // For BRAM with BPRED, PC starts at RESET_PC-4 so that pc_next = RESET_PC
  // on first cycle
  //
  localparam logic [XLEN-1:0] PC_INIT =
      (MEM_TYPE == MEM_TYPE_BRAM && BPRED != 0) ? RESET_PC - 4 : RESET_PC;

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
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= PC_INIT;
    end else if (!pc_stall) begin
      pc <= pc_next;
    end
  end

  //
  // Memory-type specific fetch logic
  //
  if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_bram
    svc_rv_stage_if_bram #(
        .XLEN (XLEN),
        .BPRED(BPRED)
    ) stage (
        .*
    );
  end else begin : g_sram
    svc_rv_stage_if_sram #(
        .XLEN     (XLEN),
        .PIPELINED(PIPELINED)
    ) stage (
        .*
    );
  end

  //
  // IF/ID Pipeline Register (PC and BTB only, not instruction)
  //
  // Instruction and valid are already buffered in the stage-specific modules
  // and drive outputs directly to avoid double-buffering.
  //
  if (PIPELINED != 0) begin : g_registered
    logic [XLEN-1:0] pc_id_buf;
    logic [XLEN-1:0] pc_plus4_id_buf;

    always_ff @(posedge clk) begin
      if (!if_id_stall) begin
        pc_id_buf       <= pc_to_if_id;
        pc_plus4_id_buf <= pc_plus4_to_if_id;
      end
    end

    assign pc_id       = pc_id_buf;
    assign pc_plus4_id = pc_plus4_id_buf;

    //
    // BTB and RAS signal buffering
    //
    svc_rv_bpred_if #(
        .XLEN     (XLEN),
        .PIPELINED(PIPELINED),
        .MEM_TYPE (MEM_TYPE)
    ) bpred (
        .*
    );

  end else begin : g_passthrough
    assign pc_id       = pc_to_if_id;
    assign pc_plus4_id = pc_plus4_to_if_id;

    //
    // BTB and RAS passthrough for non-pipelined
    //
    svc_rv_bpred_if #(
        .XLEN     (XLEN),
        .PIPELINED(PIPELINED),
        .MEM_TYPE (MEM_TYPE)
    ) bpred (
        .*
    );
  end

  //
  // Ready/valid output
  //
  // m_valid indicates a valid instruction is ready to transfer to ID.
  // m_ready is unused - stall logic still uses if_id_stall.
  //
  assign m_valid = valid_to_if_id;

  `SVC_UNUSED(m_ready);

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
  // m_valid/m_ready handshake assertions (output interface)
  //
  // NOTE: The IF stage does not yet implement proper ready/valid buffering.
  // Currently m_valid can drop unexpectedly due to flush.
  // The full protocol will be implemented when if_id_stall is replaced with
  // proper backpressure via m_ready.
  //
  // Unlike strict AXI-style valid/ready, pipeline flush/kill is allowed to
  // drop m_valid even when m_ready is low. This is intentional - flush is
  // orthogonal to flow control and gates m_valid to create bubbles.
  //
  // TODO: Add assertion once IF stage implements proper ready/valid buffering:
  // if ($past(m_valid && !m_ready)) begin
  //   assert(m_valid || if_id_flush);
  // end
  //

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
