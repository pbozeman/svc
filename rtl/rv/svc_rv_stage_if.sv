`ifndef SVC_RV_STAGE_IF_SV
`define SVC_RV_STAGE_IF_SV

`include "svc.sv"
`include "svc_unused.sv"
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
    parameter int XLEN      = 32,
    parameter int PIPELINED = 0,
    parameter int MEM_TYPE  = 0,
    parameter int BPRED     = 0
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
    output logic            ras_valid_id,
    output logic [XLEN-1:0] ras_target_id
);

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc_next;
  logic [XLEN-1:0] pc_to_if_id;
  logic [XLEN-1:0] pc_plus4_to_if_id;
  logic            btb_hit_to_if_id;
  logic            btb_pred_taken_to_if_id;
  logic [XLEN-1:0] btb_target_to_if_id;
  logic            ras_valid_to_if_id;
  logic [XLEN-1:0] ras_target_to_if_id;

  //
  // PC initialization
  //
  // For BRAM with BPRED, PC starts at -4 so that pc_next = 0 on first cycle
  //
  localparam logic [XLEN-1:0]
      PC_INIT = (MEM_TYPE == MEM_TYPE_BRAM && BPRED != 0) ? 32'hFFFFFFFC : '0;

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
  // Instruction is already buffered in the stage-specific modules and
  // drives instr_id directly to avoid double-buffering.
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

endmodule

`endif
