`ifndef SVC_RV_STAGE_IF_SV
`define SVC_RV_STAGE_IF_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Instruction Fetch (IF) Stage
//
// Encapsulates all logic for the instruction fetch pipeline stage:
// - Program counter (PC) management
// - Instruction memory interface
// - Memory-type specific instruction fetch adapters (SRAM/BRAM)
// - IF/ID pipeline register for PC values
// - Branch prediction input handling
//
// This stage fetches instructions from memory and forwards them to the
// decode stage along with associated PC values.
//
module svc_rv_stage_if #(
    parameter int XLEN      = 32,
    parameter int PIPELINED = 0,
    parameter int MEM_TYPE  = 0
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
    // PC control from EX stage
    //
    input logic [     1:0] pc_sel,
    input logic [XLEN-1:0] pc_redirect_target,

    //
    // Branch prediction from ID stage
    //
    input logic [XLEN-1:0] pred_target,

    //
    // Instruction memory interface
    //
    output logic        imem_ren,
    output logic [31:0] imem_raddr,
    input  logic [31:0] imem_rdata,

    //
    // Outputs to ID stage
    //
    output logic [31:0] instr_id,
    output logic [31:0] pc_id,
    output logic [31:0] pc_plus4_id
);

  `include "svc_rv_defs.svh"

  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_plus4;
  logic [    31:0] instr;

  //
  // PC management
  //
  logic [XLEN-1:0] pc_next;

  assign pc_plus4 = pc + 4;

  //
  // PC next calculation with 3-way mux:
  // - PC_SEL_REDIRECT: Actual branch/jump or misprediction
  // - PC_SEL_PREDICTED: Predicted branch taken (speculative fetch)
  // - PC_SEL_SEQUENTIAL: Normal sequential execution (pc + 4)
  //
  always_comb begin
    case (pc_sel)
      PC_SEL_REDIRECT:   pc_next = pc_redirect_target;
      PC_SEL_PREDICTED:  pc_next = pred_target;
      PC_SEL_SEQUENTIAL: pc_next = pc_plus4;
      default:           pc_next = pc_plus4;
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= '0;
    end else if (!pc_stall) begin
      pc <= pc_next;
    end
  end

  //
  // Instruction memory interface
  //
  assign imem_raddr = pc;
  assign instr      = imem_rdata;

  //
  // Memory read enable
  //
  // For BRAM: Gated with PC stall to hold output
  // For SRAM: Always enabled
  //
  if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_bram_imem_ren
    assign imem_ren = !pc_stall;
  end else begin : g_sram_imem_ren
    assign imem_ren = 1'b1;
  end

  //
  // PC values for IF/ID register
  //
  // For BRAM: Need extra buffering to match 2-cycle instruction latency
  // For SRAM: Use PC directly
  //
  logic [XLEN-1:0] pc_to_if_id;
  logic [XLEN-1:0] pc_plus4_to_if_id;

  //
  // Memory-type specific instruction fetch adapter
  //
  if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_sram
    //
    // SRAM instruction fetch adapter
    //
    // Handles optional instruction registration for SRAM's 0-cycle latency
    //

    //
    // For SRAM: Pass PC directly to IF/ID register
    //
    assign pc_to_if_id       = pc;
    assign pc_plus4_to_if_id = pc_plus4;

    //
    // Instruction path
    //
    if (PIPELINED != 0) begin : g_registered
      logic [31:0] instr_buf;

      always_ff @(posedge clk) begin
        if (!rst_n || if_id_flush) begin
          instr_buf <= I_NOP;
        end else if (!if_id_stall) begin
          instr_buf <= instr;
        end
      end

      assign instr_id = instr_buf;
    end else begin : g_passthrough
      assign instr_id = instr;
    end

  end else begin : g_bram
    //
    // BRAM instruction fetch adapter
    //
    // Handles PC buffering and extended flush for BRAM's 1-cycle latency
    //
    logic [XLEN-1:0] pc_buf;
    logic [XLEN-1:0] pc_plus4_buf;
    logic            flush_extend;
    logic [    31:0] instr_buf;

    //
    // PC buffering to match instruction latency
    //
    // BRAM has 2 cycles of instruction latency (BRAM output + instr_id register)
    // but IF/ID register only provides 1 cycle for PC
    // So we need to add one more cycle of PC buffering
    //
    // NOTE: PC buffer continues tracking even during flushes. Only instructions
    // are flushed to NOP, PC values must remain correct for pipeline tracking.
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        pc_buf       <= '0;
        pc_plus4_buf <= '0;
      end else if (!if_id_stall) begin
        pc_buf       <= pc;
        pc_plus4_buf <= pc_plus4;
      end
    end

    //
    // Output buffered PC values
    //
    assign pc_to_if_id       = pc_buf;
    assign pc_plus4_to_if_id = pc_plus4_buf;

    //
    // Extended flush for BRAM
    //
    // With BRAM's 1-cycle latency, when a branch is taken the BRAM output
    // contains a stale instruction for one more cycle. We need to extend the
    // flush signal to cover this case and insert NOPs for 2 cycles total.
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        flush_extend <= 1'b0;
      end else begin
        flush_extend <= if_id_flush;
      end
    end

    //
    // Instruction path with stall support and extended flush
    //
    always_ff @(posedge clk) begin
      if (!rst_n || if_id_flush || flush_extend) begin
        instr_buf <= I_NOP;
      end else if (!if_id_stall) begin
        instr_buf <= instr;
      end
    end

    assign instr_id = instr_buf;
  end

  //
  // IF/ID Pipeline Register for PC values
  //
  if (PIPELINED != 0) begin : g_registered_pc
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

  end else begin : g_passthrough_pc
    assign pc_id       = pc_to_if_id;
    assign pc_plus4_id = pc_plus4_to_if_id;

    `SVC_UNUSED({if_id_stall, if_id_flush})
  end

endmodule

`endif
