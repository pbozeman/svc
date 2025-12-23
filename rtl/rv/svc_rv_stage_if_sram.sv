`ifndef SVC_RV_STAGE_IF_SRAM_SV
`define SVC_RV_STAGE_IF_SRAM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Instruction Fetch - SRAM Implementation
//
// SRAM has 0-cycle read latency. Instructions are available immediately
// in the same cycle the address is presented. No PC or BTB buffering needed.
//
module svc_rv_stage_if_sram #(
    parameter int XLEN,
    parameter int PIPELINED
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
    output logic        imem_ren,
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

  logic [XLEN-1:0] pc_plus4;
  logic [    31:0] instr;

  assign pc_plus4   = pc + 4;

  //
  // Instruction memory interface
  //
  // SRAM: Always enabled
  //
  assign imem_raddr = pc;
  assign instr      = imem_rdata;
  assign imem_ren   = 1'b1;

  //
  // Instruction, PC, and BTB/RAS buffering
  //
  // Optional buffering for pipelined mode. Each submodule handles its own
  // timing requirements - SRAM needs IF/ID pipeline registers here.
  //
  if (PIPELINED != 0) begin : g_registered
    logic [31:0] instr_buf;
    logic        valid_buf;

    //
    // Instruction buffer with stall-aware flush
    //
    // When stalled (advance=0), hold the buffer even if if_id_flush is
    // asserted. This prevents losing the predicting instruction (e.g., JAL)
    // when a prediction coincides with a stall. The flush takes effect
    // when the stall releases.
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        instr_buf <= I_NOP;
      end else if (advance) begin
        if (if_id_flush) begin
          instr_buf <= I_NOP;
        end else begin
          instr_buf <= instr;
        end
      end
    end

    assign instr_id = instr_buf;

    //
    // Instruction validity tracking
    //
    // Use valid_if from the PC stage to gate valid_buf. This ensures we
    // don't output valid when PC stage is generating a bubble (e.g., after
    // reset or stall release with PC_REG=1). This mirrors BRAM behavior
    // where valid_if gates imem_ren which feeds into fetch_started.
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        valid_buf <= 1'b0;
      end else if (advance) begin
        valid_buf <= valid_if && !if_id_flush;
      end
    end

    assign valid_ram = valid_buf;

    //
    // BTB/RAS buffering (control signals with reset/flush)
    //
    logic            btb_hit_buf;
    logic            btb_pred_taken_buf;
    logic [XLEN-1:0] btb_tgt_buf;
    logic            btb_is_return_buf;
    logic            ras_valid_buf;
    logic [XLEN-1:0] ras_tgt_buf;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        btb_hit_buf        <= 1'b0;
        btb_pred_taken_buf <= 1'b0;
        btb_is_return_buf  <= 1'b0;
        ras_valid_buf      <= 1'b0;
      end else if (if_id_flush) begin
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
    // Datapath registers (no reset needed)
    //
    always_ff @(posedge clk) begin
      if (advance) begin
        btb_tgt_buf <= btb_tgt_if;
        ras_tgt_buf <= ras_tgt_if;
      end
    end

    assign btb_hit_id        = btb_hit_buf;
    assign btb_pred_taken_id = btb_pred_taken_buf;
    assign btb_tgt_id        = btb_tgt_buf;
    assign btb_is_return_id  = btb_is_return_buf;
    assign ras_valid_id      = ras_valid_buf;
    assign ras_tgt_id        = ras_tgt_buf;


  end else begin : g_passthrough
    assign instr_id          = instr;
    assign valid_ram         = rst_n;

    //
    // Non-pipelined: direct passthrough
    //
    assign btb_hit_id        = btb_hit_if;
    assign btb_pred_taken_id = btb_pred_taken_if;
    assign btb_tgt_id        = btb_tgt_if;
    assign btb_is_return_id  = btb_is_return_if;
    assign ras_valid_id      = ras_valid_if;
    assign ras_tgt_id        = ras_tgt_if;

    `SVC_UNUSED({clk, valid_if, if_id_flush, advance})
  end

  //
  // PC passthrough (buffered in wrapper's IF/ID register)
  //
  assign pc_ram       = pc;
  assign pc_plus4_ram = pc_plus4;

endmodule

`endif
