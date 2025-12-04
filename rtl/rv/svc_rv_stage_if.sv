`ifndef SVC_RV_STAGE_IF_SV
`define SVC_RV_STAGE_IF_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Instruction Fetch (IF) Stage
//
// Supports two modes:
// - PIPELINED=1: Buffers PC and metadata, expects synchronous memory interface
// - PIPELINED=0: Passthrough for single-cycle execution
//
// Uses imem_rvalid from memory subsystem to determine when instruction is valid.
//
module svc_rv_stage_if #(
    parameter int          XLEN      = 32,
    parameter int          PIPELINED = 1,
    parameter int          BPRED     = 0,
    parameter logic [31:0] RESET_PC  = 32'h0000_0000
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic if_id_flush,

    //
    // Ready/valid interface from PC stage
    //
    input  logic s_valid,
    output logic s_ready,

    //
    // PC inputs from stage_pc
    //
    input logic [XLEN-1:0] pc,
    input logic [XLEN-1:0] pc_next,

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
    output logic        imem_arvalid,
    output logic [31:0] imem_araddr,
    input  logic [31:0] imem_rdata,
    input  logic        imem_rvalid,

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

  logic [31:0] instr;
  logic        flush_extend;

  //
  // Ready signal to PC stage
  //
  // Backpressure from downstream: accept new PC when ID stage can accept.
  // Stall conditions (data hazards, multi-cycle ops) flow through ID's
  // s_ready via id_stall, so we don't need pc_stall here.
  //
  assign s_ready = m_ready;

  //
  // Intermediate signals for pipeline register inputs
  //
  logic [XLEN-1:0] pc_to_if_id;
  logic [XLEN-1:0] pc_plus4_to_if_id;
  logic            btb_hit_to_if_id;
  logic            btb_pred_taken_to_if_id;
  logic [XLEN-1:0] btb_target_to_if_id;
  logic            btb_is_return_to_if_id;
  logic            ras_valid_to_if_id;
  logic [XLEN-1:0] ras_target_to_if_id;

  // =========================================================================
  // Instruction memory interface
  // =========================================================================
  //
  // Pipelined with BPRED: Use pc_next for early speculative fetch
  // Pipelined without BPRED: Use pc for normal fetch
  // Single-cycle: Use pc, always enabled
  //
  assign instr = imem_rdata;

  if (PIPELINED != 0 && BPRED != 0) begin : g_pipelined_bpred_imem
    //
    // BPRED mode: !rst_n ensures first-cycle fetch when PC starts at
    // RESET_PC-4 and pc_next = RESET_PC
    //
    assign imem_araddr  = pc_next;
    assign imem_arvalid = !rst_n || m_ready;

    //
    // In BPRED mode, pc goes to BTB from stage_pc, not used here
    //
    `SVC_UNUSED({pc})
  end else if (PIPELINED != 0) begin : g_pipelined_imem
    assign imem_araddr  = pc;
    assign imem_arvalid = m_ready;

    `SVC_UNUSED({pc_next})
  end else begin : g_single_cycle_imem
    assign imem_araddr  = pc;
    assign imem_arvalid = 1'b1;

    `SVC_UNUSED({pc_next})
  end

  //
  // s_valid from stage_pc is unused for now - stage_pc.m_valid is always 1
  // This will be used in step 6.3 when we add proper flow control
  //
  `SVC_UNUSED({s_valid})

  // =========================================================================
  // Extended flush for pipelined mode without BPRED
  // =========================================================================
  //
  // Without BPRED: Sequential instruction is already fetched before redirect
  // is detected, so we need flush_extend to clear the stale instruction.
  //
  // With BPRED: Target is fetched immediately when prediction happens,
  // so flush_extend would incorrectly flush the CORRECT target instruction.
  //
  if (PIPELINED != 0 && BPRED == 0) begin : g_flush_extend
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        flush_extend <= 1'b0;
      end else begin
        flush_extend <= if_id_flush;
      end
    end
  end else begin : g_no_flush_extend
    assign flush_extend = 1'b0;
  end

  // =========================================================================
  // PC and metadata handling
  // =========================================================================
  //
  // Pipelined: Buffer by one cycle to align with instruction
  // Single-cycle: Passthrough (instruction available same cycle)
  //
  if (PIPELINED != 0) begin : g_pipelined_metadata
    (* max_fanout = 32 *)logic [XLEN-1:0] pc_buf;
    (* max_fanout = 32 *)logic [XLEN-1:0] pc_plus4_buf;
    logic            btb_hit_buf;
    logic            btb_pred_taken_buf;
    logic [XLEN-1:0] btb_target_buf;
    logic            btb_is_return_buf;
    logic            ras_valid_buf;
    logic [XLEN-1:0] ras_target_buf;

    //
    // Control signals: need reset for correct behavior
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        btb_hit_buf        <= 1'b0;
        btb_pred_taken_buf <= 1'b0;
        btb_is_return_buf  <= 1'b0;
        ras_valid_buf      <= 1'b0;
      end else if (m_ready) begin
        btb_hit_buf        <= btb_hit_if;
        btb_pred_taken_buf <= btb_pred_taken_if;
        btb_is_return_buf  <= btb_is_return_if;
        ras_valid_buf      <= ras_valid_if;
      end
    end

    //
    // Datapath registers: no reset needed (don't care until valid)
    //
    always_ff @(posedge clk) begin
      if (m_ready) begin
        pc_buf         <= imem_araddr;
        pc_plus4_buf   <= imem_araddr + 4;
        btb_target_buf <= btb_target_if;
        ras_target_buf <= ras_target_if;
      end
    end

    assign pc_to_if_id             = pc_buf;
    assign pc_plus4_to_if_id       = pc_plus4_buf;
    assign btb_hit_to_if_id        = btb_hit_buf;
    assign btb_pred_taken_to_if_id = btb_pred_taken_buf;
    assign btb_target_to_if_id     = btb_target_buf;
    assign btb_is_return_to_if_id  = btb_is_return_buf;
    assign ras_valid_to_if_id      = ras_valid_buf;
    assign ras_target_to_if_id     = ras_target_buf;

  end else begin : g_single_cycle_metadata
    //
    // Single-cycle: Passthrough (instruction available same cycle)
    //
    assign pc_to_if_id             = pc;
    assign pc_plus4_to_if_id       = pc + 4;
    assign btb_hit_to_if_id        = btb_hit_if;
    assign btb_pred_taken_to_if_id = btb_pred_taken_if;
    assign btb_target_to_if_id     = btb_target_if;
    assign btb_is_return_to_if_id  = btb_is_return_if;
    assign ras_valid_to_if_id      = ras_valid_if;
    assign ras_target_to_if_id     = ras_target_if;
  end

  // =========================================================================
  // Instruction buffering and validity
  // =========================================================================
  if (PIPELINED != 0) begin : g_pipelined
    logic [31:0] instr_buf;
    logic        valid_buf;

    //
    // Instruction buffering with stall support and extended flush
    //
    always_ff @(posedge clk) begin
      if (!rst_n || if_id_flush || flush_extend) begin
        instr_buf <= I_NOP;
      end else if (m_ready) begin
        instr_buf <= instr;
      end
    end

    //
    // Validity tracking using imem_rvalid
    //
    // imem_rvalid arrives after the synchronous memory responds.
    // We set valid_buf to 1 when rvalid arrives, preserving it during stalls.
    //
    always_ff @(posedge clk) begin
      if (!rst_n || if_id_flush || flush_extend) begin
        valid_buf <= 1'b0;
      end else if (m_ready && imem_rvalid) begin
        valid_buf <= 1'b1;
      end
    end

    assign instr_id = instr_buf;
    assign m_valid  = valid_buf;

    // =====================================================================
    // IF/ID Pipeline Registers
    // =====================================================================
    logic [XLEN-1:0] pc_id_buf;
    logic [XLEN-1:0] pc_plus4_id_buf;

    always_ff @(posedge clk) begin
      if (m_ready) begin
        pc_id_buf       <= pc_to_if_id;
        pc_plus4_id_buf <= pc_plus4_to_if_id;
      end
    end

    assign pc_id             = pc_id_buf;
    assign pc_plus4_id       = pc_plus4_id_buf;

    //
    // BTB and RAS signals to IF/ID pipeline register
    //
    // Metadata is already buffered by g_pipelined_metadata, passthrough here.
    //
    assign btb_hit_id        = btb_hit_to_if_id;
    assign btb_pred_taken_id = btb_pred_taken_to_if_id;
    assign btb_target_id     = btb_target_to_if_id;
    assign btb_is_return_id  = btb_is_return_to_if_id;
    assign ras_valid_id      = ras_valid_to_if_id;
    assign ras_target_id     = ras_target_to_if_id;

  end else begin : g_non_pipelined
    //
    // Non-pipelined: Passthrough everything
    //
    assign instr_id          = instr;
    assign m_valid           = imem_rvalid;
    assign pc_id             = pc_to_if_id;
    assign pc_plus4_id       = pc_plus4_to_if_id;
    assign btb_hit_id        = btb_hit_to_if_id;
    assign btb_pred_taken_id = btb_pred_taken_to_if_id;
    assign btb_target_id     = btb_target_to_if_id;
    assign btb_is_return_id  = btb_is_return_to_if_id;
    assign ras_valid_id      = ras_valid_to_if_id;
    assign ras_target_id     = ras_target_to_if_id;

    `SVC_UNUSED({if_id_flush, m_ready, flush_extend, instr})
  end

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
  // Unlike strict AXI-style valid/ready, pipeline flush/kill is allowed to
  // drop m_valid even when m_ready is low. This is intentional - flush is
  // orthogonal to flow control and gates m_valid to create bubbles.
  //
  //
  // flush_extend is an internal signal that clears the pipeline in
  // non-BPRED pipelined mode. Include it in the flush condition.
  //
  logic f_flush;
  assign f_flush = if_id_flush || flush_extend;

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(m_valid && !m_ready && !f_flush)) begin
        //
        // Valid must remain asserted until ready (unless flushed)
        //
        `FASSERT(a_valid_stable, m_valid || f_flush);

        //
        // Payload signals must remain stable
        //
        `FASSERT(a_instr_stable, instr_id == $past(instr_id));
        `FASSERT(a_pc_stable, pc_id == $past(pc_id));
        `FASSERT(a_pc_plus4_stable, pc_plus4_id == $past(pc_plus4_id));
        `FASSERT(a_btb_hit_stable, btb_hit_id == $past(btb_hit_id));
        `FASSERT(a_btb_pred_taken_stable, btb_pred_taken_id == $past(
                 btb_pred_taken_id));
        `FASSERT(a_btb_target_stable, btb_target_id == $past(btb_target_id));
        `FASSERT(a_btb_is_return_stable, btb_is_return_id == $past(
                 btb_is_return_id));
        `FASSERT(a_ras_valid_stable, ras_valid_id == $past(ras_valid_id));
        `FASSERT(a_ras_target_stable, ras_target_id == $past(ras_target_id));
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
