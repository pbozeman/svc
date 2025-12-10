`ifndef SVC_RV_STAGE_IF_SV
`define SVC_RV_STAGE_IF_SV

`include "svc.sv"
`include "svc_unused.sv"
`include "svc_sync_fifo.sv"

//
// RISC-V Instruction Fetch (IF) Stage
//
// Supports two modes:
// - PIPELINED=1: Uses FIFOs to buffer PC, instruction, and metadata
// - PIPELINED=0: Passthrough for single-cycle execution
//
module svc_rv_stage_if #(
    parameter int XLEN      = 32,
    parameter int PIPELINED = 1,
    parameter int BPRED     = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic if_id_flush,

    //
    // PC inputs from stage_pc
    //
    input  logic s_valid,
    output logic s_ready,

    input logic [XLEN-1:0] pc_if,
    input logic [XLEN-1:0] pc_next_if,

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
    output logic m_valid,
    input  logic m_ready,

    output logic [    31:0] instr_id,
    output logic [XLEN-1:0] pc_id,
    output logic [XLEN-1:0] pc_plus4_id,
    output logic            btb_hit_id,
    output logic            btb_pred_taken_id,
    output logic [XLEN-1:0] btb_target_id,
    output logic            btb_is_return_id,
    output logic            ras_valid_id,
    output logic [XLEN-1:0] ras_target_id
);

  `include "svc_rv_defs.svh"

  logic [31:0] instr;
  logic        flush_extend;

  //
  // Ready signal to PC stage
  //
  // Backpressure from downstream and internal FIFOs.
  //
  logic        pc_fifo_ready;

  assign s_ready = m_ready && pc_fifo_ready;

  // =========================================================================
  // Instruction memory interface
  // =========================================================================
  //
  // Pipelined with BPRED: Use pc_next for early speculative fetch
  // Pipelined without BPRED: Use pc for normal fetch
  // Single-cycle: Use pc, always enabled
  //
  assign instr   = imem_rdata;

  if (PIPELINED != 0 && BPRED != 0) begin : g_pipelined_bpred_imem
    //
    // BPRED mode: !rst_n ensures first-cycle fetch when PC starts at
    // RESET_PC-4 and pc_next_if = RESET_PC
    //
    assign imem_araddr  = pc_next_if;
    assign imem_arvalid = !rst_n || (s_valid && s_ready);

    //
    // In BPRED mode, pc goes to BTB from stage_pc, not used here
    //
    `SVC_UNUSED({pc_if})
  end else if (PIPELINED != 0) begin : g_pipelined_imem
    assign imem_araddr  = pc_if;
    assign imem_arvalid = s_valid && s_ready;

    `SVC_UNUSED({pc_next_if})
  end else begin : g_single_cycle_imem
    assign imem_araddr  = pc_if;
    assign imem_arvalid = s_valid;

    `SVC_UNUSED({pc_next_if, s_ready})
  end

  // =========================================================================
  // Extended flush for pipelined mode without BPRED
  // =========================================================================
  //
  // Without BPRED: Sequential instruction is already fetched before redirect
  // is detected, so we need flush_extend to clear the stale instruction.
  //
  // TODO: I think we can likely drop flush_extend now that we have the
  // fifo design. The corresponding queues will have been flushed,
  // so the read should get tossed.
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
  // FIFO control signals
  // =========================================================================
  logic fifo_clr;
  logic pc_fifo_valid;
  logic aligned_pc_fifo_valid;
  logic instr_fifo_valid;
  logic meta_fifo_valid;

  assign fifo_clr = if_id_flush || flush_extend;

  // =========================================================================
  // PC FIFO
  // =========================================================================
  logic [XLEN-1:0] pc_id_next;
  logic [XLEN-1:0] pc_plus4_id_next;

  if (PIPELINED != 0) begin : g_pc_fifo
    logic [XLEN-1:0] pc_fifo_rdata;
    logic            pc_fifo_empty;
    logic            pc_fifo_half_full;

    assign pc_fifo_valid = !pc_fifo_empty;

    svc_sync_fifo #(
        .ADDR_WIDTH(2),
        .DATA_WIDTH(XLEN)
    ) pc_fifo (
        .clk        (clk),
        .rst_n      (rst_n),
        .clr        (fifo_clr),
        .w_inc      (s_valid && s_ready),
        .w_data     (imem_araddr),
        .w_full     (),
        .w_half_full(pc_fifo_half_full),
        .r_inc      (imem_rvalid && !fifo_clr && pc_fifo_valid),
        .r_empty    (pc_fifo_empty),
        .r_data     (pc_fifo_rdata)
    );

    assign pc_fifo_ready = !pc_fifo_half_full;

    //
    // Aligned PC FIFO - push from pc_fifo when imem_rvalid arrives
    //
    // TODO: try to remove this second fifo. It doesn't seem like
    // it should be necessary. If it is, add a more comprehensive
    // comment
    //
    logic            aligned_pc_fifo_empty;
    logic            aligned_pc_fifo_half_full;
    logic [XLEN-1:0] aligned_pc_fifo_rdata;

    assign aligned_pc_fifo_valid = !aligned_pc_fifo_empty;

    svc_sync_fifo #(
        .ADDR_WIDTH(2),
        .DATA_WIDTH(XLEN)
    ) aligned_pc_fifo (
        .clk        (clk),
        .rst_n      (rst_n),
        .clr        (fifo_clr),
        .w_inc      (imem_rvalid && !fifo_clr && pc_fifo_valid),
        .w_data     (pc_fifo_rdata),
        .w_full     (),
        .w_half_full(aligned_pc_fifo_half_full),
        .r_inc      (m_valid && m_ready && aligned_pc_fifo_valid),
        .r_empty    (aligned_pc_fifo_empty),
        .r_data     (aligned_pc_fifo_rdata)
    );

    `SVC_UNUSED({aligned_pc_fifo_half_full})

    assign pc_id_next       = aligned_pc_fifo_rdata;
    assign pc_plus4_id_next = aligned_pc_fifo_rdata + 4;


  end else begin : g_no_pc_fifo
    assign pc_fifo_ready         = 1'b1;
    assign pc_fifo_valid         = '0;
    assign aligned_pc_fifo_valid = '0;
    assign pc_id_next            = '0;
    assign pc_plus4_id_next      = '0;
  end

  // =========================================================================
  // Instruction FIFO
  // =========================================================================
  logic [31:0] instr_id_next;

  if (PIPELINED != 0) begin : g_instr_fifo
    logic [31:0] instr_fifo_rdata;
    logic        instr_fifo_empty;
    logic        instr_fifo_half_full;

    assign instr_fifo_valid = !instr_fifo_empty;

    svc_sync_fifo #(
        .ADDR_WIDTH(2),
        .DATA_WIDTH(32)
    ) instr_fifo (
        .clk        (clk),
        .rst_n      (rst_n),
        .clr        (fifo_clr),
        .w_inc      (imem_rvalid && !fifo_clr && pc_fifo_valid),
        .w_data     (imem_rdata),
        .w_full     (),
        .w_half_full(instr_fifo_half_full),
        .r_inc      (m_valid && m_ready && instr_fifo_valid),
        .r_empty    (instr_fifo_empty),
        .r_data     (instr_fifo_rdata)
    );

    `SVC_UNUSED({instr_fifo_half_full})

    //
    // Output NOP when FIFO empty (reset behavior)
    //
    assign instr_id_next = instr_fifo_valid ? instr_fifo_rdata : 32'h00000013;

  end else begin : g_no_instr_fifo
    assign instr_fifo_valid = '0;
    assign instr_id_next    = '0;
  end

  // =========================================================================
  // BTB/RAS Metadata FIFO
  // =========================================================================
  localparam META_WIDTH = 1 + 1 + XLEN + 1 + 1 + XLEN;

  logic            btb_hit_id_next;
  logic            btb_pred_taken_id_next;
  logic [XLEN-1:0] btb_target_id_next;
  logic            btb_is_return_id_next;
  logic            ras_valid_id_next;
  logic [XLEN-1:0] ras_target_id_next;

  if (PIPELINED != 0) begin : g_meta_fifo
    logic [META_WIDTH-1:0] meta_fifo_wdata;
    logic [META_WIDTH-1:0] meta_fifo_rdata;
    logic                  meta_fifo_empty;

    assign meta_fifo_valid = !meta_fifo_empty;

    assign meta_fifo_wdata = {
      btb_hit_if,
      btb_pred_taken_if,
      btb_target_if,
      btb_is_return_if,
      ras_valid_if,
      ras_target_if
    };

    svc_sync_fifo #(
        .ADDR_WIDTH(2),
        .DATA_WIDTH(META_WIDTH)
    ) meta_fifo (
        .clk        (clk),
        .rst_n      (rst_n),
        .clr        (fifo_clr),
        .w_inc      (s_valid && s_ready && !fifo_clr),
        .w_data     (meta_fifo_wdata),
        .w_full     (),
        .w_half_full(),
        .r_inc      (m_valid && m_ready && meta_fifo_valid),
        .r_empty    (meta_fifo_empty),
        .r_data     (meta_fifo_rdata)
    );

    assign {btb_hit_id_next, btb_pred_taken_id_next, btb_target_id_next,
            btb_is_return_id_next, ras_valid_id_next, ras_target_id_next} =
        meta_fifo_rdata;

    //
    // FIFO validity check (simulation only, not formal)
    //
`ifndef SYNTHESIS
`ifndef FORMAL
    always @(posedge clk) begin
      if (rst_n && m_valid) begin
        if (!aligned_pc_fifo_valid) begin
          $fatal(0, "m_valid but aligned_pc_fifo empty");
        end
        if (!instr_fifo_valid) begin
          $fatal(0, "m_valid but instr_fifo empty");
        end
        if (!meta_fifo_valid) begin
          $fatal(0, "m_valid but meta_fifo empty");
        end
      end

      if (rst_n) begin
        if (g_pc_fifo.aligned_pc_fifo_half_full !=
            g_instr_fifo.instr_fifo_half_full) begin
          $fatal(0, "aligned_pc_fifo and instr_fifo half_full mismatch");
        end
      end
    end
`endif
`endif

  end else begin : g_no_meta_fifo
    assign meta_fifo_valid        = '0;
    assign btb_hit_id_next        = '0;
    assign btb_pred_taken_id_next = '0;
    assign btb_target_id_next     = '0;
    assign btb_is_return_id_next  = '0;
    assign ras_valid_id_next      = '0;
    assign ras_target_id_next     = '0;
  end

  // =========================================================================
  // Output assignments and validity
  // =========================================================================
  if (PIPELINED != 0) begin : g_pipelined
    assign m_valid           = aligned_pc_fifo_valid && instr_fifo_valid;
    assign instr_id          = instr_id_next;
    assign pc_id             = pc_id_next;
    assign pc_plus4_id       = pc_plus4_id_next;
    assign btb_hit_id        = btb_hit_id_next;
    assign btb_pred_taken_id = btb_pred_taken_id_next;
    assign btb_target_id     = btb_target_id_next;
    assign btb_is_return_id  = btb_is_return_id_next;
    assign ras_valid_id      = ras_valid_id_next;
    assign ras_target_id     = ras_target_id_next;

    `SVC_UNUSED({instr})

  end else begin : g_non_pipelined
    //
    // Non-pipelined: Passthrough everything
    //
    assign m_valid           = imem_rvalid;
    assign instr_id          = instr;
    assign pc_id             = pc_if;
    assign pc_plus4_id       = pc_if + 4;
    assign btb_hit_id        = btb_hit_if;
    assign btb_pred_taken_id = btb_pred_taken_if;
    assign btb_target_id     = btb_target_if;
    assign btb_is_return_id  = btb_is_return_if;
    assign ras_valid_id      = ras_valid_if;
    assign ras_target_id     = ras_target_if;

    //
    // FIFO signals are only used in pipelined mode
    //
    // verilog_format: off
   `SVC_UNUSED({clk, rst_n, if_id_flush, m_ready, flush_extend, fifo_clr,
                 pc_fifo_valid, aligned_pc_fifo_valid,
                 instr_fifo_valid, meta_fifo_valid,
                 pc_id_next, pc_plus4_id_next, instr_id_next,
                 btb_hit_id_next, btb_pred_taken_id_next, btb_target_id_next,
                 btb_is_return_id_next, ras_valid_id_next, ras_target_id_next});
    // verilog_format: on
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
  // Require 2 cycles of reset at start to initialize all state
  //
  logic f_past_valid2 = 1'b0;

  always @(posedge clk) begin
    f_past_valid2 <= f_past_valid;
  end

  always_ff @(posedge clk) begin
    if (!f_past_valid2) begin
      assume (!rst_n);
    end
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
  // During flush (including extended flush), upstream shouldn't send valid
  // data. This prevents the FIFO clr+w_inc behavior from putting data in
  // hardware FIFOs while shadow queue is being reset.
  //
  // TODO: when all passing, remove this and decide how to handle it
  //
  always_ff @(posedge clk) begin
    if (rst_n && (if_id_flush || flush_extend)) begin
      assume (!s_valid);
    end
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

  //
  // Verify imem_araddr matches expected value based on BPRED parameter
  //
  if (PIPELINED != 0) begin : g_f_imem_check
    always_ff @(posedge clk) begin
      if (f_past_valid && rst_n && imem_arvalid) begin
        if (BPRED != 0) begin
          `FASSERT(a_imem_addr_bpred, imem_araddr == pc_next_if);
        end else begin
          `FASSERT(a_imem_addr_no_bpred, imem_araddr == pc_if);
        end
      end
    end
  end

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
      // Cover back-to-back valid transfers
      `FCOVER(c_back_to_back, $past(m_valid && m_ready) && m_valid);

      // Cover stalled transfer (valid high, ready low for a cycle)
      `FCOVER(c_stalled, $past(m_valid && !m_ready) && m_valid && m_ready);
    end
  end

  //
  // Input stability: data must be held when s_valid && !s_ready
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(s_valid && !s_ready)) begin
        `FASSUME(a_in_pc_stable, pc_if == $past(pc_if));
        `FASSUME(a_in_btb_hit_stable, btb_hit_if == $past(btb_hit_if));
        `FASSUME(a_in_btb_pred_taken_stable, btb_pred_taken_if == $past(
                 btb_pred_taken_if));
        `FASSUME(a_in_btb_target_stable, btb_target_if == $past(btb_target_if));
        `FASSUME(a_in_btb_is_return_stable, btb_is_return_if == $past(
                 btb_is_return_if));
        `FASSUME(a_in_ras_valid_stable, ras_valid_if == $past(ras_valid_if));
        `FASSUME(a_in_ras_target_stable, ras_target_if == $past(ras_target_if));
      end
    end
  end

  //
  // Formal verification: Input-to-Output Contract
  //
  // This verifies that inputs from PC stage are correctly delivered to ID
  // stage. IMPORTANT: Track TRUE INPUTS, NOT internal signals (imem_araddr,
  // pc_fifo_rdata, etc.). Tracking internal signals would miss bugs in how
  // inputs are transformed. The shadow queue captures what goes IN and
  // verifies it matches what comes OUT.
  //
  // Exception: In BPRED mode, we fetch pc_next_if (speculative), not pc_if.
  // The shadow queue tracks pc_next_if in BPRED mode, pc_if otherwise.
  //
  // With multiple outstanding requests, we need FIFOs to match which
  // input corresponds to which output. Push on request, pop on output.
  //
  localparam F_QUEUE_DEPTH = 4;

  logic [XLEN-1:0] f_pc_queue            [0:F_QUEUE_DEPTH-1];
  logic            f_btb_hit_queue       [0:F_QUEUE_DEPTH-1];
  logic            f_btb_pred_taken_queue[0:F_QUEUE_DEPTH-1];
  logic [XLEN-1:0] f_btb_target_queue    [0:F_QUEUE_DEPTH-1];
  logic            f_btb_is_return_queue [0:F_QUEUE_DEPTH-1];
  logic            f_ras_valid_queue     [0:F_QUEUE_DEPTH-1];
  logic [XLEN-1:0] f_ras_target_queue    [0:F_QUEUE_DEPTH-1];

  logic [     1:0] f_wr_ptr;
  logic [     1:0] f_rd_ptr;

  //
  // Push on request handshake (matching hardware pc_fifo/meta_fifo push)
  //
  always_ff @(posedge clk) begin
    if (!rst_n || if_id_flush || flush_extend) begin
      f_wr_ptr <= '0;
    end else if (s_valid && s_ready) begin
      //
      // Track imem_araddr directly - this is what hardware stores in pc_fifo
      //
      f_pc_queue[f_wr_ptr]             <= imem_araddr;
      f_btb_hit_queue[f_wr_ptr]        <= btb_hit_if;
      f_btb_pred_taken_queue[f_wr_ptr] <= btb_pred_taken_if;
      f_btb_target_queue[f_wr_ptr]     <= btb_target_if;
      f_btb_is_return_queue[f_wr_ptr]  <= btb_is_return_if;
      f_ras_valid_queue[f_wr_ptr]      <= ras_valid_if;
      f_ras_target_queue[f_wr_ptr]     <= ras_target_if;
      f_wr_ptr                         <= f_wr_ptr + 1;
    end
  end

  //
  // Pop and verify on output handshake
  //
  always_ff @(posedge clk) begin
    if (!rst_n || if_id_flush || flush_extend) begin
      f_rd_ptr <= '0;
    end else if (m_valid && m_ready) begin
      f_rd_ptr <= f_rd_ptr + 1;
    end
  end

  //
  // Track valid count - ensures assertions only fire when shadow queue
  // has data that was actually pushed (not arbitrary initial state)
  //
  logic [2:0] f_valid_count;

  always_ff @(posedge clk) begin
    if (!rst_n || if_id_flush || flush_extend) begin
      f_valid_count <= '0;
    end else begin
      case ({
        s_valid && s_ready, m_valid && m_ready
      })
        2'b10:   f_valid_count <= f_valid_count + 1;
        2'b01:   f_valid_count <= f_valid_count - 1;
        default: ;
      endcase
    end
  end

  //
  // Track total completions - ensures we only check after data has
  // fully propagated through both pc_fifo and aligned_pc_fifo
  //
  // TODO: this seems questionable
  //
  logic [3:0] f_total_completions;

  always_ff @(posedge clk) begin
    if (!rst_n || if_id_flush || flush_extend) begin
      f_total_completions <= '0;
    end else if (m_valid && m_ready) begin
      f_total_completions <= f_total_completions + 1;
    end
  end

  //
  // Data integrity assertions
  //
  // When output is valid, compare to the corresponding queued input.
  // Guard with f_valid_count to ensure shadow queue has tracked data.
  // Skip NOPs since PC doesn't matter for bubbles.
  //
  localparam logic [31:0] F_NOP = 32'h00000013;

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n && !if_id_flush) begin
      if (m_valid && m_ready && f_valid_count > 0 && instr_id != F_NOP) begin
        `FASSERT(a_pc_integrity, pc_id == f_pc_queue[f_rd_ptr]);
        `FASSERT(a_pc_plus4_integrity, pc_plus4_id == f_pc_queue[f_rd_ptr] + 4);
        `FASSERT(a_btb_hit_integrity, btb_hit_id == f_btb_hit_queue[f_rd_ptr]);
        `FASSERT(a_btb_pred_taken_integrity,
                 btb_pred_taken_id == f_btb_pred_taken_queue[f_rd_ptr]);
        `FASSERT(a_btb_target_integrity,
                 btb_target_id == f_btb_target_queue[f_rd_ptr]);
        `FASSERT(a_btb_is_return_integrity,
                 btb_is_return_id == f_btb_is_return_queue[f_rd_ptr]);
        `FASSERT(a_ras_valid_integrity,
                 ras_valid_id == f_ras_valid_queue[f_rd_ptr]);
        `FASSERT(a_ras_target_integrity,
                 ras_target_id == f_ras_target_queue[f_rd_ptr]);
      end
    end
  end

  //
  // Cover data flowing through pipeline
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `FCOVER(c_data_flow, $past(s_valid && s_ready) && m_valid && m_ready);

      // Cover input backpressure (s_valid && !s_ready)
      `FCOVER(c_input_backpressure, $past(s_valid && !s_ready));
    end
  end

  //
  // Cover integrity check exercised (non-NOP instruction verified)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (!if_id_flush) begin
        `FCOVER(c_integrity_checked,
                m_valid && m_ready && f_valid_count > 0 && instr_id != F_NOP);

        // Cover multiple entries in shadow queue
        `FCOVER(c_multiple_in_flight, f_valid_count > 1);
      end

      // Cover flush clearing tracked entries
      `FCOVER(c_flush_clears_tracked, if_id_flush && f_valid_count > 0);
    end
  end

  //
  // Mem latency tracking
  //
  logic [1:0] f_req_cycles;
  logic [1:0] f_outstanding;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_outstanding <= '0;
      f_req_cycles  <= '0;
    end else begin
      case ({
        s_valid && s_ready, imem_rvalid
      })
        2'b10:   f_outstanding <= f_outstanding + 1;
        2'b01:   f_outstanding <= f_outstanding - 1;
        default: ;
      endcase

      if (s_valid && s_ready) begin
        f_req_cycles <= '0;
      end else if (f_outstanding > 0 && f_req_cycles < 2'd3) begin
        f_req_cycles <= f_req_cycles + 1'b1;
      end
    end
  end

  //
  // imem_rvalid only fires when requests are outstanding
  //
  always_comb begin
    `FASSUME(a_rvalid_needs_outstanding, !imem_rvalid || f_outstanding > 0);
  end

  //
  // Cover 1, 2, and 3 cycle memory responses
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // 1-cycle response: imem_rvalid same cycle as request
      `FCOVER(c_mem_resp_1cyc, $past(s_valid && s_ready) && imem_rvalid);

      // 2-cycle response: imem_rvalid one cycle after request
      `FCOVER(c_mem_resp_2cyc,
              f_outstanding > 0 && f_req_cycles == 2'd1 && imem_rvalid);

      // 3-cycle response: imem_rvalid two cycles after request
      `FCOVER(c_mem_resp_3cyc,
              f_outstanding > 0 && f_req_cycles == 2'd2 && imem_rvalid);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
