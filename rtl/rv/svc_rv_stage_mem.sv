`ifndef SVC_RV_STAGE_MEM_SV
`define SVC_RV_STAGE_MEM_SV

`include "svc.sv"
`include "svc_unused.sv"

`include "svc_rv_fmt_ld.sv"
`include "svc_rv_fmt_st.sv"
`include "svc_rv_ext_mul_mem.sv"
`include "svc_rv_bpred_mem.sv"
`include "svc_rv_pipe_ctrl.sv"
`include "svc_rv_pipe_data.sv"

//
// RISC-V Memory (MEM) Stage
//
// Encapsulates all logic for the memory access pipeline stage:
// - Load data formatting and sign extension
// - Store data formatting and byte lane generation
// - Data memory interface
// - Result selection for forwarding
// - MEM/WB pipeline register
//
module svc_rv_stage_mem #(
    parameter int XLEN       = 32,
    parameter int PIPELINED  = 1,
    parameter int MEM_TYPE   = 0,
    parameter int BPRED      = 0,
    parameter int RAS_ENABLE = 0
) (
    input logic clk,
    input logic rst_n,

    // Valid interface from EX stage
    input logic instr_valid_mem,

    // Stall
    input logic stall_mem,

    // From EX stage
    input logic            reg_write_mem,
    input logic            mem_read_mem,
    input logic            mem_write_mem,
    input logic [     2:0] res_src_mem,
    input logic [    31:0] instr_mem,
    input logic [     4:0] rd_mem,
    input logic [     2:0] funct3_mem,
    input logic [XLEN-1:0] alu_result_mem,
    input logic [XLEN-1:0] rs1_data_mem,
    input logic [XLEN-1:0] rs2_data_mem,
    input logic [XLEN-1:0] pc_plus4_mem,
    input logic [XLEN-1:0] jb_tgt_mem,
    input logic [XLEN-1:0] csr_rdata_mem,
    input logic [XLEN-1:0] m_result_mem,
    input logic [XLEN-1:0] mul_ll_mem,
    input logic [XLEN-1:0] mul_lh_mem,
    input logic [XLEN-1:0] mul_hl_mem,
    input logic [XLEN-1:0] mul_hh_mem,
    input logic            is_branch_mem,
    input logic            is_jalr_mem,
    input logic            is_jmp_mem,
    input logic            branch_taken_mem,
    input logic            bpred_taken_mem,
    input logic [XLEN-1:0] pred_tgt_mem,
    input logic            trap_mem,
    input logic [     1:0] trap_code_mem,
    input logic            is_ebreak_mem,

    // Data memory interface
    output logic        dmem_ren,
    output logic [31:0] dmem_raddr,
    input  logic [31:0] dmem_rdata,
    output logic        dmem_we,
    output logic [31:0] dmem_waddr,
    output logic [31:0] dmem_wdata,
    output logic [ 3:0] dmem_wstrb,

    // Outputs to WB stage
    output logic            instr_valid_wb,
    output logic            reg_write_wb,
    output logic [     2:0] res_src_wb,
    output logic [    31:0] instr_wb,
    output logic [     4:0] rd_wb,
    output logic [     2:0] funct3_wb,
    output logic [XLEN-1:0] alu_result_wb,
    output logic [XLEN-1:0] rs1_data_wb,
    output logic [XLEN-1:0] rs2_data_wb,
    output logic [XLEN-1:0] ld_data_wb,
    output logic [XLEN-1:0] pc_plus4_wb,
    output logic [XLEN-1:0] jb_tgt_wb,
    output logic [XLEN-1:0] csr_rdata_wb,
    output logic [XLEN-1:0] m_result_wb,
    output logic [    63:0] product_64_wb,
    output logic            trap_wb,
    output logic [     1:0] trap_code_wb,
    output logic            is_ebreak_wb,

`ifdef RISCV_FORMAL
    output logic            f_mem_write_wb,
    output logic [XLEN-1:0] f_dmem_waddr_wb,
    output logic [XLEN-1:0] f_dmem_raddr_wb,
    output logic [XLEN-1:0] f_dmem_wdata_wb,
    output logic [     3:0] f_dmem_wstrb_wb,
    output logic [XLEN-1:0] f_dmem_rdata_wb,
    output logic [     3:0] f_dmem_rstrb_wb,
    output logic            f_is_branch_wb,
    output logic            f_is_jmp_wb,
    output logic            f_branch_taken_wb,
`endif

    // Outputs for forwarding (MEM stage result)
    output logic [XLEN-1:0] result_mem,
    output logic [XLEN-1:0] ld_data_mem,

    // RAS update outputs
    output logic            ras_push_en,
    output logic [XLEN-1:0] ras_push_addr,
    output logic            ras_pop_en,

    // Branch/JALR misprediction detection and PC control (MEM stage)
    output logic            redir_valid_mem,
    output logic [XLEN-1:0] redir_tgt_mem
);

  `include "svc_rv_defs.svh"

  // Instruction accepted into stage (MEM always accepts, stall handles flow)
  logic s_accept;
  assign s_accept = instr_valid_mem;

  //===========================================================================
  // Store data formatting
  //===========================================================================
  logic [3:0] st_fmt_wstrb;

  svc_rv_fmt_st #(
      .XLEN(XLEN)
  ) st_fmt (
      .data_in (rs2_data_mem),
      .addr    (alu_result_mem[1:0]),
      .funct3  (funct3_mem),
      .data_out(dmem_wdata),
      .wstrb   (st_fmt_wstrb)
  );

  //===========================================================================
  // Trap detection (MEM stage)
  //===========================================================================
  logic       misalign_trap;
  logic [1:0] funct3_size;
  logic       halfword_misalign;
  logic       word_misalign;
  logic       mem_misalign;

  assign funct3_size       = funct3_mem[1:0];
  assign halfword_misalign = alu_result_mem[0];
  assign word_misalign     = |alu_result_mem[1:0];

  always_comb begin
    mem_misalign = 1'b0;

    if (mem_read_mem || mem_write_mem) begin
      case (funct3_size)
        2'b01:   mem_misalign = halfword_misalign;
        2'b10:   mem_misalign = word_misalign;
        default: mem_misalign = 1'b0;
      endcase
    end
  end

  assign misalign_trap = trap_mem | mem_misalign;

  //===========================================================================
  // Data memory interface
  //
  // Suppress memory operations on misalignment trap
  //===========================================================================

  //
  // When the pipeline is stalled (e.g., instruction cache miss), hold off
  // issuing new memory enables. This prevents BRAM read data from being
  // overwritten by younger loads while an older load sits in WB.
  //
  logic mem_req_en;
  assign mem_req_en = s_accept && !stall_mem;

  assign dmem_ren   = mem_req_en && mem_read_mem && !misalign_trap;
  assign dmem_raddr = {alu_result_mem[31:2], 2'b00};

  assign dmem_we    = mem_req_en && mem_write_mem && !misalign_trap;
  assign dmem_waddr = {alu_result_mem[31:2], 2'b00};
  assign dmem_wstrb = mem_write_mem ? st_fmt_wstrb : 4'b0000;

  //===========================================================================
  // Load data extension
  //
  // For SRAM: Format in MEM stage (combinational memory)
  // For BRAM: Format in WB stage (registered memory)
  //===========================================================================
  logic [     1:0] ld_fmt_addr;
  logic [     2:0] ld_fmt_funct3;
  logic [XLEN-1:0] ld_fmt_out;

`ifdef RISCV_FORMAL
  logic [3:0] f_ld_fmt_rstrb;
`endif

  if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_ld_fmt_signals_sram
    assign ld_fmt_addr   = alu_result_mem[1:0];
    assign ld_fmt_funct3 = funct3_mem;
    assign ld_data_mem   = ld_fmt_out;

  end else begin : g_ld_fmt_signals_bram
    // Use funct3_wb from pipeline registers for BRAM load formatting
    assign ld_fmt_addr   = alu_result_wb[1:0];
    assign ld_fmt_funct3 = funct3_wb;

    // BRAM: load data not available in MEM stage (no forwarding)
    assign ld_data_mem   = '0;
  end

  svc_rv_fmt_ld #(
      .XLEN(XLEN)
  ) ld_fmt (
      .data_in (dmem_rdata),
      .addr    (ld_fmt_addr),
      .funct3  (ld_fmt_funct3),
`ifdef RISCV_FORMAL
      .f_rstrb (f_ld_fmt_rstrb),
`endif
      .data_out(ld_fmt_out)
  );

  //===========================================================================
  // MEM stage result for forwarding
  //
  // Select the actual result in MEM stage based on res_src_mem.
  // This unified result is forwarded to resolve data hazards.
  //
  // RES_M: M extension result (division only - multiply not forwarded from MEM)
  // RES_PC4: PC+4 (used by JAL/JALR)
  // RES_TGT: Jump/branch target (used by AUIPC)
  // Default: ALU result (most instructions)
  //
  // Note: Multiply results are not forwarded from MEM (completed in WB stage).
  // Division results are in m_result_mem and can be forwarded.
  //===========================================================================
  always_comb begin
    case (res_src_mem)
      RES_M:   result_mem = m_result_mem;
      RES_PC4: result_mem = pc_plus4_mem;
      RES_TGT: result_mem = jb_tgt_mem;
      default: result_mem = alu_result_mem;
    endcase
  end

  //===========================================================================
  // RAS Update Logic
  //
  // Detect JAL/JALR instructions and generate push/pop signals for RAS
  // - Push: JAL or JALR with rd != x0 (call instructions)
  // - Pop: JALR (return instructions)
  // - Push address: PC+4 (return address)
  //===========================================================================
  assign ras_push_en   = s_accept && is_jmp_mem && (rd_mem != 5'b0);
  assign ras_push_addr = pc_plus4_mem;
  assign ras_pop_en    = s_accept && is_jalr_mem;

  //===========================================================================
  // JALR misprediction detection (MEM stage)
  //
  // Moved from EX stage to break critical timing path:
  // forwarding → ALU → JALR target → comparison → PC
  //===========================================================================
  logic branch_mispredicted_mem;
  logic jalr_mispredicted_mem;

  svc_rv_bpred_mem #(
      .XLEN      (XLEN),
      .BPRED     (BPRED),
      .RAS_ENABLE(RAS_ENABLE)
  ) bpred_mem (
      .is_branch_mem          (is_branch_mem),
      .branch_taken_mem       (branch_taken_mem),
      .is_jalr_mem            (is_jalr_mem),
      .bpred_taken_mem        (bpred_taken_mem),
      .jb_tgt_mem             (jb_tgt_mem),
      .pred_tgt_mem           (pred_tgt_mem),
      .branch_mispredicted_mem(branch_mispredicted_mem),
      .jalr_mispredicted_mem  (jalr_mispredicted_mem)
  );

  //===========================================================================
  // PC redirect target calculation
  //
  // On branch misprediction:
  // - If predicted taken but actually not-taken: redirect to pc + 4
  // - If predicted not-taken but actually taken: redirect to jb_tgt
  //
  // On JALR misprediction: redirect to jb_tgt
  //===========================================================================
  logic mispred_not_taken;
  assign mispred_not_taken = branch_mispredicted_mem && !branch_taken_mem;

  logic [XLEN-1:0] pc_redir_tgt_comb;
  always_comb begin
    pc_redir_tgt_comb = jb_tgt_mem;
    if (mispred_not_taken) begin
      pc_redir_tgt_comb = pc_plus4_mem;
    end
  end

  //===========================================================================
  // Redirect output
  //
  // Redirect is always accepted immediately - no handshake needed.
  // On misprediction, younger instructions (causing stalls) will be flushed,
  // so redirect should not wait for them.
  //===========================================================================
  assign redir_valid_mem = (s_accept &&
                            (branch_mispredicted_mem | jalr_mispredicted_mem));
  assign redir_tgt_mem = pc_redir_tgt_comb;

  //===========================================================================
  // M Extension MEM stage: combine partial products
  //===========================================================================
  logic [63:0] product_64_mem;

  svc_rv_ext_mul_mem ext_mul_mem (
      .mul_ll    (mul_ll_mem),
      .mul_lh    (mul_lh_mem),
      .mul_hl    (mul_hl_mem),
      .mul_hh    (mul_hh_mem),
      .div_result(m_result_mem),
      .product_64(product_64_mem)
  );

  //===========================================================================
  // MEM/WB Pipeline
  //===========================================================================
  logic pipe_advance_o;
  logic pipe_flush_o;
  logic pipe_bubble_o;

  svc_rv_pipe_ctrl #(
      .REG(PIPELINED)
  ) pipe_ctrl (
      .clk      (clk),
      .rst_n    (rst_n),
      .stall_i  (stall_mem),
      .flush_i  (1'b0),
      .bubble_i (!instr_valid_mem),
      .advance_o(pipe_advance_o),
      .flush_o  (pipe_flush_o),
      .bubble_o (pipe_bubble_o)
  );

  //
  // Control signals (WITH bubble)
  //
  // These trigger actions (regfile write, trap handling) so they must be
  // cleared when invalid. This allows downstream to use them directly
  // without re-checking valid.
  //
  svc_rv_pipe_data #(
      .WIDTH(3),
      .REG  (PIPELINED)
  ) pipe_ctrl_data (
      .clk(clk),
      .rst_n(rst_n),
      .advance(pipe_advance_o),
      .flush(pipe_flush_o),
      .bubble(pipe_bubble_o),
      .data_i({
        instr_valid_mem, reg_write_mem && !misalign_trap, misalign_trap
      }),
      .data_o({instr_valid_wb, reg_write_wb, trap_wb})
  );

  //
  // Payload signals (NO bubble) - can be stale
  //
  localparam int PAYLOAD_WIDTH = 3 + 32 + 5 + 3 + 7 * XLEN + 64 + 2 + 1;

  svc_rv_pipe_data #(
      .WIDTH(PAYLOAD_WIDTH),
      .REG  (PIPELINED)
  ) pipe_payload_data (
      .clk(clk),
      .rst_n(rst_n),
      .advance(pipe_advance_o),
      .flush(1'b0),
      .bubble(1'b0),
      .data_i({
        res_src_mem,
        instr_mem,
        rd_mem,
        funct3_mem,
        alu_result_mem,
        rs1_data_mem,
        rs2_data_mem,
        pc_plus4_mem,
        jb_tgt_mem,
        csr_rdata_mem,
        m_result_mem,
        product_64_mem,
        is_ebreak_mem,
        mem_misalign ? TRAP_LDST_MISALIGN : trap_code_mem
      }),
      .data_o({
        res_src_wb,
        instr_wb,
        rd_wb,
        funct3_wb,
        alu_result_wb,
        rs1_data_wb,
        rs2_data_wb,
        pc_plus4_wb,
        jb_tgt_wb,
        csr_rdata_wb,
        m_result_wb,
        product_64_wb,
        is_ebreak_wb,
        trap_code_wb
      })
  );

  //===========================================================================
  // Load data to WB stage
  //
  // BRAM: formatter uses WB-stage signals, ld_fmt_out is WB-timed, passthrough
  // SRAM pipelined: formatter uses MEM-stage signals, needs pipeline register
  // SRAM single-cycle: formatter uses MEM-stage signals, passthrough
  //===========================================================================
  localparam bit LD_DATA_REG = (PIPELINED != 0) && (MEM_TYPE == MEM_TYPE_SRAM);

  svc_rv_pipe_data #(
      .WIDTH(XLEN),
      .REG  (LD_DATA_REG)
  ) pipe_ld_data (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance_o),
      .flush  (1'b0),
      .bubble (pipe_bubble_o),
      .data_i (ld_fmt_out),
      .data_o (ld_data_wb)
  );



  //===========================================================================
  // RVFI mem addrs
  //
  // dmem_we fires for the INPUT instruction, but f_mem_write_wb must track
  // the OUTPUT instruction (in sync with instr_wb). We use two-stage tracking:
  // - pending_store: set when dmem_we fires (INPUT has actual store)
  // - f_mem_write_wb: set from pending_store when pipeline advances (OUTPUT)
  //
  // This ensures stores that trap (dmem_we=0) are correctly reported as
  // non-stores, while keeping f_mem_write_wb in sync with instr_wb.
  //===========================================================================
`ifdef RISCV_FORMAL
  if (PIPELINED != 0) begin : g_rvfi_store_pipelined
    // Pending registers to capture memory operation data when initiated,
    // then transfer to output when the pipeline advances. This handles the
    // case where a new memory op fires before the previous one retires.
    logic            f_pending_store;
    logic [XLEN-1:0] f_pending_waddr;
    logic [XLEN-1:0] f_pending_wdata;
    logic [     3:0] f_pending_wstrb;
    logic            f_pending_load;
    logic [XLEN-1:0] f_pending_raddr;

    always_ff @(posedge clk) begin
      if (!rst_n) begin
        f_pending_store <= 1'b0;
        f_pending_waddr <= '0;
        f_pending_wdata <= '0;
        f_pending_wstrb <= '0;
        f_pending_load  <= 1'b0;
        f_pending_raddr <= '0;
        f_mem_write_wb  <= 1'b0;
        f_dmem_waddr_wb <= '0;
        f_dmem_raddr_wb <= '0;
        f_dmem_wdata_wb <= '0;
        f_dmem_wstrb_wb <= '0;
      end else if (pipe_flush_o) begin
        f_pending_store <= 1'b0;
        f_pending_load  <= 1'b0;
        f_mem_write_wb  <= 1'b0;
        f_dmem_wstrb_wb <= '0;
      end else begin
        // Track dmem_we for INPUT store instruction - capture to pending
        if (dmem_we) begin
          f_pending_store <= 1'b1;
          f_pending_waddr <= dmem_waddr;
          f_pending_wdata <= dmem_wdata;
          f_pending_wstrb <= dmem_wstrb;
        end

        // Track dmem_ren for INPUT load instruction - capture to pending
        if (dmem_ren) begin
          f_pending_load  <= 1'b1;
          f_pending_raddr <= dmem_raddr;
        end

        // Transfer to OUTPUT when pipeline advances
        if (pipe_advance_o) begin
          // Transfer store: use current dmem signals if store is advancing
          // in same cycle (no stall), otherwise use pending. This handles
          // the race where dmem_we and pipe_advance_o fire simultaneously.
          if (dmem_we) begin
            f_mem_write_wb  <= 1'b1;
            f_dmem_waddr_wb <= dmem_waddr;
            f_dmem_wdata_wb <= dmem_wdata;
            f_dmem_wstrb_wb <= dmem_wstrb;
          end else if (f_pending_store) begin
            f_mem_write_wb  <= 1'b1;
            f_dmem_waddr_wb <= f_pending_waddr;
            f_dmem_wdata_wb <= f_pending_wdata;
            f_dmem_wstrb_wb <= f_pending_wstrb;
          end else begin
            f_mem_write_wb  <= 1'b0;
            f_dmem_wstrb_wb <= '0;
          end
          f_pending_store <= 1'b0;

          // Transfer load address: use current dmem_raddr if load is
          // advancing in same cycle, otherwise use pending.
          if (dmem_ren) begin
            f_dmem_raddr_wb <= dmem_raddr;
          end else if (f_pending_load) begin
            f_dmem_raddr_wb <= f_pending_raddr;
          end
          f_pending_load <= 1'b0;
        end
      end
    end
  end else begin : g_rvfi_store_passthrough
    assign f_mem_write_wb  = mem_write_mem;
    assign f_dmem_waddr_wb = dmem_waddr;
    assign f_dmem_raddr_wb = dmem_raddr;
    assign f_dmem_wdata_wb = dmem_wdata;
    assign f_dmem_wstrb_wb = dmem_wstrb;
  end

  //===========================================================================
  // RVFI load data - use pipe_data with MEM_TYPE-aware policy
  //
  // BRAM: passthrough (memory has 1-cycle latency)
  // SRAM: needs pipeline register (combinational memory)
  //
  // TODO: pass ld_rstrb as f_ signal from formatter instead of recomputing
  //===========================================================================
  localparam
      bit RVFI_RDATA_REG = (PIPELINED != 0) && (MEM_TYPE == MEM_TYPE_SRAM);

  // Gate signal for rmask - must match timing of f_ld_fmt_rstrb
  logic f_is_load_for_rstrb;
  if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_rstrb_gate_bram
    // BRAM: f_ld_fmt_rstrb uses WB-stage signals, gate with WB timing
    assign f_is_load_for_rstrb = (res_src_wb == RES_MEM);
  end else begin : g_rstrb_gate_sram
    // SRAM: f_ld_fmt_rstrb uses MEM-stage signals, gate with MEM timing
    assign f_is_load_for_rstrb = mem_read_mem;
  end

  svc_rv_pipe_data #(
      .WIDTH(XLEN + 4),
      .REG  (RVFI_RDATA_REG)
  ) pipe_rvfi_rdata (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance_o),
      .flush  (pipe_flush_o),
      .bubble (pipe_bubble_o),
      .data_i ({dmem_rdata, f_is_load_for_rstrb ? f_ld_fmt_rstrb : 4'b0}),
      .data_o ({f_dmem_rdata_wb, f_dmem_rstrb_wb})
  );

  //===========================================================================
  // RVFI branch/jump signals for arch_next_pc computation
  //===========================================================================
  svc_rv_pipe_data #(
      .WIDTH(3),
      .REG  (PIPELINED)
  ) pipe_rvfi_branch (
      .clk    (clk),
      .rst_n  (rst_n),
      .advance(pipe_advance_o),
      .flush  (pipe_flush_o),
      .bubble (pipe_bubble_o),
      .data_i ({is_branch_mem, is_jmp_mem, branch_taken_mem}),
      .data_o ({f_is_branch_wb, f_is_jmp_wb, f_branch_taken_wb})
  );
`endif

  //
  // Formal verification
  //
`ifdef FORMAL
`ifdef FORMAL_SVC_RV_STAGE_MEM
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
  // instr_valid_wb stability during stall
  //
  // When stalled, instr_valid_wb must stay stable (unless flushed)
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if ($past(stall_mem && instr_valid_wb)) begin
        `FASSERT(a_instr_valid_stable_stall, instr_valid_wb);
      end
    end
  end

  //
  // Cover properties
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // back-to-back valid transfers
      `FCOVER(c_back_to_back, $past(instr_valid_wb) && instr_valid_wb);

      // stalled transfer (stall_mem active)
      `FCOVER(c_stalled, $past(stall_mem && instr_valid_wb) && instr_valid_wb);

      // redirect triggered (only reachable with BPRED enabled)
      if (BPRED != 0) begin
        `FCOVER(c_redir, redir_valid_mem);
      end
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
