`ifndef SVC_RV_STAGE_MEM_SV
`define SVC_RV_STAGE_MEM_SV

`include "svc.sv"
`include "svc_unused.sv"

`include "svc_rv_fmt_ld.sv"
`include "svc_rv_fmt_st.sv"
`include "svc_rv_ext_mul_mem.sv"
`include "svc_rv_bpred_mem.sv"

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
// This stage handles memory accesses and forwards results to the
// writeback stage.
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

    //
    // From EX stage
    //
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
    input logic [XLEN-1:0] jb_target_mem,
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
    input logic [XLEN-1:0] pred_target_mem,
    input logic            trap_mem,
    input logic [     1:0] trap_code_mem,

    //
    // Ready/valid interface from EX stage
    //
    input  logic s_valid,
    output logic s_ready,

    //
    // Data memory interface
    //
    output logic        dmem_ren,
    output logic [31:0] dmem_raddr,
    input  logic [31:0] dmem_rdata,
    output logic        dmem_we,
    output logic [31:0] dmem_waddr,
    output logic [31:0] dmem_wdata,
    output logic [ 3:0] dmem_wstrb,

    //
    // Outputs to WB stage
    //
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
    output logic [XLEN-1:0] jb_target_wb,
    output logic [XLEN-1:0] csr_rdata_wb,
    output logic [XLEN-1:0] m_result_wb,
    output logic [    63:0] product_64_wb,
    output logic            trap_wb,
    output logic [     1:0] trap_code_wb,

`ifdef RISCV_FORMAL
    output logic            f_mem_write_wb,
    output logic [XLEN-1:0] f_dmem_waddr_wb,
    output logic [XLEN-1:0] f_dmem_raddr_wb,
    output logic [XLEN-1:0] f_dmem_wdata_wb,
    output logic [     3:0] f_dmem_wstrb_wb,
    output logic [XLEN-1:0] f_dmem_rdata_wb,
    output logic [     3:0] f_dmem_rstrb_wb,
`endif

    //
    // Ready/valid interface to WB stage
    //
    output logic m_valid,
    input  logic m_ready,

    //
    // Outputs for forwarding (MEM stage result)
    //
    output logic [XLEN-1:0] result_mem,
    output logic [XLEN-1:0] load_data_mem,

    //
    // RAS update outputs
    //
    output logic            ras_push_en,
    output logic [XLEN-1:0] ras_push_addr,
    output logic            ras_pop_en,

    //
    // Branch/JALR misprediction detection and PC control (MEM stage)
    //
    output logic            jalr_mispredicted_mem,
    output logic            mispredicted_mem,
    output logic [XLEN-1:0] pc_redirect_target_mem
);

  `include "svc_rv_defs.svh"

  //
  // Handshake: instruction accepted into stage
  //
  logic s_accept;
  assign s_accept = s_valid && s_ready;

  //
  // Store data formatting
  //
  // Stores use rs2_data_mem, which comes from fwd_rs2_ex in EX stage.
  // This means stores automatically get forwarded values.
  //
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

  assign dmem_wstrb = mem_write_mem ? st_fmt_wstrb : 4'b0000;

  //
  // Trap detection (MEM stage)
  //
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

  //
  // Data memory interface
  //
  // Suppress memory operations on misalignment trap
  //
  // Memory addresses are word-aligned (bits[1:0] cleared).
  // Byte strobes indicate which bytes within the word are accessed.
  //
  assign dmem_ren      = s_accept && mem_read_mem && !misalign_trap;
  assign dmem_raddr    = {alu_result_mem[31:2], 2'b00};

  assign dmem_we       = s_accept && mem_write_mem && !misalign_trap;
  assign dmem_waddr    = {alu_result_mem[31:2], 2'b00};

  //
  // Load data extension
  //
  // For SRAM: Format in MEM stage (combinational memory)
  // For BRAM: Format in WB stage (registered memory)
  //
  logic [XLEN-1:0] ld_data_mem;

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
    //
    // Use funct3_wb from pipeline registers for BRAM load formatting
    //
    assign ld_fmt_addr   = alu_result_wb[1:0];
    assign ld_fmt_funct3 = funct3_wb;

    //
    // BRAM formatter output is already WB-stage timed
    //
    assign ld_data_mem   = '0;
    assign ld_data_wb    = ld_fmt_out;
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

  //
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
  //
  always_comb begin
    case (res_src_mem)
      RES_M:   result_mem = m_result_mem;
      RES_PC4: result_mem = pc_plus4_mem;
      RES_TGT: result_mem = jb_target_mem;
      default: result_mem = alu_result_mem;
    endcase
  end

  assign load_data_mem = ld_data_mem;

  // RAS Update Logic
  //
  // Detect JAL/JALR instructions and generate push/pop signals for RAS
  // - Push: JAL or JALR with rd != x0 (call instructions)
  // - Pop: JALR (return instructions)
  // - Push address: PC+4 (return address)
  assign ras_push_en   = s_accept && is_jmp_mem && (rd_mem != 5'b0);
  assign ras_push_addr = pc_plus4_mem;
  assign ras_pop_en    = s_accept && is_jalr_mem;

  // JALR misprediction detection (MEM stage)
  //
  // Moved from EX stage to break critical timing path:
  // forwarding → ALU → JALR target → comparison → PC
  logic branch_mispredicted_mem;

  svc_rv_bpred_mem #(
      .XLEN      (XLEN),
      .BPRED     (BPRED),
      .RAS_ENABLE(RAS_ENABLE)
  ) bpred_mem (
      .is_branch_mem          (is_branch_mem),
      .branch_taken_mem       (branch_taken_mem),
      .is_jalr_mem            (is_jalr_mem),
      .bpred_taken_mem        (bpred_taken_mem),
      .jb_target_mem          (jb_target_mem),
      .pred_target_mem        (pred_target_mem),
      .branch_mispredicted_mem(branch_mispredicted_mem),
      .jalr_mispredicted_mem  (jalr_mispredicted_mem)
  );

  // Combined misprediction signal
  assign mispredicted_mem = (s_accept &&
                             (branch_mispredicted_mem | jalr_mispredicted_mem));

  // PC redirect target calculation
  //
  // On branch misprediction:
  // - If predicted taken but actually not-taken: redirect to pc + 4
  // - If predicted not-taken but actually taken: redirect to jb_target
  //
  // On JALR misprediction: redirect to jb_target
  //
  logic mispred_not_taken;
  assign mispred_not_taken = branch_mispredicted_mem && !branch_taken_mem;

  always_comb begin
    pc_redirect_target_mem = jb_target_mem;
    if (mispred_not_taken) begin
      // Branch was predicted taken but is actually not-taken
      // Redirect to sequential PC (already in jb_target for branches)
      pc_redirect_target_mem = pc_plus4_mem;
    end
  end

  //
  // M Extension MEM stage: combine partial products
  //
  logic [63:0] product_64_mem;

  svc_rv_ext_mul_mem ext_mul_mem (
      .mul_ll    (mul_ll_mem),
      .mul_lh    (mul_lh_mem),
      .mul_hl    (mul_hl_mem),
      .mul_hh    (mul_hh_mem),
      .div_result(m_result_mem),
      .product_64(product_64_mem)
  );

  //
  // MEM/WB Pipeline Register
  //
  if (PIPELINED != 0) begin : g_registered
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        m_valid <= 1'b0;
      end else if (!m_valid || m_ready) begin
        m_valid <= s_valid;
      end
    end

    //
    // payload
    //
    always_ff @(posedge clk) begin
      if (!m_valid || m_ready) begin
        reg_write_wb  <= reg_write_mem && !misalign_trap;
        res_src_wb    <= res_src_mem;
        instr_wb      <= instr_mem;
        rd_wb         <= rd_mem;
        funct3_wb     <= funct3_mem;
        alu_result_wb <= alu_result_mem;
        rs1_data_wb   <= rs1_data_mem;
        rs2_data_wb   <= rs2_data_mem;
        pc_plus4_wb   <= pc_plus4_mem;
        jb_target_wb  <= jb_target_mem;
        csr_rdata_wb  <= csr_rdata_mem;
        m_result_wb   <= m_result_mem;
        product_64_wb <= product_64_mem;
        trap_wb       <= misalign_trap;
        trap_code_wb  <= (mem_misalign ? TRAP_LDST_MISALIGN : trap_code_mem);
      end
    end

    //
    // Pipeline SRAM load data
    //
    // BRAM data is already assigned in the formatter section above
    //
    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_dmem_rdata_sram
      logic [XLEN-1:0] ld_data_wb_piped;

      always_ff @(posedge clk) begin
        if (!m_valid || m_ready) begin
          ld_data_wb_piped <= ld_data_mem;
        end
      end

      assign ld_data_wb = ld_data_wb_piped;
    end

`ifdef RISCV_FORMAL
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        f_mem_write_wb  <= 1'b0;
        f_dmem_waddr_wb <= '0;
        f_dmem_raddr_wb <= '0;
        f_dmem_wdata_wb <= '0;
        f_dmem_wstrb_wb <= '0;
      end else if (dmem_we) begin
        // dmem_we only pulses high for one cycle per write (for MMIO safety).
        // During stalls, mem_write_mem gets cleared but we must preserve the
        // write info for RVFI. Capture here before it's lost.
        f_mem_write_wb  <= 1'b1;
        f_dmem_waddr_wb <= dmem_waddr;
        f_dmem_raddr_wb <= dmem_raddr;
        f_dmem_wdata_wb <= dmem_wdata;
        f_dmem_wstrb_wb <= dmem_wstrb;
      end else begin
        //
        // Clear write signals when the store retires. This ensures the write
        // info is captured by the lag buffer BEFORE clearing.
        //
        // Using m_valid (the retiring instruction) instead of valid_mem (the
        // advancing instruction) ensures proper timing for both:
        // - Stores followed by multi-cycle ops (wmask preserved until
        //   retirement)
        // - Non-stores after multi-cycle ops (wmask cleared after store
        //   retired)
        //
        if (m_valid && f_mem_write_wb) begin
          f_mem_write_wb  <= 1'b0;
          f_dmem_wstrb_wb <= '0;
        end

        //
        // Update address/data signals when pipeline advances (for loads).
        //
        if (!m_valid || m_ready) begin
          f_dmem_waddr_wb <= dmem_waddr;
          f_dmem_raddr_wb <= dmem_raddr;
          f_dmem_wdata_wb <= dmem_wdata;
        end
      end
    end

    // BRAM: dmem_rdata is already WB-stage timed (1-cycle latency)
    // SRAM: dmem_rdata is MEM-stage timed, needs registering
    if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_f_dmem_rdata_bram
      assign f_dmem_rdata_wb = dmem_rdata;
      assign f_dmem_rstrb_wb = f_ld_fmt_rstrb;
    end else begin : g_f_dmem_rdata_sram
      always_ff @(posedge clk) begin
        if (!rst_n) begin
          f_dmem_rdata_wb <= '0;
          f_dmem_rstrb_wb <= '0;
        end else if (!m_valid || m_ready) begin
          f_dmem_rdata_wb <= dmem_rdata;
          f_dmem_rstrb_wb <= f_ld_fmt_rstrb;
        end
      end
    end
`endif

  end else begin : g_passthrough
    assign reg_write_wb  = reg_write_mem && !misalign_trap;
    assign res_src_wb    = res_src_mem;
    assign instr_wb      = instr_mem;
    assign rd_wb         = rd_mem;
    assign funct3_wb     = funct3_mem;
    assign alu_result_wb = alu_result_mem;
    assign rs1_data_wb   = rs1_data_mem;
    assign rs2_data_wb   = rs2_data_mem;
    assign pc_plus4_wb   = pc_plus4_mem;
    assign jb_target_wb  = jb_target_mem;
    assign csr_rdata_wb  = csr_rdata_mem;
    assign m_result_wb   = m_result_mem;
    assign product_64_wb = product_64_mem;
    assign trap_wb       = misalign_trap;
    assign trap_code_wb  = mem_misalign ? TRAP_LDST_MISALIGN : trap_code_mem;
    assign m_valid       = s_valid;

    //
    // Pass through SRAM load data
    //
    // BRAM data is already assigned in the formatter section above
    //
    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_dmem_rdata_sram
      assign ld_data_wb = ld_data_mem;
    end

`ifdef RISCV_FORMAL
    assign f_mem_write_wb  = mem_write_mem;
    assign f_dmem_waddr_wb = dmem_waddr;
    assign f_dmem_raddr_wb = dmem_raddr;
    assign f_dmem_wdata_wb = dmem_wdata;
    assign f_dmem_wstrb_wb = dmem_wstrb;
    assign f_dmem_rdata_wb = dmem_rdata;
    assign f_dmem_rstrb_wb = f_ld_fmt_rstrb;
`endif

    `SVC_UNUSED({clk, rst_n});
  end

  //
  // Ready/valid interface (from EX stage)
  //
  // s_ready: For now, pass through from WB (m_ready).
  //          Later with cache: s_ready = m_ready && !cache_busy
  // s_valid: Used for misprediction gating and m_valid pipeline register.
  //
  assign s_ready = m_ready;

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
  // m_valid/m_ready handshake assertions
  //
  // Once m_valid goes high, it must stay high until m_ready
  // All output signals must remain stable while m_valid && !m_ready
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      //
      // Valid must stay high until ready
      //
      if ($past(m_valid && !m_ready)) begin
        `FASSERT(a_m_valid_stable, m_valid);
      end

      //
      // Output signals must be stable while valid && !ready
      //
      if ($past(m_valid && !m_ready)) begin
        `FASSERT(a_reg_write_wb_stable, $stable(reg_write_wb));
        `FASSERT(a_res_src_wb_stable, $stable(res_src_wb));
        `FASSERT(a_instr_wb_stable, $stable(instr_wb));
        `FASSERT(a_rd_wb_stable, $stable(rd_wb));
        `FASSERT(a_funct3_wb_stable, $stable(funct3_wb));
        `FASSERT(a_alu_result_wb_stable, $stable(alu_result_wb));
        `FASSERT(a_pc_plus4_wb_stable, $stable(pc_plus4_wb));
        `FASSERT(a_jb_target_wb_stable, $stable(jb_target_wb));
        `FASSERT(a_trap_wb_stable, $stable(trap_wb));
        `FASSERT(a_trap_code_wb_stable, $stable(trap_code_wb));
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
