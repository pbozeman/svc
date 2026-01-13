`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_unused.sv"

`include "svc_rv_btb.sv"
`include "svc_rv_ras.sv"
`include "svc_rv_bpred_id.sv"
`include "svc_rv_bpred_ex.sv"
`include "svc_rv_pc_sel.sv"
`include "svc_rv_hazard.sv"
`include "svc_rv_stage_pc.sv"
`include "svc_rv_stage_if.sv"
`include "svc_rv_stage_id.sv"
`include "svc_rv_stage_ex.sv"
`include "svc_rv_stage_mem.sv"
`include "svc_rv_stage_wb.sv"

//
// RISC-V RV32I Processor Core
//
// A configurable 5-stage pipelined RISC-V processor implementing the base
// RV32I instruction set with optional extensions.
//
// Pipeline stages:
// - IF:  Instruction Fetch
// - ID:  Instruction Decode
// - EX:  Execute
// - MEM: Memory Access
// - WB:  Write Back
//
// Features:
// - Configurable pipeline (combinational or fully pipelined)
// - Memory type support (SRAM with 0-cycle latency, BRAM with 1-cycle latency)
// - Optional data forwarding
// - Optional branch prediction (static BTFNT)
// - Optional M extension (multiply/divide)
// - Optional Zmmul extension (multiply-only)
// - Zicntr extension (performance counters)
//
module svc_rv #(
    parameter int          XLEN        = 32,
    parameter int          IMEM_AW     = 10,
    parameter int          DMEM_AW     = 10,
    parameter int          PIPELINED   = 0,
    parameter int          FWD_REGFILE = PIPELINED,
    parameter int          FWD         = 0,
    parameter int          MEM_TYPE    = 0,
    parameter int          BPRED       = 0,
    parameter int          BTB_ENABLE  = 0,
    parameter int          BTB_ENTRIES = 16,
    parameter int          RAS_ENABLE  = 0,
    parameter int          RAS_DEPTH   = 8,
    parameter int          EXT_ZMMUL   = 0,
    parameter int          EXT_M       = 0,
    parameter int          PC_REG      = 0,
    parameter logic [31:0] RESET_PC    = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Instruction memory interface (read-only)
    //
    output logic        imem_ren,
    output logic [31:0] imem_raddr,
    input  logic [31:0] imem_rdata,

    //
    // Data memory read interface
    //
    output logic        dmem_ren,
    output logic [31:0] dmem_raddr,
    input  logic [31:0] dmem_rdata,

    //
    // Data memory write interface
    //
    output logic        dmem_we,
    output logic [31:0] dmem_waddr,
    output logic [31:0] dmem_wdata,
    output logic [ 3:0] dmem_wstrb,

    //
    // Data memory stall (for cache miss)
    //
    input logic dmem_stall,

    //
    // Instruction memory stall (for cache miss)
    //
    input logic imem_stall,

`ifdef RISCV_FORMAL
    output logic        rvfi_valid,
    output logic [63:0] rvfi_order,
    output logic [31:0] rvfi_insn,
    output logic [31:0] rvfi_pc_rdata,
    output logic [31:0] rvfi_pc_wdata,
    output logic [ 4:0] rvfi_rs1_addr,
    output logic [ 4:0] rvfi_rs2_addr,
    output logic [ 4:0] rvfi_rd_addr,
    output logic [31:0] rvfi_rs1_rdata,
    output logic [31:0] rvfi_rs2_rdata,
    output logic [31:0] rvfi_rd_wdata,
    output logic        rvfi_trap,
    output logic        rvfi_halt,
    output logic        rvfi_intr,
    output logic [ 1:0] rvfi_mode,
    output logic [ 1:0] rvfi_ixl,
    output logic        rvfi_mem_valid,
    output logic        rvfi_mem_instr,
    output logic [31:0] rvfi_mem_addr,
    output logic [ 3:0] rvfi_mem_rmask,
    output logic [ 3:0] rvfi_mem_wmask,
    output logic [31:0] rvfi_mem_rdata,
    output logic [31:0] rvfi_mem_wdata,
`endif

    output logic ebreak,
    output logic trap
);

  `include "svc_rv_defs.svh"

  //
  // Parameter validation
  //
  initial begin
    if ((MEM_TYPE == MEM_TYPE_BRAM) && (PIPELINED == 0)) begin
      $fatal(1, "BRAM memory type requires PIPELINED=1");
    end
    if ((FWD_REGFILE == 1) && (PIPELINED == 0)) begin
      $fatal(1, "FWD_REGFILE=1 requires PIPELINED=1");
    end
    if ((FWD == 1) && (PIPELINED == 0)) begin
      $fatal(1, "FWD=1 requires PIPELINED=1");
    end
    if ((BPRED == 1) && (PIPELINED == 0)) begin
      $fatal(1, "BPRED=1 requires PIPELINED=1");
    end
    if ((BTB_ENABLE == 1) && (BPRED == 0)) begin
      $fatal(1, "BTB_ENABLE=1 requires BPRED=1");
    end
    if ((RAS_ENABLE == 1) && (BPRED == 0)) begin
      $fatal(1, "RAS_ENABLE=1 requires BPRED=1");
    end
    if ((RAS_ENABLE == 1) && (BTB_ENABLE == 0)) begin
      $fatal(1, "RAS_ENABLE=1 requires BTB_ENABLE=1");
    end
    if ((EXT_ZMMUL == 1) && (EXT_M == 1)) begin
      $fatal(1, "EXT_ZMMUL and EXT_M are mutually exclusive");
    end
    if ((EXT_M == 1) && (PIPELINED == 0) && (MEM_TYPE == MEM_TYPE_BRAM)) begin
      $fatal(1, "EXT_M with PIPELINED=0 requires MEM_TYPE=SRAM");
    end
    if ((PC_REG == 1) && (PIPELINED == 0)) begin
      $fatal(1, "PC_REG=1 requires PIPELINED=1");
    end
  end

  //
  // Inter-stage signals
  //

  // IF -> ID
  logic [    31:0] instr_id;
  logic [XLEN-1:0] pc_id;
  logic [XLEN-1:0] pc_plus4_id;

  // PC stage outputs
  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_if;
  logic [XLEN-1:0] pc_next_if;

  // PC -> IF
  logic            instr_valid_if;

  //
  // Redirect from MEM stage (misprediction)
  //
  // Redirect is always accepted immediately - no handshake needed.
  // On misprediction, younger instructions (causing stalls) will be flushed.
  //
  logic            redir_valid_mem;

  // ID -> EX
  logic            reg_write_ex;
  logic            mem_read_ex;
  logic            mem_write_ex;

  (* max_fanout = 32 *)logic [     1:0] alu_a_src_ex;
  (* max_fanout = 32 *)logic            alu_b_src_ex;

  logic [     1:0] alu_instr_ex;
  logic [     2:0] res_src_ex;
  logic            is_branch_ex;
  logic            is_jmp_ex;
  logic            jb_tgt_src_ex;
  logic            is_jal_ex;
  logic            is_jalr_ex;
  logic            is_mc_ex;
  logic            trap_ex;
  logic [     1:0] trap_code_ex;
  logic            is_ebreak_ex;
  logic [    31:0] instr_ex;
  logic [     4:0] rd_ex;
  logic [     4:0] rs1_ex;
  logic [     4:0] rs2_ex;
  logic [     2:0] funct3_ex;
  logic [     6:0] funct7_ex;
  logic [XLEN-1:0] rs1_data_ex;
  logic [XLEN-1:0] rs2_data_ex;
  logic [XLEN-1:0] imm_ex;
  logic [XLEN-1:0] pc_ex;
  logic [XLEN-1:0] pc_plus4_ex;
  logic            bpred_taken_ex;
  logic [XLEN-1:0] pred_tgt_ex;

  // ID -> Hazard
  logic [     4:0] rs1_id;
  logic [     4:0] rs2_id;
  logic            rs1_used_id;
  logic            rs2_used_id;
  logic            is_mc_id;

  // IF -> ID
  logic            instr_valid_id;

  // ID -> EX
  logic            instr_valid_ex;

  // EX -> MEM
  logic            instr_valid_mem;
  logic            reg_write_mem;
  logic            mem_read_mem;
  logic            mem_write_mem;
  logic [     2:0] res_src_mem;
  logic [    31:0] instr_mem;
  logic [     4:0] rd_mem;
  logic [     4:0] rs2_mem;
  logic [     2:0] funct3_mem;
  logic [XLEN-1:0] alu_result_mem;
  logic [XLEN-1:0] rs1_data_mem;
  logic [XLEN-1:0] rs2_data_mem;
  logic [XLEN-1:0] pc_plus4_mem;
  logic [XLEN-1:0] jb_tgt_mem;
  logic            is_branch_mem;
  logic            is_jalr_mem;
  logic            is_jmp_mem;
  logic            branch_taken_mem;
  logic            bpred_taken_mem;
  logic [XLEN-1:0] pred_tgt_mem;
  logic            trap_mem;
  logic [     1:0] trap_code_mem;
  logic            is_ebreak_mem;
  logic [XLEN-1:0] csr_rdata_mem;
  logic [XLEN-1:0] m_result_mem;
  logic [XLEN-1:0] mul_ll_mem;
  logic [XLEN-1:0] mul_lh_mem;
  logic [XLEN-1:0] mul_hl_mem;
  logic [XLEN-1:0] mul_hh_mem;

  // MEM -> WB
  logic            instr_valid_wb;

  // WB -> svc_rv
  logic            instr_valid_ret;
  logic            reg_write_wb;
  logic [     2:0] res_src_wb;
  logic [    31:0] instr_wb;
  logic [     4:0] rd_wb;
  logic [     2:0] funct3_wb;
  logic [XLEN-1:0] alu_result_wb;
  logic [XLEN-1:0] rs1_data_wb;
  logic [XLEN-1:0] rs2_data_wb;
  logic [XLEN-1:0] ld_data_wb;
  logic [XLEN-1:0] pc_plus4_wb;
  logic [XLEN-1:0] jb_tgt_wb;
  logic [XLEN-1:0] csr_rdata_wb;
  logic [XLEN-1:0] m_result_wb;
  logic [    63:0] product_64_wb;
  logic            trap_wb;
  logic [     1:0] trap_code_wb;
  logic            is_ebreak_wb;
`ifdef RISCV_FORMAL
  logic            f_mem_write_wb;
  logic [XLEN-1:0] f_dmem_waddr_wb;
  logic [XLEN-1:0] f_dmem_raddr_wb;
  logic [XLEN-1:0] f_dmem_wdata_wb;
  logic [     3:0] f_dmem_wstrb_wb;
  logic [XLEN-1:0] f_dmem_rdata_wb;
  logic [     3:0] f_dmem_rstrb_wb;
  logic            f_is_branch_wb;
  logic            f_is_jmp_wb;
  logic            f_branch_taken_wb;
`endif

  // WB retired instruction outputs
  logic [    31:0] instr_ret;
  logic [XLEN-1:0] pc_ret;
  logic [XLEN-1:0] rs1_data_ret;
  logic [XLEN-1:0] rs2_data_ret;
  logic [XLEN-1:0] rd_data_ret;
  logic            trap_ret;
  logic [     1:0] trap_code_ret;
  logic            reg_write_ret;
  logic            ebreak_ret;
`ifdef RISCV_FORMAL
  logic            f_mem_write_ret;
  logic [XLEN-1:0] f_dmem_waddr_ret;
  logic [XLEN-1:0] f_dmem_raddr_ret;
  logic [XLEN-1:0] f_dmem_wdata_ret;
  logic [     3:0] f_dmem_wstrb_ret;
  logic [XLEN-1:0] f_dmem_rdata_ret;
  logic [     3:0] f_dmem_rstrb_ret;
  logic            f_is_branch_ret;
  logic            f_is_jmp_ret;
  logic            f_branch_taken_ret;
  logic [XLEN-1:0] f_jb_tgt_ret;
  logic [XLEN-1:0] f_pc_plus4_ret;
`endif

  // WB -> ID (register write-back, combinational for same-cycle write)
  logic [XLEN-1:0] rd_data_wb;

  //
  // PC Control Signals
  //

  // EX -> IF (PC control)
  (* max_fanout = 32 *)logic [     1:0] pc_sel_ex;
  logic [XLEN-1:0] pc_redir_tgt_ex;
  logic            mispredicted_ex;

  // MEM -> IF (PC control)
  logic [XLEN-1:0] redir_tgt_mem;

  // ID -> IF (branch prediction)
  logic [     1:0] pc_sel_id;
  logic [XLEN-1:0] pred_tgt_id;
  logic            pred_taken_id;
  logic            is_jalr_id;

  // Arbitrated PC control to IF
  logic [     1:0] pc_sel;
  logic [XLEN-1:0] pc_redir_tgt;
  logic [XLEN-1:0] pred_tgt;

  // Registered redirect pending signal (from stage_pc)
  logic redir_pending_if;

  // MEM -> EX (forwarding)
  logic [XLEN-1:0] result_mem;
  logic [XLEN-1:0] ld_data_mem;

  // EX -> Hazard
  logic            is_csr_ex;
  logic            is_m_ex;
  logic            op_active_ex;

  // Hazard control signals
  // verilog_format: off
  (* max_fanout = 32 *)logic data_hazard_id_raw;
  (* max_fanout = 32 *)logic data_hazard_id;
  (* max_fanout = 32 *)logic if_id_flush;
  (* max_fanout = 32 *)logic id_ex_flush;
  (* max_fanout = 32 *)logic ex_mem_flush;
  // verilog_format: on

  //
  // BTB prediction signals
  //
  // *_pc: From pc_sel arbiter, input to stage_pc
  // *_if: From stage_pc (optionally registered), input to stage_if
  // *_id: From stage_if, output to ID stage
  // btb_pred_taken: IF-stage synchronous signal to hazard unit indicating
  //                 "this PC_SEL_PREDICTED came from BTB in this cycle"
  //                 (NOT ID-aligned - must be synchronous with PC mux)
  //
  logic            btb_hit_pc;
  logic            btb_pred_taken_pc;
  logic [XLEN-1:0] btb_tgt_pc;
  logic            btb_is_return_pc;
  logic            btb_hit_if;
  logic            btb_pred_taken_if;
  logic [XLEN-1:0] btb_tgt_if;
  logic            btb_is_return_if;
  logic            btb_hit_id;
  logic            btb_pred_taken_id;
  logic [XLEN-1:0] btb_tgt_id;
  logic            btb_is_return_id;
  logic            btb_pred_taken;
  logic            ras_pred_taken;

  //
  // RAS prediction signals
  //
  logic            ras_valid_pc;
  logic [XLEN-1:0] ras_tgt_pc;
  logic            ras_valid_if;
  logic [XLEN-1:0] ras_tgt_if;
  logic            ras_valid_id;
  logic [XLEN-1:0] ras_tgt_id;

  //
  // BTB signals
  //
  logic            btb_hit;
  logic [XLEN-1:0] btb_tgt;
  logic            btb_taken;
  logic            btb_is_return;
  logic            btb_update_en;
  logic [XLEN-1:0] btb_update_pc;
  logic [XLEN-1:0] btb_update_tgt;
  logic            btb_update_taken;
  logic            btb_update_is_ret;
  logic            btb_update_is_jal;

  //
  // RAS signals
  //
  logic            ras_valid;
  logic [XLEN-1:0] ras_tgt;
  logic            ras_push_en;
  logic [XLEN-1:0] ras_push_addr;
  logic            ras_pop_en;

  // Retired signal (for instruction counting)
  // An instruction retires when WB has valid output and is not stalled
  logic retired;
  assign retired = instr_valid_ret && !stall_wb;

  //
  // Global stall
  //
  logic stall_cpu;
  assign stall_cpu      = halt || dmem_stall;

  //
  // Front-end stall/bubble (data hazards + instruction fetch stalls)
  //
  assign data_hazard_id = data_hazard_id_raw || imem_stall;

  //
  // Per-stage stall signals
  //
  logic stall_pc;
  logic stall_if;
  logic stall_id;
  logic stall_ex;
  logic stall_mem;
  logic stall_wb;

  //
  // stall_pc: redirect overrides stall because on redirect,
  // data_hazard_id and op_active_ex are caused by younger instructions
  // that will be flushed anyway.
  //
  // Both MEM redirects (redir_valid_mem) and EX redirects (pc_sel ==
  // PC_SEL_REDIRECT) override stall. Without this, EX redirects during
  // dmem_stall would not take effect until the stall releases, but by then
  // the EX stage has advanced and the redirect target may be lost.
  //
  logic pc_redir;
  assign pc_redir = (pc_sel == PC_SEL_REDIRECT);
  assign stall_pc = ((stall_cpu || data_hazard_id || op_active_ex) &&
                     !redir_valid_mem && !pc_redir);

  //
  // stall_if: IF must respect imem_stall even when stall_pc is overridden
  // by redirects. Otherwise the fetch stage can "advance" while the I$ is
  // busy, corrupting the BRAM-style 1-cycle alignment assumptions.
  //
  assign stall_if = stall_pc || imem_stall;

  //
  // ID stall does NOT include data_hazard_id because:
  // - ID must advance to send bubble to EX during data hazards
  // - data_hazard_id only stalls PC/IF (don't fetch new instructions)
  //
  assign stall_id = stall_cpu || op_active_ex;
  assign stall_ex = stall_cpu;
  assign stall_mem = stall_cpu;
  assign stall_wb = stall_cpu;

  //
  // Halt signals
  //
  logic halt;
  logic halt_next;

  //
  // Hazard Detection Unit
  //
  // Full hazard unit for pipelined mode.
  // Minimal stall logic for single-cycle mode with M extension.
  //
  if (PIPELINED == 1) begin : g_hazard
    svc_rv_hazard #(
        .FWD_REGFILE(FWD_REGFILE),
        .FWD        (FWD),
        .MEM_TYPE   (MEM_TYPE),
        .PC_REG     (PC_REG)
    ) hazard (
        .data_hazard_id(data_hazard_id_raw),
        .*
    );

    `SVC_UNUSED(mispredicted_ex);
  end else if (EXT_M == 1) begin : g_minimal_hazard
    //
    // Minimal hazard logic for single-cycle mode with M extension
    //
    // No data hazards in single-cycle mode. Multi-cycle ops (division)
    // are handled by EX stage's s_ready (gated by op_active_ex).
    // Halt is handled by stall_cpu.
    //
    assign data_hazard_id_raw = 1'b0;
    assign if_id_flush        = 1'b0;
    assign id_ex_flush        = 1'b0;
    assign ex_mem_flush       = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({rs1_id, rs2_id, rs1_used_id, rs2_used_id, is_mc_id, is_ld_ex,
                mispredicted_ex, is_csr_ex, is_m_ex, btb_pred_taken, ras_pred_taken,
                op_active_ex, redir_pending_if});
    // verilog_format: on
  end else begin : g_no_hazard
    //
    // No hazards in single-cycle mode without multi-cycle operations
    //
    // Halt is handled by stall_cpu.
    //
    assign data_hazard_id_raw = 1'b0;
    assign if_id_flush        = 1'b0;
    assign id_ex_flush        = 1'b0;
    assign ex_mem_flush       = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({rs1_id, rs2_id, rs1_used_id, rs2_used_id, is_mc_id, is_ld_ex,
                mispredicted_ex, is_csr_ex, is_m_ex, op_active_ex, btb_pred_taken,
                redir_pending_if, ras_pred_taken});
    // verilog_format: on
  end

  //
  // Define is_ld_ex for hazard unit
  //
  logic is_ld_ex;

  assign is_ld_ex = (res_src_ex == RES_MEM);

  //
  // PC Selection Arbiter
  //
  // Combines PC selection from EX, ID, RAS, and BTB with priority:
  // EX (redirect) > RAS (IF JALR) > BTB (IF branch/JAL) > ID (static) > sequential
  //
  svc_rv_pc_sel #(
      .XLEN      (XLEN),
      .RAS_ENABLE(RAS_ENABLE),
      .BTB_ENABLE(BTB_ENABLE)
  ) pc_sel_arbiter (
      .*
  );

  // Branch Target Buffer
  //
  if (BTB_ENABLE == 1) begin : g_btb
    svc_rv_btb #(
        .XLEN    (XLEN),
        .NENTRIES(BTB_ENTRIES)
    ) btb (
        .clk            (clk),
        .rst_n          (rst_n),
        .lookup_pc      (pc),
        .hit            (btb_hit),
        .predicted_tgt  (btb_tgt),
        .predicted_taken(btb_taken),
        .is_return      (btb_is_return),
        .update_en      (btb_update_en),
        .update_pc      (btb_update_pc),
        .update_tgt     (btb_update_tgt),
        .update_taken   (btb_update_taken),
        .update_is_ret  (btb_update_is_ret),
        .update_is_jal  (btb_update_is_jal)
    );
  end else begin : g_no_btb
    assign btb_hit       = 1'b0;
    assign btb_tgt       = '0;
    assign btb_taken     = 1'b0;
    assign btb_is_return = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({pc, btb_hit, btb_tgt, btb_taken, btb_is_return,
                 btb_update_en, btb_update_pc, btb_update_tgt, btb_update_taken,
                 btb_update_is_ret, btb_update_is_jal});
    // verilog_format: on
  end

  //
  // Return Address Stack
  //
  if (RAS_ENABLE == 1) begin : g_ras
    svc_rv_ras #(
        .XLEN (XLEN),
        .DEPTH(RAS_DEPTH)
    ) ras (
        .clk      (clk),
        .rst_n    (rst_n),
        .ras_valid(ras_valid),
        .ras_tgt  (ras_tgt),
        .push_en  (ras_push_en),
        .push_addr(ras_push_addr),
        .pop_en   (ras_pop_en)
    );
  end else begin : g_no_ras
    assign ras_valid = 1'b0;
    assign ras_tgt   = '0;

    // verilog_format: off
    `SVC_UNUSED({ras_valid, ras_tgt, ras_push_en, ras_push_addr, ras_pop_en});
    // verilog_format: on
  end

  //----------------------------------------------------------------------------
  // Pipeline Stages
  //----------------------------------------------------------------------------

  //
  // PC Stage: Program Counter
  //
  svc_rv_stage_pc #(
      .XLEN    (XLEN),
      .MEM_TYPE(MEM_TYPE),
      .BPRED   (BPRED),
      .PC_REG  (PC_REG),
      .RESET_PC(RESET_PC)
  ) stage_pc (
      .clk              (clk),
      .rst_n            (rst_n),
      .pc_sel           (pc_sel),
      .pc_redir_tgt     (pc_redir_tgt),
      .pred_tgt         (pred_tgt),
      .btb_pred_taken   (btb_pred_taken),
      .btb_hit_pc       (btb_hit_pc),
      .btb_pred_taken_pc(btb_pred_taken_pc),
      .btb_tgt_pc       (btb_tgt_pc),
      .btb_is_return_pc (btb_is_return_pc),
      .ras_valid_pc     (ras_valid_pc),
      .ras_tgt_pc       (ras_tgt_pc),
      .instr_valid_if   (instr_valid_if),
      .stall_pc         (stall_pc),
      .imem_stall       (imem_stall),
      .pc               (pc),
      .pc_if            (pc_if),
      .pc_next_if       (pc_next_if),
      .btb_hit_if       (btb_hit_if),
      .btb_pred_taken_if(btb_pred_taken_if),
      .btb_tgt_if       (btb_tgt_if),
      .btb_is_return_if (btb_is_return_if),
      .ras_valid_if     (ras_valid_if),
      .ras_tgt_if       (ras_tgt_if),
      .redir_pending_if (redir_pending_if)
  );

  //
  // IF Stage: Instruction Fetch
  //
  svc_rv_stage_if #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED),
      .MEM_TYPE (MEM_TYPE),
      .BPRED    (BPRED)
  ) stage_if (
      .instr_valid_if(instr_valid_if),
      .stall_i       (stall_if),
      .pc_if         (pc_if),
      .pc_next_if    (pc_next_if),
      .*
  );

  //
  // ID Stage: Instruction Decode
  //
  svc_rv_stage_id #(
      .XLEN       (XLEN),
      .PIPELINED  (PIPELINED),
      .FWD_REGFILE(FWD_REGFILE),
      .MEM_TYPE   (MEM_TYPE),
      .BPRED      (BPRED),
      .BTB_ENABLE (BTB_ENABLE),
      .RAS_ENABLE (RAS_ENABLE),
      .EXT_ZMMUL  (EXT_ZMMUL),
      .EXT_M      (EXT_M)
  ) stage_id (
      .pred_tgt(pred_tgt_id),
      .*
  );

  //
  // EX Stage: Execute
  //
  svc_rv_stage_ex #(
      .XLEN      (XLEN),
      .PIPELINED (PIPELINED),
      .FWD       (FWD),
      .MEM_TYPE  (MEM_TYPE),
      .BPRED     (BPRED),
      .BTB_ENABLE(BTB_ENABLE),
      .EXT_ZMMUL (EXT_ZMMUL),
      .EXT_M     (EXT_M)
  ) stage_ex (
      .*
  );

  //
  // MEM Stage: Memory Access
  //
  svc_rv_stage_mem #(
      .XLEN      (XLEN),
      .PIPELINED (PIPELINED),
      .MEM_TYPE  (MEM_TYPE),
      .BPRED     (BPRED),
      .RAS_ENABLE(RAS_ENABLE)
  ) stage_mem (
      .*
  );

  // WB Stage: Write Back
  svc_rv_stage_wb #(.XLEN(XLEN)) stage_wb (.*);

  // Halt logic
  assign halt_next = (retired && (ebreak_ret || trap_ret)) || halt;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      halt   <= 1'b0;
      ebreak <= 1'b0;
      trap   <= 1'b0;
    end else begin
      halt   <= halt_next;
      ebreak <= (retired && ebreak_ret) || ebreak;
      trap   <= (retired && trap_ret) || trap;
    end
  end

`ifndef RISCV_FORMAL
  // verilog_format: off
  `SVC_UNUSED({IMEM_AW, DMEM_AW, rs2_mem, pred_taken_id, trap_code_wb,
               instr_ret, pc_ret, rs1_data_ret, rs2_data_ret, rd_data_ret,
               trap_ret, trap_code_ret, reg_write_ret});
  // verilog_format: on
`else
  `SVC_UNUSED({IMEM_AW, DMEM_AW, rs2_mem, pred_taken_id});
`endif

  `include "svc_rv_dbg.svh"

`ifdef RISCV_FORMAL
  //
  // RISCV-FORMAL Interface (RVFI)
  //
  // Computes architectural next-PC directly from instruction properties,
  // enabling immediate RVFI emission without lag buffer. This correctly
  // reports what the instruction SHOULD do, allowing formal to catch bugs
  // where the pipeline executes the wrong path.
  //

  // Current commit signals
  logic [XLEN-1:0] f_commit_pc;
  logic            f_commit_mem_valid;
  logic [     3:0] f_commit_mem_rmask;
  logic [     3:0] f_commit_mem_wmask;
  logic [XLEN-1:0] f_commit_mem_rdata;
  logic [XLEN-1:0] f_commit_mem_wdata;

  // Note: We decode instruction types here rather than using the pipeline's
  // rs1_used/rs2_used signals because those are for hazard detection only.
  //
  // For performance, we don't mind if CSR or other instructions stall/forward
  // unnecessarily, but RVFI must accurately report which registers are
  // architecturally read. Instructions that don't read a register must report
  // addr=0 and rdata=0 per the RVFI specification.
  logic [     6:0] f_opcode_ret;
  logic            f_csr_imm_mode_ret;
  logic            f_instr_valid_ret;
  logic            f_instr_reads_rs1_ret;
  logic            f_instr_reads_rs2_ret;
  logic            f_rs1_used_ret;
  logic            f_rs2_used_ret;

  assign f_opcode_ret       = instr_ret[6:0];
  assign f_csr_imm_mode_ret = instr_ret[14];

  assign f_instr_valid_ret  = (trap_code_ret != TRAP_INSTR_INVALID);

  // rs1/rs2 usage detection for RVFI
  always_comb begin
    // Illegal instructions: registers not used
    // Valid instructions: rs1 NOT used by LUI, AUIPC, JAL, CSR immediate
    //
    // See note above as to why we are doing this decoding here.
    case (f_opcode_ret)
      OP_LUI, OP_AUIPC, OP_JAL: f_instr_reads_rs1_ret = 1'b0;
      OP_SYSTEM:                f_instr_reads_rs1_ret = !f_csr_imm_mode_ret;
      default:                  f_instr_reads_rs1_ret = 1'b1;
    endcase

    case (f_opcode_ret)
      OP_RTYPE, OP_BRANCH, OP_STORE: f_instr_reads_rs2_ret = 1'b1;
      default:                       f_instr_reads_rs2_ret = 1'b0;
    endcase

    f_rs1_used_ret = f_instr_valid_ret && f_instr_reads_rs1_ret;
    f_rs2_used_ret = f_instr_valid_ret && f_instr_reads_rs2_ret;
  end

  assign f_commit_pc = pc_ret;

  always_comb begin
    f_commit_mem_valid = 1'b0;
    f_commit_mem_rmask = 4'b0000;
    f_commit_mem_wmask = 4'b0000;
    f_commit_mem_rdata = 32'h0;
    f_commit_mem_wdata = 32'h0;

    // Use _ret signals for memory since they're captured on WB entry
    // and remain stable until retirement

    // Loads (f_dmem_rstrb_ret is non-zero for loads)
    if (|f_dmem_rstrb_ret && !trap_ret) begin
      f_commit_mem_valid = 1'b1;
      f_commit_mem_rmask = f_dmem_rstrb_ret;
      f_commit_mem_rdata = f_dmem_rdata_ret;
    end

    // Stores
    if (f_mem_write_ret && !trap_ret) begin
      f_commit_mem_valid = 1'b1;
      f_commit_mem_wmask = f_dmem_wstrb_ret;
      f_commit_mem_wdata = f_dmem_wdata_ret;
    end
  end

  // ---------------------------------------------------------------------------
  // Architectural next-PC computation
  // ---------------------------------------------------------------------------
  //
  // Compute the architectural next-PC from the instruction's own properties,
  // not from what the pipeline actually did. This is the key fix that allows
  // formal verification to catch misprediction bugs.
  //
  // - Jumps (JAL/JALR): always go to jb_tgt
  // - Branches: go to jb_tgt if taken, pc+4 if not taken
  // - Traps: stay at current PC (trap handler will redirect)
  // - Other: pc+4
  //
  logic [XLEN-1:0] f_arch_next_pc;
  logic            f_halt;

  assign f_halt = ebreak_ret || trap_ret;

  always_comb begin
    if (f_halt) begin
      // On halt/trap, next PC is current PC per RVFI spec
      f_arch_next_pc = f_commit_pc;
    end else if (f_is_jmp_ret) begin
      // JAL/JALR always jump to target
      f_arch_next_pc = f_jb_tgt_ret;
    end else if (f_is_branch_ret) begin
      // Branch: target if taken, pc+4 if not taken
      f_arch_next_pc = f_branch_taken_ret ? f_jb_tgt_ret : f_pc_plus4_ret;
    end else begin
      // All other instructions: sequential
      f_arch_next_pc = f_pc_plus4_ret;
    end
  end

  // ---------------------------------------------------------------------------
  // Immediate RVFI emission (no lag buffer)
  // ---------------------------------------------------------------------------
  //
  // Emit RVFI data immediately when instruction retires. The architectural
  // next-PC is computed from the instruction itself, not observed from the
  // next instruction.
  //
  (* keep *) logic rvfi_retire;

  assign rvfi_retire = retired;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rvfi_valid <= 1'b0;
      rvfi_order <= 64'd0;
    end else begin
      rvfi_valid <= 1'b0;

      if (rvfi_retire) begin
        rvfi_valid <= 1'b1;
        rvfi_order <= rvfi_order + 64'd1;

        rvfi_insn <= instr_ret;
        rvfi_pc_rdata <= f_commit_pc;
        rvfi_pc_wdata <= f_arch_next_pc;

        //
        // Override rs1/rs2 addr/rdata to 0 when not architecturally read.
        // Per RVFI spec, instructions that don't read a register must report
        // addr=0 and rdata=0 (e.g., LUI, JAL, CSR immediate instructions).
        //
        rvfi_rs1_addr <= f_rs1_used_ret ? instr_ret[19:15] : 5'b0;
        rvfi_rs2_addr <= f_rs2_used_ret ? instr_ret[24:20] : 5'b0;
        rvfi_rs1_rdata <= f_rs1_used_ret ? rs1_data_ret : '0;
        rvfi_rs2_rdata <= f_rs2_used_ret ? rs2_data_ret : '0;

        //
        // Override rd_addr to 0 when not writing.
        //
        rvfi_rd_addr <= reg_write_ret ? instr_ret[11:7] : 5'b0;
        rvfi_rd_wdata <= (reg_write_ret && instr_ret[11:7] != 5'b0) ?
            rd_data_ret : '0;

        rvfi_trap <= trap_ret;
        rvfi_halt <= f_halt;
        rvfi_intr <= 1'b0;

        rvfi_mem_valid <= f_commit_mem_valid;
        rvfi_mem_instr <= 1'b0;
        rvfi_mem_addr <= f_mem_write_ret ? f_dmem_waddr_ret : f_dmem_raddr_ret;
        rvfi_mem_rmask <= f_commit_mem_rmask;
        rvfi_mem_wmask <= f_commit_mem_wmask;
        rvfi_mem_rdata <= f_commit_mem_rdata;
        rvfi_mem_wdata <= f_commit_mem_wdata;
      end
    end
  end

  //
  // Static mode/XLEN
  //
  assign rvfi_mode = 2'b11;
  assign rvfi_ixl  = 2'b01;
`endif

endmodule

`endif
