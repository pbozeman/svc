`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_unused.sv"

`include "svc_rv_hazard.sv"
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
    parameter int XLEN        = 32,
    parameter int IMEM_AW     = 10,
    parameter int DMEM_AW     = 10,
    parameter int PIPELINED   = 0,
    parameter int FWD_REGFILE = PIPELINED,
    parameter int FWD         = 0,
    parameter int MEM_TYPE    = 0,
    parameter int BPRED       = 0,
    parameter int EXT_ZMMUL   = 0,
    parameter int EXT_M       = 0
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

    output logic ebreak
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
    if ((EXT_ZMMUL == 1) && (EXT_M == 1)) begin
      $fatal(1, "EXT_ZMMUL and EXT_M are mutually exclusive");
    end
  end

  //
  // Inter-stage signals
  //

  // IF -> ID
  logic [    31:0] instr_id;
  logic [XLEN-1:0] pc_id;
  logic [XLEN-1:0] pc_plus4_id;

  // ID -> EX
  logic            reg_write_ex;
  logic            mem_read_ex;
  logic            mem_write_ex;
  logic [     1:0] alu_a_src_ex;
  logic            alu_b_src_ex;
  logic [     1:0] alu_instr_ex;
  logic [     2:0] res_src_ex;
  logic            is_branch_ex;
  logic            is_jump_ex;
  logic            jb_target_src_ex;
  logic            is_mc_ex;
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

  // ID -> Hazard
  logic [     4:0] rs1_id;
  logic [     4:0] rs2_id;
  logic            rs1_used_id;
  logic            rs2_used_id;

  // EX -> MEM
  logic            reg_write_mem;
  logic            mem_read_mem;
  logic            mem_write_mem;
  logic [     2:0] res_src_mem;
  logic [    31:0] instr_mem;
  logic [     4:0] rd_mem;
  logic [     4:0] rs2_mem;
  logic [     2:0] funct3_mem;
  logic [XLEN-1:0] alu_result_mem;
  logic [XLEN-1:0] rs2_data_mem;
  logic [XLEN-1:0] pc_plus4_mem;
  logic [XLEN-1:0] jb_target_mem;
  logic [XLEN-1:0] csr_rdata_mem;
  logic [XLEN-1:0] m_result_mem;

  // MEM -> WB
  logic            reg_write_wb;
  logic [     2:0] res_src_wb;
  logic [    31:0] instr_wb;
  logic [     4:0] rd_wb;
  logic [XLEN-1:0] alu_result_wb;
  logic [XLEN-1:0] dmem_rdata_ext_wb;
  logic [XLEN-1:0] pc_plus4_wb;
  logic [XLEN-1:0] jb_target_wb;
  logic [XLEN-1:0] csr_rdata_wb;
  logic [XLEN-1:0] m_result_wb;

  // WB -> ID (register write-back)
  logic [XLEN-1:0] rd_data_wb;

  // EX -> IF (PC control)
  logic [     1:0] pc_sel_ex;
  logic [XLEN-1:0] pc_redirect_target;
  logic            mispredicted_ex;

  // ID -> IF (branch prediction)
  logic [     1:0] pc_sel_id;
  logic [XLEN-1:0] pred_target;

  // Combined PC selection to IF
  logic [     1:0] pc_sel;

  // MEM -> EX (forwarding)
  logic [XLEN-1:0] result_mem;
  logic [XLEN-1:0] load_data_mem;

  // EX -> Hazard
  logic            is_csr_ex;
  logic            op_active_ex;

  // Hazard control signals
  logic            pc_stall;
  logic            if_id_stall;
  logic            if_id_flush;
  logic            id_ex_stall;
  logic            id_ex_flush;
  logic            ex_mem_stall;
  logic            mem_wb_stall;

  //
  // Instruction retirement tracking
  //
  // An instruction retires when it reaches WB and is not a bubble.
  // Bubbles are injected as 0 on reset. Flushed instructions become NOPs
  // which also should not count as retired.
  //
  logic            instr_retired;

  assign instr_retired = (instr_wb != 32'h0) && (instr_wb != I_NOP);

  //
  // Hazard Detection Unit
  //
  // Only instantiate when pipeline registers are enabled.
  // In a single-cycle design, there are no pipeline hazards.
  //
  if (PIPELINED == 1) begin : g_hazard
    svc_rv_hazard #(
        .FWD_REGFILE(FWD_REGFILE),
        .FWD        (FWD),
        .MEM_TYPE   (MEM_TYPE)
    ) hazard (
        .*
    );
  end else begin : g_no_hazard
    assign pc_stall     = 1'b0;
    assign if_id_stall  = 1'b0;
    assign if_id_flush  = 1'b0;
    assign id_ex_stall  = 1'b0;
    assign id_ex_flush  = 1'b0;
    assign ex_mem_stall = 1'b0;
    assign mem_wb_stall = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({rs1_id, rs2_id, rs1_used_id, rs2_used_id, is_load_ex,
                mispredicted_ex, is_csr_ex, op_active_ex});
    // verilog_format: on
  end

  //
  // Define is_load_ex for hazard unit
  //
  logic is_load_ex;

  assign is_load_ex = (res_src_ex == RES_MEM);

  //
  // Combine PC selection signals from EX and ID stages
  //
  // Priority: EX (redirect) > ID (prediction) > sequential
  // EX stage overrides ID prediction on actual branch resolution
  //
  assign pc_sel     = (pc_sel_ex == PC_SEL_REDIRECT) ? pc_sel_ex : pc_sel_id;

  //----------------------------------------------------------------------------
  // Pipeline Stages
  //----------------------------------------------------------------------------

  //
  // IF Stage: Instruction Fetch
  //
  svc_rv_stage_if #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED),
      .MEM_TYPE (MEM_TYPE)
  ) stage_if (
      .*
  );

  //
  // ID Stage: Instruction Decode
  //
  svc_rv_stage_id #(
      .XLEN       (XLEN),
      .PIPELINED  (PIPELINED),
      .FWD_REGFILE(FWD_REGFILE),
      .BPRED      (BPRED),
      .EXT_ZMMUL  (EXT_ZMMUL),
      .EXT_M      (EXT_M)
  ) stage_id (
      .*
  );

  //
  // EX Stage: Execute
  //
  svc_rv_stage_ex #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED),
      .FWD      (FWD),
      .MEM_TYPE (MEM_TYPE),
      .BPRED    (BPRED),
      .EXT_ZMMUL(EXT_ZMMUL),
      .EXT_M    (EXT_M)
  ) stage_ex (
      .*
  );

  //
  // MEM Stage: Memory Access
  //
  svc_rv_stage_mem #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED),
      .MEM_TYPE (MEM_TYPE)
  ) stage_mem (
      .*
  );

  //
  // WB Stage: Write Back
  //
  svc_rv_stage_wb #(.XLEN(XLEN)) stage_wb (.*);

  `SVC_UNUSED({IMEM_AW, DMEM_AW, rs2_mem});

  //
  // Optional pipeline execution monitor for debug
  // Controlled by +SVC_CPU_DBG runtime plusarg
  //
`ifndef SYNTHESIS
  `include "svc_rv_dasm.svh"

  logic cpu_dbg_enabled;

  initial begin
    integer cpu_dbg_level;

    if ($value$plusargs("SVC_CPU_DBG=%d", cpu_dbg_level)) begin
      cpu_dbg_enabled = (cpu_dbg_level != 0);
    end else begin
      cpu_dbg_enabled = 1'b0;
    end
  end

  always @(posedge clk) begin
    if (rst_n && cpu_dbg_enabled) begin
      if (is_branch_ex) begin
        //
        // Branch ops: show comparison operands, prediction, and actual result
        //
        $display("[%12t] %-4s %08x  %-28s  %08x %08x -> %08x %s %s", $time, "",
                 pc_ex, dasm_inst(instr_ex), stage_ex.fwd_rs1_ex,
                 stage_ex.fwd_rs2_ex, stage_ex.jb_target_ex,
                 bpred_taken_ex ? "T" : "N",
                 stage_ex.branch_taken_ex ? "T" : "N");
      end else if (is_jump_ex) begin
        //
        // Jump ops: show base address (for JALR) and target
        //
        $display("[%12t] %-4s %08x  %-28s  %08x %08x -> %08x", $time, "",
                 pc_ex, dasm_inst(instr_ex),
                 jb_target_src_ex ? stage_ex.fwd_rs1_ex : pc_ex, imm_ex,
                 stage_ex.jb_target_ex);
      end else if (res_src_ex == RES_M) begin
        //
        // M extension ops: show operands and result
        // Note: fwd_rs1_ex/fwd_rs2_ex are stable during multi-cycle ops
        //
        $display("[%12t] %-4s %08x  %-28s  %08x %08x -> %08x", $time, "",
                 pc_ex, dasm_inst(instr_ex), stage_ex.fwd_rs1_ex,
                 stage_ex.fwd_rs2_ex, stage_ex.m_result_ex);
      end else begin
        //
        // Non-M ops: show ALU operation
        //
        $display("[%12t] %-4s %08x  %-28s  %08x %08x -> %08x", $time, "",
                 pc_ex, dasm_inst(instr_ex), stage_ex.alu_a_ex,
                 stage_ex.alu_b_ex, stage_ex.alu_result_ex);
      end

      //
      // Memory operations
      // SRAM: 0-cycle latency, display in EX stage when dmem_ren/dmem_we active
      // BRAM: 1-cycle latency, display in MEM stage when mem_read_mem/mem_write_mem active
      //
      if (MEM_TYPE == MEM_TYPE_SRAM) begin
        if (dmem_ren) begin
          $display("[%12t] %-4s %08x  %-28s  %08x %8s -> %08x", $time, "MR:",
                   pc_plus4_mem - 4, "", alu_result_mem, "", dmem_rdata);
        end else if (dmem_we) begin
          $display("[%12t] %-4s %08x  %-28s  %08x %8s -> %08x", $time, "MW:",
                   pc_plus4_mem - 4, "", alu_result_mem, "", dmem_wdata);
        end
      end else begin
        if (mem_read_mem) begin
          $display("[%12t] %-4s %08x  %-28s  %08x %8s -> %08x", $time, "MR:",
                   pc_plus4_mem - 4, "", alu_result_mem, "", dmem_rdata);
        end else if (mem_write_mem) begin
          $display("[%12t] %-4s %08x  %-28s  %08x %8s -> %08x", $time, "MW:",
                   pc_plus4_mem - 4, "", alu_result_mem, "", dmem_wdata);
        end
      end
    end
  end
`endif

endmodule

`endif
