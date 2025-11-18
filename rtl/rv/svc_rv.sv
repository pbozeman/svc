`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_unused.sv"

`include "svc_rv_btb.sv"
`include "svc_rv_ras.sv"
`include "svc_rv_bpred_if.sv"
`include "svc_rv_bpred_id.sv"
`include "svc_rv_bpred_ex.sv"
`include "svc_rv_pc_sel.sv"
`include "svc_rv_hazard.sv"
`include "svc_rv_stage_if_sram.sv"
`include "svc_rv_stage_if_bram.sv"
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
    parameter int BTB_ENABLE  = 0,
    parameter int BTB_ENTRIES = 16,
    parameter int RAS_ENABLE  = 0,
    parameter int RAS_DEPTH   = 8,
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
  end

  //
  // Inter-stage signals
  //

  // IF -> ID
  logic [    31:0] instr_id;
  logic [XLEN-1:0] pc_id;
  logic [XLEN-1:0] pc_plus4_id;

  // IF -> BTB
  logic [XLEN-1:0] pc;

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
  logic            is_jal_ex;
  logic            is_jalr_ex;
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
  logic [XLEN-1:0] pred_target_ex;

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
  logic [XLEN-1:0] rs1_data_mem;
  logic [XLEN-1:0] rs2_data_mem;
  logic [XLEN-1:0] pc_plus4_mem;
  logic [XLEN-1:0] jb_target_mem;
  logic            is_jalr_mem;
  logic [XLEN-1:0] csr_rdata_mem;
  logic [XLEN-1:0] m_result_mem;
  logic [XLEN-1:0] mul_ll_mem;
  logic [XLEN-1:0] mul_lh_mem;
  logic [XLEN-1:0] mul_hl_mem;
  logic [XLEN-1:0] mul_hh_mem;

  // MEM -> WB
  logic            reg_write_wb;
  logic [     2:0] res_src_wb;
  logic [    31:0] instr_wb;
  logic [     4:0] rd_wb;
  logic [     2:0] funct3_wb;
  logic [XLEN-1:0] alu_result_wb;
  logic [XLEN-1:0] rs1_data_wb;
  logic [XLEN-1:0] rs2_data_wb;
  logic [XLEN-1:0] dmem_rdata_ext_wb;
  logic [XLEN-1:0] pc_plus4_wb;
  logic [XLEN-1:0] jb_target_wb;
  logic [XLEN-1:0] csr_rdata_wb;
  logic [XLEN-1:0] m_result_wb;
  logic [    63:0] product_64_wb;

  // WB -> ID (register write-back)
  logic [XLEN-1:0] rd_data_wb;

  // EX -> IF (PC control)
  logic [     1:0] pc_sel_ex;
  logic [XLEN-1:0] pc_redirect_target;
  logic            mispredicted_ex;

  // ID -> IF (branch prediction)
  logic [     1:0] pc_sel_id;
  logic [XLEN-1:0] pred_target_id;
  logic [XLEN-1:0] pred_target;
  logic            pred_taken_id;
  logic            is_jalr_id;

  // Combined PC selection to IF
  logic [     1:0] pc_sel;

  // MEM -> EX (forwarding)
  logic [XLEN-1:0] result_mem;
  logic [XLEN-1:0] load_data_mem;

  // EX -> Hazard
  logic            is_csr_ex;
  logic            is_m_ex;
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
  // BTB prediction signals
  //
  // btb_hit_if: BTB hit input to IF stage (from BTB lookup)
  // btb_pred_taken_if: BTB prediction input to IF stage (from BTB lookup)
  // btb_target_if: BTB target input to IF stage (from BTB lookup)
  // btb_is_return_if: BTB is_return input to IF stage (from BTB lookup)
  // btb_hit_id: BTB hit output from IF/ID register
  // btb_pred_taken_id: BTB prediction output from IF/ID register
  // btb_target_id: BTB target output from IF/ID register
  // btb_is_return_id: BTB is_return output from IF/ID register
  // btb_pred_taken: IF-stage synchronous signal to hazard unit indicating
  //                 "this PC_SEL_PREDICTED came from BTB in this cycle"
  //                 (NOT ID-aligned - must be synchronous with PC mux)
  //
  logic            btb_hit_if;
  logic            btb_pred_taken_if;
  logic [XLEN-1:0] btb_target_if;
  logic            btb_is_return_if;
  logic            btb_hit_id;
  logic            btb_pred_taken_id;
  logic [XLEN-1:0] btb_target_id;
  logic            btb_is_return_id;
  logic            btb_pred_taken;
  logic            ras_pred_taken;

  //
  // RAS prediction signals
  //
  logic            ras_valid_if;
  logic [XLEN-1:0] ras_target_if;
  logic            ras_valid_id;
  logic [XLEN-1:0] ras_target_id;

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
  // BTB signals
  //
  logic            btb_hit;
  logic [XLEN-1:0] btb_target;
  logic            btb_taken;
  logic            btb_is_return;
  logic            btb_update_en;
  logic [XLEN-1:0] btb_update_pc;
  logic [XLEN-1:0] btb_update_target;
  logic            btb_update_taken;
  logic            btb_update_is_return;

  //
  // RAS signals
  //
  logic            ras_valid;
  logic [XLEN-1:0] ras_target;
  logic            ras_push_en;
  logic [XLEN-1:0] ras_push_addr;
  logic            ras_pop_en;

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
        .MEM_TYPE   (MEM_TYPE)
    ) hazard (
        .*
    );
  end else if (EXT_M == 1) begin : g_minimal_hazard
    //
    // Minimal hazard logic for single-cycle mode with M extension
    //
    // Multi-cycle division operations (32 cycles) require stalling the PC
    // to keep the instruction visible in the combinational pipeline while
    // the divider runs. The multi-cycle state machine in EX stage handles
    // op_active_ex generation.
    //
    // No data hazards exist in single-cycle mode (no pipeline registers),
    // so only PC and IF/ID stalls are needed.
    //
    assign pc_stall     = op_active_ex;
    assign if_id_stall  = op_active_ex;
    assign if_id_flush  = 1'b0;
    assign id_ex_stall  = 1'b0;
    assign id_ex_flush  = 1'b0;
    assign ex_mem_stall = 1'b0;
    assign mem_wb_stall = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({rs1_id, rs2_id, rs1_used_id, rs2_used_id, is_load_ex,
                mispredicted_ex, is_csr_ex, is_m_ex, btb_pred_taken, ras_pred_taken});
    // verilog_format: on
  end else begin : g_no_hazard
    //
    // No hazards in single-cycle mode without multi-cycle operations
    //
    assign pc_stall     = 1'b0;
    assign if_id_stall  = 1'b0;
    assign if_id_flush  = 1'b0;
    assign id_ex_stall  = 1'b0;
    assign id_ex_flush  = 1'b0;
    assign ex_mem_stall = 1'b0;
    assign mem_wb_stall = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({rs1_id, rs2_id, rs1_used_id, rs2_used_id, is_load_ex,
                mispredicted_ex, is_csr_ex, is_m_ex, op_active_ex, btb_pred_taken,
                ras_pred_taken});
    // verilog_format: on
  end

  //
  // Define is_load_ex for hazard unit
  //
  logic is_load_ex;

  assign is_load_ex = (res_src_ex == RES_MEM);

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
        .clk             (clk),
        .rst_n           (rst_n),
        .lookup_pc       (pc),
        .hit             (btb_hit),
        .predicted_target(btb_target),
        .predicted_taken (btb_taken),
        .is_return       (btb_is_return),
        .update_en       (btb_update_en),
        .update_pc       (btb_update_pc),
        .update_target   (btb_update_target),
        .update_taken    (btb_update_taken),
        .update_is_return(btb_update_is_return)
    );
  end else begin : g_no_btb
    assign btb_hit       = 1'b0;
    assign btb_target    = '0;
    assign btb_taken     = 1'b0;
    assign btb_is_return = 1'b0;

    // verilog_format: off
    `SVC_UNUSED({pc, btb_hit, btb_target, btb_taken, btb_is_return,
                 btb_update_en, btb_update_pc, btb_update_target, btb_update_taken,
                 btb_update_is_return});
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
        .clk       (clk),
        .rst_n     (rst_n),
        .ras_valid (ras_valid),
        .ras_target(ras_target),
        .push_en   (ras_push_en),
        .push_addr (ras_push_addr),
        .pop_en    (ras_pop_en)
    );
  end else begin : g_no_ras
    assign ras_valid  = 1'b0;
    assign ras_target = '0;

    // verilog_format: off
    `SVC_UNUSED({ras_valid, ras_target, ras_push_en, ras_push_addr, ras_pop_en});
    // verilog_format: on
  end

  //----------------------------------------------------------------------------
  // Pipeline Stages
  //----------------------------------------------------------------------------

  //
  // IF Stage: Instruction Fetch
  //
  svc_rv_stage_if #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED),
      .MEM_TYPE (MEM_TYPE),
      .BPRED    (BPRED)
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
      .BTB_ENABLE (BTB_ENABLE),
      .RAS_ENABLE (RAS_ENABLE),
      .EXT_ZMMUL  (EXT_ZMMUL),
      .EXT_M      (EXT_M)
  ) stage_id (
      .pred_target(pred_target_id),
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
      .RAS_ENABLE(RAS_ENABLE),
      .EXT_ZMMUL (EXT_ZMMUL),
      .EXT_M     (EXT_M)
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

  `SVC_UNUSED({IMEM_AW, DMEM_AW, rs2_mem, pred_taken_id});

  //
  // Optional pipeline execution monitor for debug
  // Controlled by +SVC_RV_DBG_IF and +SVC_RV_DBG_EX runtime plusargs
  //
  // Linter gets too confused about reaching into the hierarchy while
  // linting, so just disable it.
  //
`ifndef SYNTHESIS
`ifndef VERILATOR
  `include "svc_rv_dasm.svh"

  //
  // Debug alignment constants
  //
  localparam int DBG_ID_PRED_WIDTH = 13;
  localparam int DBG_EX_FLAGS_WIDTH = 5;
  localparam int DBG_WB_WIDTH = 27;
  localparam int DBG_MEM_WIDTH = 24;

  logic dbg_if;
  logic dbg_id;
  logic dbg_ex;
  logic dbg_mem;
  logic dbg_wb;
  logic dbg_haz;
  logic dbg_first_line;

  initial begin
    integer dbg_if_level;
    integer dbg_id_level;
    integer dbg_ex_level;
    integer dbg_mem_level;
    integer dbg_wb_level;
    integer dbg_haz_level;
    integer dbg_cpu_level;

    //
    // Master debug flag - enables all CPU debug output
    //
    if ($value$plusargs("SVC_RV_DBG_CPU=%d", dbg_cpu_level)) begin
      if (dbg_cpu_level != 0) begin
        dbg_if  = 1'b1;
        dbg_id  = 1'b1;
        dbg_ex  = 1'b1;
        dbg_mem = 1'b1;
        dbg_wb  = 1'b1;
        dbg_haz = 1'b1;
      end else begin
        dbg_if  = 1'b0;
        dbg_id  = 1'b0;
        dbg_ex  = 1'b0;
        dbg_mem = 1'b0;
        dbg_wb  = 1'b0;
        dbg_haz = 1'b0;
      end
    end else begin
      dbg_if  = 1'b0;
      dbg_id  = 1'b0;
      dbg_ex  = 1'b0;
      dbg_mem = 1'b0;
      dbg_wb  = 1'b0;
      dbg_haz = 1'b0;
    end

    //
    // Individual debug flags (override master setting)
    //
    if ($value$plusargs("SVC_RV_DBG_IF=%d", dbg_if_level)) begin
      dbg_if = (dbg_if_level != 0);
    end

    if ($value$plusargs("SVC_RV_DBG_ID=%d", dbg_id_level)) begin
      dbg_id = (dbg_id_level != 0);
    end

    if ($value$plusargs("SVC_RV_DBG_EX=%d", dbg_ex_level)) begin
      dbg_ex = (dbg_ex_level != 0);
    end

    if ($value$plusargs("SVC_RV_DBG_MEM=%d", dbg_mem_level)) begin
      dbg_mem = (dbg_mem_level != 0);
    end

    if ($value$plusargs("SVC_RV_DBG_WB=%d", dbg_wb_level)) begin
      dbg_wb = (dbg_wb_level != 0);
    end

    if ($value$plusargs("SVC_RV_DBG_HAZ=%d", dbg_haz_level)) begin
      dbg_haz = (dbg_haz_level != 0);
    end

  end

  //
  // Track first debug line after reset
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      dbg_first_line <= 1'b1;
    end else
        if (dbg_if || dbg_id || dbg_ex || dbg_mem || dbg_wb || dbg_haz) begin
      dbg_first_line <= 1'b0;
    end
  end

  //
  // Helper function to format IF stage debug output
  //
  function automatic string fmt_if_debug();
    string pc_sel_str;
    string stall_str;
    string flush_str;
    string btb_str;

    case (stage_if.pc_sel)
      PC_SEL_SEQUENTIAL: pc_sel_str = " seq";
      PC_SEL_PREDICTED:  pc_sel_str = "pred";
      PC_SEL_REDIRECT:   pc_sel_str = "rdir";
      default:           pc_sel_str = "????";
    endcase

    stall_str = if_id_stall ? "s" : " ";
    flush_str = if_id_flush ? "f" : " ";

    if (BTB_ENABLE != 0) begin
      string hit_str;
      string status_str;

      //
      // First char: H=hit, -=miss
      //
      if (btb_hit === 1'b1) hit_str = "H";
      else if (btb_hit === 1'b0) hit_str = "-";
      else hit_str = "X";

      //
      // Second char: -=miss, R=return, T=taken, N=not-taken
      //
      if (btb_hit === 1'b0) begin
        status_str = "-";
      end else if (btb_is_return === 1'b1) begin
        status_str = "R";
      end else if (btb_taken === 1'b1) begin
        status_str = "T";
      end else begin
        status_str = "N";
      end

      btb_str = $sformatf(" BTB[%s%s:%08x]", hit_str, status_str, btb_target);
    end else begin
      btb_str = "";
    end

    return $sformatf(
        "IF %s%s %08x %s %08x%s",
        stall_str,
        flush_str,
        stage_if.pc,
        pc_sel_str,
        stage_if.pc_next,
        btb_str
    );
  endfunction

  //
  // Helper function to format ID stage debug output
  //
  function automatic string fmt_id_debug();
    string stall_str;
    string flush_str;
    string pred_str;

    stall_str = id_ex_stall ? "s" : " ";
    flush_str = id_ex_flush ? "f" : " ";

    if (BPRED != 0) begin
      if ((stage_id.is_branch_id || stage_id.is_jump_id) &&
          (pc_sel_id == PC_SEL_PREDICTED)) begin
        pred_str = $sformatf("-> %08x T", pred_target);
      end else if (stage_id.is_branch_id || stage_id.is_jump_id) begin
        pred_str = $sformatf("-> %08x N", pc_id + 4);
      end else begin
        pred_str = {DBG_ID_PRED_WIDTH{" "}};
      end
    end else begin
      pred_str = {DBG_ID_PRED_WIDTH{" "}};
    end

    return $sformatf(
        "ID %s%s %08x  %-30s %s",
        stall_str,
        flush_str,
        pc_id,
        dasm_inst(
            instr_id
        ),
        pred_str
    );
  endfunction

  always @(posedge clk) begin
    string line;

    //
    // Combined debug output
    // Display any enabled stages in pipeline order: IF | ID | EX | MEM | WB | HAZ
    //
    if (rst_n &&
        (dbg_if || dbg_id || dbg_ex || dbg_mem || dbg_wb || dbg_haz)) begin
      //
      // Print newline before first debug line after reset
      //
      if (dbg_first_line) begin
        $display("");
      end

      //
      // Build combined line with all enabled stages
      //
      line = "";

      //
      // IF stage
      //
      if (dbg_if) begin
        line = fmt_if_debug();
      end

      //
      // ID stage
      //
      if (dbg_id) begin
        if (line != "") line = {line, " | "};
        line = {line, fmt_id_debug()};
      end

      //
      // EX stage
      //
      if (dbg_ex) begin
        if (line != "") line = {line, " | "};

        if (is_branch_ex) begin
          //
          // Branch ops: show comparison operands, prediction, and actual result
          //
          line = {
            line,
            $sformatf(
                "EX %s  %08x  %-30s   %08x %08x -> %08x %s %s ",
                ex_mem_stall ? "s" : " ",
                pc_ex,
                dasm_inst(
                  instr_ex
                ),
                stage_ex.fwd_rs1_ex,
                stage_ex.fwd_rs2_ex,
                stage_ex.jb_target_ex,
                bpred_taken_ex ? "T" : "N",
                stage_ex.branch_taken_ex ? "T" : "N"
            )
          };
        end else if (is_jump_ex) begin
          //
          // Jump ops: show base address (for JALR) and target
          //
          line = {
            line,
            $sformatf(
                "EX %s  %08x  %-30s   %08x %08x -> %08x     ",
                ex_mem_stall ? "s" : " ",
                pc_ex,
                dasm_inst(
                  instr_ex
                ),
                jb_target_src_ex ? stage_ex.fwd_rs1_ex : pc_ex,
                imm_ex,
                stage_ex.jb_target_ex
            )
          };
        end else if (res_src_ex == RES_M) begin
          //
          // M extension ops: show operands and result
          // Note: fwd_rs1_ex/fwd_rs2_ex are stable during multi-cycle ops
          //
          line = {
            line,
            $sformatf(
                "EX %s  %08x  %-30s   %08x %08x -> %08x     ",
                ex_mem_stall ? "s" : " ",
                pc_ex,
                dasm_inst(
                  instr_ex
                ),
                stage_ex.fwd_rs1_ex,
                stage_ex.fwd_rs2_ex,
                stage_ex.m_result_ex
            )
          };
        end else if (mem_write_ex) begin
          //
          // Store ops: show data to write and target address
          //
          line = {
            line,
            $sformatf(
                "EX %s  %08x  %-30s   %08x %08x -> %08x     ",
                ex_mem_stall ? "s" : " ",
                pc_ex,
                dasm_inst(
                  instr_ex
                ),
                stage_ex.fwd_rs2_ex,
                stage_ex.alu_a_ex,
                stage_ex.alu_result_ex
            )
          };
        end else if (mem_read_ex) begin
          //
          // Load ops: show address calculation
          //
          line = {
            line,
            $sformatf(
                "EX %s  %08x  %-30s   %08x %08x -> %08x     ",
                ex_mem_stall ? "s" : " ",
                pc_ex,
                dasm_inst(
                  instr_ex
                ),
                stage_ex.alu_a_ex,
                stage_ex.alu_b_ex,
                stage_ex.alu_result_ex
            )
          };
        end else begin
          //
          // Other ops: show ALU operation
          //
          line = {
            line,
            $sformatf(
                "EX %s  %08x  %-30s   %08x %08x -> %08x     ",
                ex_mem_stall ? "s" : " ",
                pc_ex,
                dasm_inst(
                  instr_ex
                ),
                stage_ex.alu_a_ex,
                stage_ex.alu_b_ex,
                stage_ex.alu_result_ex
            )
          };
        end
      end

      //
      // Memory operations
      // SRAM: 0-cycle latency, display in EX stage when dmem_ren/dmem_we active
      // BRAM: 1-cycle latency, display in MEM stage when mem_read_mem/mem_write_mem active
      //
      if (dbg_mem) begin
        string stall_str;

        stall_str = mem_wb_stall ? "s" : " ";

        if (line != "") line = {line, " | "};
        if (MEM_TYPE == MEM_TYPE_SRAM) begin
          if (dmem_ren) begin
            line = {
              line,
              $sformatf(
                  "M %s %08x r %08x ",
                  stall_str,
                  pc_plus4_mem - 4,
                  alu_result_mem
              )
            };
          end else if (dmem_we) begin
            line = {
              line,
              $sformatf(
                  "M %s %08x w %08x ",
                  stall_str,
                  pc_plus4_mem - 4,
                  alu_result_mem
              )
            };
          end else begin
            line = {line, {DBG_MEM_WIDTH{" "}}};
          end
        end else begin
          if (mem_read_mem) begin
            line = {
              line,
              $sformatf(
                  "M %s %08x r %08x ",
                  stall_str,
                  pc_plus4_mem - 4,
                  alu_result_mem
              )
            };
          end else if (mem_write_mem) begin
            line = {
              line,
              $sformatf(
                  "M %s %08x w %08x ",
                  stall_str,
                  pc_plus4_mem - 4,
                  alu_result_mem
              )
            };
          end else begin
            line = {line, {DBG_MEM_WIDTH{" "}}};
          end
        end
      end

      //
      // WB stage - show register writes (non-x0 only)
      // Always reserve space for consistent alignment
      //
      if (dbg_wb) begin
        if (line != "") line = {line, " | "};
        if (reg_write_wb && (rd_wb != 5'h0)) begin
          line = {
            line,
            $sformatf(
                "WB %08x %08x -> x%02d",
                pc_plus4_wb - 4,
                stage_wb.rd_data_wb,
                rd_wb
            )
          };
        end else begin
          line = {line, {DBG_WB_WIDTH{" "}}};
        end
      end


      //
      // Hazard information
      //
      if (PIPELINED == 1) begin
        if (dbg_haz) begin
          string rs1_str;
          string rs2_str;
          string ctrl_str;

          if (line != "") line = {line, " | "};

          // Format rs1 hazard
          //
          if (g_hazard.hazard.ex_hazard_rs1) begin
            rs1_str = $sformatf("E:x%02d  ", rd_ex);
          end else if (g_hazard.hazard.mem_hazard_rs1) begin
            rs1_str = $sformatf("M:x%02d  ", rd_mem);
          end else if (g_hazard.hazard.wb_hazard_rs1) begin
            rs1_str = $sformatf("W:x%02d  ", rd_wb);
          end else begin
            rs1_str = "       ";
          end

          //
          // Format rs2 hazard
          //
          if (g_hazard.hazard.ex_hazard_rs2) begin
            rs2_str = $sformatf("E:x%02d  ", rd_ex);
          end else if (g_hazard.hazard.mem_hazard_rs2) begin
            rs2_str = $sformatf("M:x%02d  ", rd_mem);
          end else if (g_hazard.hazard.wb_hazard_rs2) begin
            rs2_str = $sformatf("W:x%02d  ", rd_wb);
          end else begin
            rs2_str = "       ";
          end

          if (BPRED != 0) begin : g_bpred_dbg_haz
            //
            // Format control/multi-cycle
            //
            if (op_active_ex) begin
              ctrl_str = "MC";
            end else if (pc_sel == PC_SEL_REDIRECT) begin
              ctrl_str = "BR";
            end else if ((pc_sel == PC_SEL_PREDICTED) && !btb_pred_taken &&
                         !g_hazard.hazard.data_hazard && !op_active_ex) begin
              ctrl_str = "PR";
            end else begin
              ctrl_str = "  ";
            end
          end

          line = {line, $sformatf("H %s %s %s", rs1_str, rs2_str, ctrl_str)};
        end
      end

      $display("[%12t] %s", $time, line);
    end
  end
`endif
`endif

endmodule

`endif
