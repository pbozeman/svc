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
  // Controlled by +SVC_RV_DBG_IF and +SVC_RV_DBG_EX runtime plusargs
  //
`ifndef SYNTHESIS
  `include "svc_rv_dasm.svh"

  //
  // Debug alignment constants
  //
  localparam int DBG_ID_PRED_WIDTH = 13;
  localparam int DBG_EX_FLAGS_WIDTH = 5;
  localparam int DBG_WB_WIDTH = 15;
  localparam int DBG_MEM_WIDTH = 24;

  logic dbg_if;
  logic dbg_id;
  logic dbg_ex;
  logic dbg_mem;
  logic dbg_wb;

  initial begin
    integer dbg_if_level;
    integer dbg_id_level;
    integer dbg_ex_level;
    integer dbg_mem_level;
    integer dbg_wb_level;

    if ($value$plusargs("SVC_RV_DBG_IF=%d", dbg_if_level)) begin
      dbg_if = (dbg_if_level != 0);
    end else begin
      dbg_if = 1'b0;
    end

    if ($value$plusargs("SVC_RV_DBG_ID=%d", dbg_id_level)) begin
      dbg_id = (dbg_id_level != 0);
    end else begin
      dbg_id = 1'b0;
    end

    if ($value$plusargs("SVC_RV_DBG_EX=%d", dbg_ex_level)) begin
      dbg_ex = (dbg_ex_level != 0);
    end else begin
      dbg_ex = 1'b0;
    end

    if ($value$plusargs("SVC_RV_DBG_MEM=%d", dbg_mem_level)) begin
      dbg_mem = (dbg_mem_level != 0);
    end else begin
      dbg_mem = 1'b0;
    end

    if ($value$plusargs("SVC_RV_DBG_WB=%d", dbg_wb_level)) begin
      dbg_wb = (dbg_wb_level != 0);
    end else begin
      dbg_wb = 1'b0;
    end
  end

  //
  // Helper function to format IF stage debug output
  //
  function automatic string fmt_if_debug();
    string pc_sel_str;
    string stall_str;
    string flush_str;

    case (stage_if.pc_sel)
      PC_SEL_SEQUENTIAL: pc_sel_str = " seq";
      PC_SEL_PREDICTED:  pc_sel_str = "pred";
      PC_SEL_REDIRECT:   pc_sel_str = "rdir";
      default:           pc_sel_str = "????";
    endcase

    stall_str = stage_if.pc_stall ? "s" : " ";
    flush_str = stage_if.if_id_flush ? "f" : " ";

    return $sformatf(
        "IF %s%s %08x   %s   %08x %08x -> %08x",
        stall_str,
        flush_str,
        stage_if.pc,
        pc_sel_str,
        stage_if.pred_target,
        stage_if.pc_redirect_target,
        stage_if.pc_next
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
    // IF-only debug output (when ID and EX debug are disabled)
    //
    if (rst_n && dbg_if && !dbg_id && !dbg_ex) begin
      $display("[%12t] %s", $time, fmt_if_debug());
    end

    //
    // ID-only debug output (when EX debug is disabled)
    //
    if (rst_n && dbg_id && !dbg_ex) begin
      if (dbg_if) begin
        line = {fmt_if_debug(), " | ", fmt_id_debug()};
        $display("[%12t] %s", $time, line);
      end else begin
        $display("[%12t] %s", $time, fmt_id_debug());
      end
    end

    //
    // EX debug output (with optional IF and ID output when enabled)
    //
    if (rst_n && dbg_ex) begin
      //
      // Build combined line with all enabled stages
      //
      line = "";
      if (dbg_if) begin
        line = fmt_if_debug();
      end

      if (dbg_id) begin
        if (line != "") line = {line, " | "};
        line = {line, fmt_id_debug()};
      end

      //
      // Add EX stage output
      //
      if (line != "") line = {line, " | "};

      if (is_branch_ex) begin
        //
        // Branch ops: show comparison operands, prediction, and actual result
        //
        line = {
          line,
          $sformatf(
              "EX    %08x  %-30s   %08x %08x -> %08x %s %s ",
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
              "EX    %08x  %-30s   %08x %08x -> %08x%s",
              pc_ex,
              dasm_inst(
                instr_ex
              ),
              jb_target_src_ex ? stage_ex.fwd_rs1_ex : pc_ex,
              imm_ex,
              stage_ex.jb_target_ex,
              {DBG_EX_FLAGS_WIDTH{" "}}
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
              "EX    %08x  %-30s   %08x %08x -> %08x%s",
              pc_ex,
              dasm_inst(
                instr_ex
              ),
              stage_ex.fwd_rs1_ex,
              stage_ex.fwd_rs2_ex,
              stage_ex.m_result_ex,
              {DBG_EX_FLAGS_WIDTH{" "}}
          )
        };
      end else begin
        //
        // Non-M ops: show ALU operation
        //
        line = {
          line,
          $sformatf(
              "EX    %08x  %-30s   %08x %08x -> %08x%s",
              pc_ex,
              dasm_inst(
                instr_ex
              ),
              stage_ex.alu_a_ex,
              stage_ex.alu_b_ex,
              stage_ex.alu_result_ex,
              {DBG_EX_FLAGS_WIDTH{" "}}
          )
        };
      end

      //
      // Memory operations
      // SRAM: 0-cycle latency, display in EX stage when dmem_ren/dmem_we active
      // BRAM: 1-cycle latency, display in MEM stage when mem_read_mem/mem_write_mem active
      //
      if (dbg_mem) begin
        line = {line, " | "};
        if (MEM_TYPE == MEM_TYPE_SRAM) begin
          if (dmem_ren) begin
            line = {
              line, $sformatf("MR %08x -> %08x ", alu_result_mem, dmem_rdata)
            };
          end else if (dmem_we) begin
            line = {
              line, $sformatf("MW %08x -> %08x ", dmem_wdata, alu_result_mem)
            };
          end else begin
            line = {line, {DBG_MEM_WIDTH{" "}}};
          end
        end else begin
          if (mem_read_mem) begin
            line = {
              line, $sformatf("MR %08x -> %08x ", alu_result_mem, dmem_rdata)
            };
          end else if (mem_write_mem) begin
            line = {
              line, $sformatf("MW %08x -> %08x ", dmem_wdata, alu_result_mem)
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
        line = {line, " | "};
        if (reg_write_wb && (rd_wb != 5'h0)) begin
          line = {
            line, $sformatf("WB %08x -> x%02d", stage_wb.rd_data_wb, rd_wb)
          };
        end else begin
          line = {line, {DBG_WB_WIDTH{" "}}};
        end
      end

      $display("[%12t] %s", $time, line);
    end
  end
`endif

endmodule

`endif
