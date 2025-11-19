//
// RISC-V Pipeline Debug Monitor
//
// NOTE: This file is designed to be included only at the end of svc_rv.sv
// It relies on internal signals and hierarchy of that module.
// This is separated out just to keep the debug code out of the way.
//

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
  end else if (dbg_if || dbg_id || dbg_ex || dbg_mem || dbg_wb || dbg_haz) begin
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
              ex_mem_stall ? "s" : (ex_mem_flush ? "f" : " "),
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
              ex_mem_stall ? "s" : (ex_mem_flush ? "f" : " "),
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
              ex_mem_stall ? "s" : (ex_mem_flush ? "f" : " "),
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
                "M %s %08x r %08x ", stall_str, pc_plus4_mem - 4, dmem_raddr
            )
          };
        end else if (dmem_we) begin
          line = {
            line,
            $sformatf(
                "M %s %08x w %08x ", stall_str, pc_plus4_mem - 4, dmem_waddr
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
                "M %s %08x r %08x ", stall_str, pc_plus4_mem - 4, dmem_raddr
            )
          };
        end else if (mem_write_mem) begin
          line = {
            line,
            $sformatf(
                "M %s %08x w %08x ", stall_str, pc_plus4_mem - 4, dmem_waddr
            )
          };
        end else begin
          line = {line, {DBG_MEM_WIDTH{" "}}};
        end
      end
    end

    //
    // WB stage - always show PC, optionally show register writes (non-x0 only)
    // Always reserve space for consistent alignment
    //
    if (dbg_wb) begin
      string wb_str;
      if (line != "") line = {line, " | "};
      if (reg_write_wb && (rd_wb != 5'h0)) begin
        wb_str = $sformatf("WB %08x %08x -> x%02d", pc_plus4_wb - 4,
                           stage_wb.rd_data_wb, rd_wb);
      end else begin
        wb_str = $sformatf("WB %08x", pc_plus4_wb - 4);
        while (wb_str.len() < DBG_WB_WIDTH) begin
          wb_str = {wb_str, " "};
        end
      end
      line = {line, wb_str};
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
