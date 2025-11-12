`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_unused.sv"

`include "svc_rv_alu.sv"
`include "svc_rv_alu_dec.sv"
`include "svc_rv_bcmp.sv"
`include "svc_rv_csr.sv"
`include "svc_rv_ext_zmmul.sv"
`include "svc_rv_ext_m.sv"
`include "svc_rv_forward.sv"
`include "svc_rv_hazard.sv"
`include "svc_rv_idec.sv"
`include "svc_rv_if_bram.sv"
`include "svc_rv_if_sram.sv"
`include "svc_rv_ld_fmt.sv"
`include "svc_rv_pc.sv"
`include "svc_rv_reg_ex_mem.sv"
`include "svc_rv_reg_id_ex.sv"
`include "svc_rv_reg_if_id.sv"
`include "svc_rv_reg_mem_wb.sv"
`include "svc_rv_regfile.sv"
`include "svc_rv_st_fmt.sv"

// For combinational (SRAM-style) memories: Use with IF_ID_REG=0 or 1
// For registered (BRAM-style) memories: Requires IF_ID_REG=1
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

    // Data memory write interface
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

  logic [XLEN-1:0] pc;
  logic [XLEN-1:0] pc_plus4;

  logic [    31:0] instr;
  logic            pc_sel;

  //
  // IF/ID pipeline register signals
  //
  logic [    31:0] instr_id;
  logic [XLEN-1:0] pc_id;
  logic [XLEN-1:0] pc_plus4_id;

  //
  // ID stage signals
  //
  logic            reg_write_id;
  logic            mem_read_id;
  logic            mem_write_id;
  logic [     1:0] alu_a_src_id;
  logic            alu_b_src_id;
  logic [     1:0] alu_instr_id;
  logic [     2:0] res_src_id;
  logic [     2:0] imm_type;
  logic            is_branch_id;
  logic            is_jump_id;
  logic            jb_target_src_id;
  logic            is_m_id;
  logic            is_mc_id;
  logic [     4:0] rd_id;
  logic [     4:0] rs1_id;
  logic [     4:0] rs2_id;
  logic [     2:0] funct3_id;
  logic [     6:0] funct7_id;
  logic            rs1_used_id;
  logic            rs2_used_id;
  logic [XLEN-1:0] imm_i;
  logic [XLEN-1:0] imm_s;
  logic [XLEN-1:0] imm_b;
  logic [XLEN-1:0] imm_u;
  logic [XLEN-1:0] imm_j;
  logic [XLEN-1:0] imm_id;
  logic [XLEN-1:0] rs1_data_id;
  logic [XLEN-1:0] rs2_data_id;

  //
  // Branch prediction signals
  //
  logic            bpred_taken_id;
  logic [XLEN-1:0] bpred_target_id;

  //
  // ID/EX pipeline register signals
  //
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
  logic            is_m_ex;
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

  //
  // EX stage signals
  //
  logic [     3:0] alu_op_ex;
  logic [XLEN-1:0] alu_a_ex;
  logic [XLEN-1:0] alu_b_ex;
  logic [XLEN-1:0] alu_result_ex;
  logic [XLEN-1:0] jb_target_ex;
  logic            mispredicted_ex;

  //
  // Multi-cycle operation control
  //
  // Signals for managing multi-cycle M extension operations (DIV/REM).
  // The FSM and signal definitions are located after the ALU section.
  //
  logic            op_active_ex;
  logic            op_en_ex;

  //
  // Zmmul extension signals
  //
  logic [XLEN-1:0] m_result_ex;
  logic            m_result_valid_ex;
  logic            m_busy_ex;

  //
  // EX/MEM pipeline register signals
  //
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
  logic [XLEN-1:0] result_mem;


  //
  // MEM/WB pipeline register signals
  //
  logic            reg_write_wb;
  logic [     2:0] res_src_wb;
  logic [    31:0] instr_wb;
  logic [     4:0] rd_wb;
  logic [XLEN-1:0] alu_result_wb;
  logic [XLEN-1:0] pc_plus4_wb;
  logic [XLEN-1:0] jb_target_wb;
  logic [XLEN-1:0] csr_rdata_wb;
  logic [     2:0] funct3_wb;
  logic [XLEN-1:0] m_result_wb;

  //
  // WB stage signals
  //
  logic [XLEN-1:0] rd_data;

  //
  // CSR signals
  //
  logic [XLEN-1:0] csr_rdata_ex;
  logic            instr_retired;

  //
  // Hazard control signals
  //
  logic            pc_stall;
  logic            if_id_stall;
  logic            if_id_flush;
  logic            id_ex_stall;
  logic            id_ex_flush;
  logic            ex_mem_stall;
  logic            mem_wb_stall;

  //
  // Instruction retirement
  //
  // An instruction retires when it reaches WB and is not a bubble.
  // Bubbles are injected as 0 on reset. Flushed instructions become NOPs
  // which also should not count as retired.
  //
  assign instr_retired = (instr_wb != 32'h0) && (instr_wb != I_NOP);

  //
  // PC redirect target calculation
  //
  // On misprediction, redirect to:
  // - pc_ex + 4 if predicted taken but actually not-taken
  // - jb_target_ex if predicted not-taken but actually taken
  // On actual taken branch/jump: jb_target_ex
  //
  logic [XLEN-1:0] pc_redirect_target;

  if (BPRED != 0) begin : g_pc_redirect
    always_comb begin
      case (1'b1)
        mispredicted_ex && branch_taken_ex:  pc_redirect_target = jb_target_ex;
        mispredicted_ex && !branch_taken_ex: pc_redirect_target = pc_ex + 4;
        default:                             pc_redirect_target = jb_target_ex;
      endcase
    end
  end else begin : g_no_pc_redirect
    assign pc_redirect_target = jb_target_ex;
  end

  //
  // PC
  //
  svc_rv_pc #(
      .XLEN(XLEN)
  ) pc_ctrl (
      .clk  (clk),
      .rst_n(rst_n),

      // hazard control
      .stall(pc_stall),

      // pc sources
      .pc_sel     (pc_sel),
      .jb_target  (pc_redirect_target),
      .pred_taken (bpred_taken_id),
      .pred_target(bpred_target_id),

      // pc output
      .pc      (pc),
      .pc_plus4(pc_plus4)
  );

  //
  // Instruction memory interface
  //
  assign imem_raddr = pc;
  assign instr      = imem_rdata;

  //
  // Memory read enables
  //
  // For BRAM: Instruction memory gated with PC stall to hold output
  // For BRAM: Data memory always enabled (address pipelined via EX_MEM_REG)
  // For SRAM: Always enabled
  //

  if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_bram_imem_ren
    assign imem_ren = !pc_stall;
  end else begin : g_sram_imem_ren
    assign imem_ren = 1'b1;
  end

  //
  // PC values for IF/ID register
  //
  // For BRAM: Need extra buffering to match 2-cycle instruction latency
  // For SRAM: Use PC directly
  //
  logic [XLEN-1:0] pc_to_if_id;
  logic [XLEN-1:0] pc_plus4_to_if_id;

  //
  // Instruction register (IF to ID)
  //
  // For SRAM with PIPELINED=1: register with if_id_stall/flush support
  // For SRAM with PIPELINED=0: pass through
  // For BRAM: Two-stage pipeline - always capture BRAM output, then
  // conditionally advance
  //
  if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_sram
    //
    // SRAM instruction fetch adapter
    //
    // Handles optional instruction registration for SRAM's 0-cycle latency
    //
    svc_rv_if_sram #(
        .XLEN     (XLEN),
        .PIPELINED(PIPELINED)
    ) if_sram (
        .clk              (clk),
        .rst_n            (rst_n),
        .if_id_stall      (if_id_stall),
        .if_id_flush      (if_id_flush),
        .pc               (pc),
        .pc_plus4         (pc_plus4),
        .instr_sram       (instr),
        .pc_to_if_id      (pc_to_if_id),
        .pc_plus4_to_if_id(pc_plus4_to_if_id),
        .instr_id         (instr_id)
    );
  end else begin : g_bram
    //
    // BRAM instruction fetch adapter
    //
    // Handles PC buffering and extended flush for BRAM's 1-cycle latency
    //
    svc_rv_if_bram #(
        .XLEN(XLEN)
    ) if_bram (
        .clk              (clk),
        .rst_n            (rst_n),
        .if_id_stall      (if_id_stall),
        .if_id_flush      (if_id_flush),
        .pc               (pc),
        .pc_plus4         (pc_plus4),
        .instr_bram       (instr),
        .pc_to_if_id      (pc_to_if_id),
        .pc_plus4_to_if_id(pc_plus4_to_if_id),
        .instr_id         (instr_id)
    );
  end

  //----------------------------------------------------------------------------
  // IF/ID Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_if_id #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED)
  ) reg_if_id (
      .clk  (clk),
      .rst_n(rst_n),

      // hazard control
      .stall(if_id_stall),
      .flush(if_id_flush),

      // IF signals
      .pc_if      (pc_to_if_id),
      .pc_plus4_if(pc_plus4_to_if_id),

      // ID signals
      .pc_id      (pc_id),
      .pc_plus4_id(pc_plus4_id)
  );

  //
  // Instruction Decode
  //
  svc_rv_idec #(
      .XLEN (XLEN),
      .EXT_M(EXT_ZMMUL | EXT_M)
  ) idec (
      .instr        (instr_id),
      .reg_write    (reg_write_id),
      .mem_read     (mem_read_id),
      .mem_write    (mem_write_id),
      .alu_a_src    (alu_a_src_id),
      .alu_b_src    (alu_b_src_id),
      .alu_instr    (alu_instr_id),
      .res_src      (res_src_id),
      .imm_type     (imm_type),
      .is_branch    (is_branch_id),
      .is_jump      (is_jump_id),
      .jb_target_src(jb_target_src_id),
      .is_m         (is_m_id),
      .rd           (rd_id),
      .rs1          (rs1_id),
      .rs2          (rs2_id),
      .funct3       (funct3_id),
      .funct7       (funct7_id),
      .rs1_used     (rs1_used_id),
      .rs2_used     (rs2_used_id),
      .imm_i        (imm_i),
      .imm_s        (imm_s),
      .imm_b        (imm_b),
      .imm_u        (imm_u),
      .imm_j        (imm_j)
  );

  //
  // Immediate mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (5)
  ) mux_imm (
      .sel (imm_type),
      .data({imm_u, imm_j, imm_b, imm_s, imm_i}),
      .out (imm_id)
  );

  //
  // Multi-cycle operation detection
  //
  // Identifies operations that require multiple cycles to complete.
  // Currently: DIV/REM (funct3[2]=1) from M extension (not ZMMUL)
  //
  assign is_mc_id = (EXT_M != 0) && is_m_id && funct3_id[2];

  //
  // Register File
  //
  svc_rv_regfile #(
      .XLEN       (XLEN),
      .FWD_REGFILE(FWD_REGFILE)
  ) regfile (
      .clk     (clk),
      .rst_n   (rst_n),
      .rs1_addr(rs1_id),
      .rs1_data(rs1_data_id),
      .rs2_addr(rs2_id),
      .rs2_data(rs2_data_id),
      .rd_en   (reg_write_wb),
      .rd_addr (rd_wb),
      .rd_data (rd_data)
  );

  //
  // Decode result sources for hazard detection and forwarding
  //
  // These signals are shared by both the hazard unit and forwarding logic
  //
  logic is_load_ex;
  logic is_csr_ex;
  logic is_load_mem;
  logic is_csr_mem;
  logic is_m_mem;

  assign is_load_ex  = (res_src_ex == RES_MEM);
  assign is_csr_ex   = (res_src_ex == RES_CSR);
  assign is_load_mem = (res_src_mem == RES_MEM);
  assign is_csr_mem  = (res_src_mem == RES_CSR);
  assign is_m_mem    = (res_src_mem == RES_M);

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
        .MEM_TYPE   (MEM_TYPE),
        .BPRED      (BPRED)
    ) hazard (
        // ID stage register addresses
        .rs1_id      (rs1_id),
        .rs2_id      (rs2_id),
        .rs1_used    (rs1_used_id),
        .rs2_used    (rs2_used_id),
        .is_branch_id(is_branch_id),

        // EX stage
        .rd_ex       (rd_ex),
        .reg_write_ex(reg_write_ex),
        .is_load_ex  (is_load_ex),
        .is_csr_ex   (is_csr_ex),
        .op_active_ex(op_active_ex),

        // MEM stage
        .rd_mem       (rd_mem),
        .reg_write_mem(reg_write_mem),
        .is_load_mem  (is_load_mem),
        .is_csr_mem   (is_csr_mem),

        // WB stage
        .rd_wb       (rd_wb),
        .reg_write_wb(reg_write_wb),

        // Control flow changes
        .pc_sel(pc_sel),

        // Branch prediction
        .pred_taken_id(bpred_taken_id),

        // Branch misprediction
        .mispredicted_ex(mispredicted_ex),

        // hazard control outputs
        .pc_stall    (pc_stall),
        .if_id_stall (if_id_stall),
        .if_id_flush (if_id_flush),
        .id_ex_stall (id_ex_stall),
        .id_ex_flush (id_ex_flush),
        .ex_mem_stall(ex_mem_stall),
        .mem_wb_stall(mem_wb_stall)
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
    `SVC_UNUSED({is_load_ex, is_csr_ex, is_load_mem, is_csr_mem,
                 rs1_used_id, rs2_used_id });
    // verilog_format: on
  end

  //----------------------------------------------------------------------------
  // ID/EX Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_id_ex #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED)
  ) reg_id_ex (
      .clk  (clk),
      .rst_n(rst_n),

      // hazard control
      .stall(id_ex_stall),
      .flush(id_ex_flush),

      // ID stage inputs
      .reg_write_id    (reg_write_id),
      .mem_read_id     (mem_read_id),
      .mem_write_id    (mem_write_id),
      .alu_a_src_id    (alu_a_src_id),
      .alu_b_src_id    (alu_b_src_id),
      .alu_instr_id    (alu_instr_id),
      .res_src_id      (res_src_id),
      .is_branch_id    (is_branch_id),
      .is_jump_id      (is_jump_id),
      .jb_target_src_id(jb_target_src_id),
      .is_m_id         (is_m_id),
      .is_mc_id        (is_mc_id),
      .instr_id        (instr_id),
      .rd_id           (rd_id),
      .rs1_id          (rs1_id),
      .rs2_id          (rs2_id),
      .funct3_id       (funct3_id),
      .funct7_id       (funct7_id),
      .rs1_data_id     (rs1_data_id),
      .rs2_data_id     (rs2_data_id),
      .imm_id          (imm_id),
      .pc_id           (pc_id),
      .pc_plus4_id     (pc_plus4_id),
      .bpred_taken_id  (bpred_taken_id),

      // EX stage outputs
      .reg_write_ex    (reg_write_ex),
      .mem_read_ex     (mem_read_ex),
      .mem_write_ex    (mem_write_ex),
      .alu_a_src_ex    (alu_a_src_ex),
      .alu_b_src_ex    (alu_b_src_ex),
      .alu_instr_ex    (alu_instr_ex),
      .res_src_ex      (res_src_ex),
      .is_branch_ex    (is_branch_ex),
      .is_jump_ex      (is_jump_ex),
      .jb_target_src_ex(jb_target_src_ex),
      .is_m_ex         (is_m_ex),
      .is_mc_ex        (is_mc_ex),
      .instr_ex        (instr_ex),
      .rd_ex           (rd_ex),
      .rs1_ex          (rs1_ex),
      .rs2_ex          (rs2_ex),
      .funct3_ex       (funct3_ex),
      .funct7_ex       (funct7_ex),
      .rs1_data_ex     (rs1_data_ex),
      .rs2_data_ex     (rs2_data_ex),
      .imm_ex          (imm_ex),
      .pc_ex           (pc_ex),
      .pc_plus4_ex     (pc_plus4_ex),
      .bpred_taken_ex  (bpred_taken_ex)
  );

  //
  // ALU Decoder
  //
  svc_rv_alu_dec alu_dec (
      .alu_instr(alu_instr_ex),
      .funct3   (funct3_ex),
      .funct7_b5(funct7_ex[5]),
      .op_b5    (instr_ex[5]),
      .alu_op   (alu_op_ex)
  );

  //
  // Data forwarding unit
  //
  logic [XLEN-1:0] rs1_fwd_ex;
  logic [XLEN-1:0] rs2_fwd_ex;

  //
  // MEM stage result mux
  //
  // Select the actual result in MEM stage based on res_src_mem.
  // This unified result is forwarded to resolve data hazards.
  //
  assign result_mem = is_m_mem ? m_result_mem : alu_result_mem;

  svc_rv_forward #(
      .XLEN    (XLEN),
      .FWD     ((PIPELINED != 0 && FWD != 0) ? 1 : 0),
      .MEM_TYPE(MEM_TYPE)
  ) forward (
      // EX stage inputs
      .rs1_ex     (rs1_ex),
      .rs2_ex     (rs2_ex),
      .rs1_data_ex(rs1_data_ex),
      .rs2_data_ex(rs2_data_ex),

      // MEM stage inputs
      .rd_mem       (rd_mem),
      .reg_write_mem(reg_write_mem),
      .is_load_mem  (is_load_mem),
      .is_csr_mem   (is_csr_mem),
      .result_mem   (result_mem),
      .load_data_mem(dmem_rdata_ext_mem),

      // WB stage inputs
      .rd_wb       (rd_wb),
      .reg_write_wb(reg_write_wb),
      .rd_data     (rd_data),

      // Forwarded outputs
      .rs1_fwd_ex(rs1_fwd_ex),
      .rs2_fwd_ex(rs2_fwd_ex)
  );

  //
  // ALU A input mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (3)
  ) mux_alu_a (
      .sel (alu_a_src_ex),
      .data({pc_ex, {XLEN{1'b0}}, rs1_fwd_ex}),
      .out (alu_a_ex)
  );

  //
  // ALU B input mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_alu_b (
      .sel (alu_b_src_ex),
      .data({imm_ex, rs2_fwd_ex}),
      .out (alu_b_ex)
  );

  //
  // ALU
  //
  svc_rv_alu #(
      .XLEN(XLEN)
  ) alu (
      .a     (alu_a_ex),
      .b     (alu_b_ex),
      .alu_op(alu_op_ex),
      .result(alu_result_ex)
  );

  //
  // Multi-cycle operation control state machine
  //
  // Manages the lifecycle of multi-cycle operations (DIV/REM) in EX stage.
  //
  // States:
  //   IDLE: No multi-cycle operation active
  //   EXEC: Multi-cycle operation executing
  //
  // For single-cycle M ops (MUL): IDLE -> IDLE (never enter EXEC)
  // For multi-cycle M ops (DIV/REM): IDLE -> EXEC -> IDLE
  //
  typedef enum logic {
    MC_STATE_IDLE,
    MC_STATE_EXEC
  } mc_state_t;

  mc_state_t mc_state;
  mc_state_t mc_state_next;

  //
  // Next state and output logic
  //
  always_comb begin
    mc_state_next = mc_state;
    op_active_ex  = 1'b0;
    op_en_ex      = 1'b0;

    case (mc_state)
      MC_STATE_IDLE: begin
        if (is_mc_ex) begin
          op_en_ex      = 1'b1;
          op_active_ex  = 1'b1;
          mc_state_next = MC_STATE_EXEC;
        end
      end

      MC_STATE_EXEC: begin
        if (!m_busy_ex) begin
          mc_state_next = MC_STATE_IDLE;
        end else begin
          op_active_ex = 1'b1;
        end
      end

      default: begin
        mc_state_next = MC_STATE_IDLE;
      end
    endcase
  end

  //
  // State registers
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      mc_state <= MC_STATE_IDLE;
    end else begin
      mc_state <= mc_state_next;
    end
  end

  //
  // M Extension Unit
  //
  if (EXT_ZMMUL != 0) begin : g_m_ext
    svc_rv_ext_zmmul ext_zmmul (
        .clk         (clk),
        .rst_n       (rst_n),
        .en          (op_en_ex),
        .rs1         (rs1_fwd_ex),
        .rs2         (rs2_fwd_ex),
        .op          (funct3_ex),
        .busy        (m_busy_ex),
        .result      (m_result_ex),
        .result_valid(m_result_valid_ex)
    );
  end else if (EXT_M != 0) begin : g_m_ext
    svc_rv_ext_m ext_m (
        .clk         (clk),
        .rst_n       (rst_n),
        .en          (op_en_ex),
        .rs1         (rs1_fwd_ex),
        .rs2         (rs2_fwd_ex),
        .op          (funct3_ex),
        .busy        (m_busy_ex),
        .result      (m_result_ex),
        .result_valid(m_result_valid_ex)
    );
  end else begin : g_no_m_ext
    assign m_result_ex       = '0;
    assign m_result_valid_ex = 1'b0;
    assign m_busy_ex         = 1'b0;

    `SVC_UNUSED({op_en_ex, op_active_ex});
  end

  //
  // Jump/Branch target calculation
  //
  // Two target address calculation modes:
  //
  // 1. PC-relative (JAL and all branches):
  //    target = PC + offset
  //    Used by: JAL, BEQ, BNE, BLT, BGE, BLTU, BGEU
  //
  // 2. Register-indirect (JALR only):
  //    target = (rs1 + offset) & ~1
  //    The ALU computes rs1+offset, then LSB is cleared per RISC-V spec.
  //    This ensures all jump targets are aligned to even addresses
  //
  logic [XLEN-1:0] jb_target_jalr;
  logic [XLEN-1:0] jb_target_pc_rel;

  //
  // JALR target: ALU result with LSB cleared
  //
  assign jb_target_jalr   = {alu_result_ex[XLEN-1:1], 1'b0};

  //
  // PC-relative target: Dedicated adder for JAL and branches
  //
  assign jb_target_pc_rel = pc_ex + imm_ex;

  svc_muxn #(
      .WIDTH(XLEN),
      .N    (2)
  ) mux_jb_target (
      .sel (jb_target_src_ex),
      .data({jb_target_jalr, jb_target_pc_rel}),
      .out (jb_target_ex)
  );

  //
  // Branch comparison (spans ID and EX stages)
  //
  // TODO: it is worth looking into making the regfile a bram interface,
  // in which case this would need to split into EX and MEM stages, adding
  // an extra cycle for branches. Once a predictor is in place, revisit this
  // and see how overall CPI is impacted and total perf from being able to
  // run at faster clocks.
  //
  logic branch_taken_ex;

  svc_rv_bcmp #(
      .XLEN(XLEN)
  ) bcmp (
      .a_ex           (rs1_fwd_ex),
      .b_ex           (rs2_fwd_ex),
      .funct3         (funct3_ex),
      .branch_taken_ex(branch_taken_ex)
  );

  //
  // Branch Prediction
  //
  // Static BTFNT (Backward Taken/Forward Not-Taken) prediction:
  // - Backward branches (negative immediate): predict taken
  // - Forward branches (positive immediate): predict not-taken
  // - JAL (unconditional PC-relative jump): predict taken
  //
  if (BPRED != 0) begin : g_bpred
    //
    // Prediction based on immediate sign (only for branches) and JAL
    //
    // Backward branches (negative displacement, imm[31]=1): predict taken
    // Forward branches (positive displacement, imm[31]=0): predict not-taken
    // JAL (PC-relative jump): predict taken
    // JALR (register-indirect): not predicted (wait for ALU)
    //
    assign bpred_taken_id = ((is_branch_id && imm_id[XLEN-1]) ||
                             (is_jump_id && !jb_target_src_id));

    //
    // Predicted target calculation (PC-relative for branches and JAL)
    //
    assign bpred_target_id = pc_id + imm_id;

    //
    // Misprediction detection (actual outcome vs prediction)
    //
    assign
        mispredicted_ex = is_branch_ex && (bpred_taken_ex != branch_taken_ex);
  end else begin : g_no_bpred
    assign bpred_taken_id  = 1'b0;
    assign bpred_target_id = '0;
    assign mispredicted_ex = 1'b0;

    `SVC_UNUSED(bpred_taken_ex);
  end

  //
  // PC muxing and misprediction recovery
  //
  // pc_sel triggers PC redirection for:
  // - Actual taken branches (only if not correctly predicted)
  // - Jumps (JALR always, JAL only if not predicted)
  // - Branch mispredictions (need to redirect to correct target)
  //
  // When BPRED is enabled:
  //   - JAL is handled by predictor in ID stage, so don't redirect in EX
  //   - JALR still needs EX stage redirect (requires ALU result)
  //   - Branches handled by predictor, only redirect on misprediction
  //   - Mispredictions trigger recovery
  //
  logic pc_sel_jump;
  logic pc_sel_branch;

  if (BPRED != 0) begin : g_pc_sel_jump
    //
    // Only JALR triggers pc_sel (JAL is predicted in ID)
    //
    assign pc_sel_jump   = is_jump_ex && jb_target_src_ex;

    //
    // Branches don't trigger pc_sel (handled by predictor or misprediction)
    //
    assign pc_sel_branch = 1'b0;
  end else begin : g_no_pc_sel_jump
    //
    // All jumps trigger pc_sel
    //
    assign pc_sel_jump   = is_jump_ex;

    //
    // Taken branches trigger pc_sel
    //
    assign pc_sel_branch = is_branch_ex & branch_taken_ex;
  end

  assign pc_sel = pc_sel_branch | pc_sel_jump | mispredicted_ex;

  //
  // CSR (Control and Status Registers) - Zicntr
  //
  svc_rv_csr csr (
      .clk        (clk),
      .rst_n      (rst_n),
      .csr_addr   (imm_ex[11:0]),
      .csr_rdata  (csr_rdata_ex),
      .instret_inc(instr_retired)
  );

  //----------------------------------------------------------------------------
  // EX/MEM Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_ex_mem #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED)
  ) reg_ex_mem (
      .clk  (clk),
      .rst_n(rst_n),

      // Hazard control
      .stall(ex_mem_stall),

      // EX stage inputs
      .reg_write_ex (reg_write_ex),
      .mem_read_ex  (mem_read_ex),
      .mem_write_ex (mem_write_ex),
      .res_src_ex   (res_src_ex),
      .instr_ex     (instr_ex),
      .rd_ex        (rd_ex),
      .rs2_ex       (rs2_ex),
      .funct3_ex    (funct3_ex),
      .alu_result_ex(alu_result_ex),
      .rs2_data_ex  (rs2_fwd_ex),
      .pc_plus4_ex  (pc_plus4_ex),
      .jb_target_ex (jb_target_ex),
      .csr_rdata_ex (csr_rdata_ex),
      .m_result_ex  (m_result_ex),

      // MEM stage outputs
      .reg_write_mem (reg_write_mem),
      .mem_read_mem  (mem_read_mem),
      .mem_write_mem (mem_write_mem),
      .res_src_mem   (res_src_mem),
      .instr_mem     (instr_mem),
      .rd_mem        (rd_mem),
      .rs2_mem       (rs2_mem),
      .funct3_mem    (funct3_mem),
      .alu_result_mem(alu_result_mem),
      .rs2_data_mem  (rs2_data_mem),
      .pc_plus4_mem  (pc_plus4_mem),
      .jb_target_mem (jb_target_mem),
      .csr_rdata_mem (csr_rdata_mem),
      .m_result_mem  (m_result_mem)
  );

  //
  // Data memory (store formatting)
  //
  // Stores use rs2_data_mem, which comes from rs2_fwd_ex pipelined through
  // the EX/MEM register. This means stores automatically get forwarded values.
  //
  svc_rv_st_fmt #(
      .XLEN(XLEN)
  ) st_fmt (
      .data_in  (rs2_data_mem),
      .addr     (alu_result_mem[1:0]),
      .funct3   (funct3_mem),
      .mem_write(mem_write_mem),
      .data_out (dmem_wdata),
      .wstrb    (dmem_wstrb)
  );

  //
  // Data memory interface
  //
  assign dmem_ren   = mem_read_mem;
  assign dmem_raddr = alu_result_mem;

  assign dmem_we    = mem_write_mem;
  assign dmem_waddr = alu_result_mem;

  //
  // Load data extension
  //
  // For SRAM: Format in MEM stage (combinational memory)
  // For BRAM: Format in WB stage (registered memory)
  //
  logic [XLEN-1:0] dmem_rdata_ext_mem;
  // verilator lint_off UNDRIVEN
  logic [XLEN-1:0] dmem_rdata_ext_wb_direct;
  // verilator lint_on UNDRIVEN

  logic [     1:0] ld_fmt_addr;
  logic [     2:0] ld_fmt_funct3;
  logic [XLEN-1:0] ld_fmt_out;

  if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_ld_fmt_signals_sram
    assign ld_fmt_addr        = alu_result_mem[1:0];
    assign ld_fmt_funct3      = funct3_mem;
    assign dmem_rdata_ext_mem = ld_fmt_out;

    `SVC_UNUSED({funct3_wb});
  end else begin : g_ld_fmt_signals_bram
    assign ld_fmt_addr              = alu_result_wb[1:0];
    assign ld_fmt_funct3            = funct3_wb;
    assign dmem_rdata_ext_wb_direct = ld_fmt_out;
    assign dmem_rdata_ext_mem       = '0;
  end

  svc_rv_ld_fmt #(
      .XLEN(XLEN)
  ) ld_fmt (
      .data_in (dmem_rdata),
      .addr    (ld_fmt_addr),
      .funct3  (ld_fmt_funct3),
      .data_out(ld_fmt_out)
  );

  //----------------------------------------------------------------------------
  // MEM/WB Pipeline Boundary
  //----------------------------------------------------------------------------

  svc_rv_reg_mem_wb #(
      .XLEN     (XLEN),
      .PIPELINED(PIPELINED)
  ) reg_mem_wb (
      .clk  (clk),
      .rst_n(rst_n),

      // Hazard control
      .stall(mem_wb_stall),

      // MEM stage inputs
      .reg_write_mem     (reg_write_mem),
      .res_src_mem       (res_src_mem),
      .funct3_mem        (funct3_mem),
      .instr_mem         (instr_mem),
      .rd_mem            (rd_mem),
      .alu_result_mem    (alu_result_mem),
      .dmem_rdata_ext_mem(dmem_rdata_ext_mem),
      .pc_plus4_mem      (pc_plus4_mem),
      .jb_target_mem     (jb_target_mem),
      .csr_rdata_mem     (csr_rdata_mem),
      .m_result_mem      (m_result_mem),

      // WB stage outputs
      .reg_write_wb     (reg_write_wb),
      .res_src_wb       (res_src_wb),
      .funct3_wb        (funct3_wb),
      .instr_wb         (instr_wb),
      .rd_wb            (rd_wb),
      .alu_result_wb    (alu_result_wb),
      .dmem_rdata_ext_wb(dmem_rdata_ext_wb_piped),
      .pc_plus4_wb      (pc_plus4_wb),
      .jb_target_wb     (jb_target_wb),
      .csr_rdata_wb     (csr_rdata_wb),
      .m_result_wb      (m_result_wb)
  );

  //----------------------------------------------------------------------------
  // WB Stage
  //----------------------------------------------------------------------------

  //
  // Select formatted load data based on memory type
  //
  // For SRAM: Use pipelined data from MEM stage formatter
  // For BRAM: Use direct data from WB stage formatter
  //
  logic [XLEN-1:0] dmem_rdata_ext_wb;
  logic [XLEN-1:0] dmem_rdata_ext_wb_piped;

  assign dmem_rdata_ext_wb = (MEM_TYPE == MEM_TYPE_BRAM) ?
      dmem_rdata_ext_wb_direct : dmem_rdata_ext_wb_piped;

  //
  // Result mux
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (6)
  ) mux_res (
      .sel(res_src_wb),
      .data({
        m_result_wb,
        csr_rdata_wb,
        jb_target_wb,
        pc_plus4_wb,
        dmem_rdata_ext_wb,
        alu_result_wb
      }),
      .out(rd_data)
  );

  assign ebreak = (rst_n && instr_wb == I_EBREAK);

  //
  // Note: m_result_valid_ex is currently unused but m_busy_ex is now
  // integrated into pipeline stall control for multi-cycle operations.
  //
  `SVC_UNUSED({IMEM_AW, DMEM_AW, pc, pc_plus4, pc_id[1:0], pc_ex[1:0],
               funct7_id[6], funct7_id[4:0], funct7_ex[6], funct7_ex[4:0],
               rs1_ex, rs2_ex, instr_ex, rs2_mem, is_m_ex, m_result_valid_ex});

endmodule

`endif
