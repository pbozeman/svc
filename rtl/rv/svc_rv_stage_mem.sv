`ifndef SVC_RV_STAGE_MEM_SV
`define SVC_RV_STAGE_MEM_SV

`include "svc.sv"
`include "svc_unused.sv"

`include "svc_rv_ld_fmt.sv"
`include "svc_rv_st_fmt.sv"

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
    parameter int XLEN      = 32,
    parameter int PIPELINED = 0,
    parameter int MEM_TYPE  = 0
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic mem_wb_stall,

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
    input logic [XLEN-1:0] rs2_data_mem,
    input logic [XLEN-1:0] pc_plus4_mem,
    input logic [XLEN-1:0] jb_target_mem,
    input logic [XLEN-1:0] csr_rdata_mem,
    input logic [XLEN-1:0] m_result_mem,

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
    output logic [XLEN-1:0] alu_result_wb,
    output logic [XLEN-1:0] dmem_rdata_ext_wb,
    output logic [XLEN-1:0] pc_plus4_wb,
    output logic [XLEN-1:0] jb_target_wb,
    output logic [XLEN-1:0] csr_rdata_wb,
    output logic [XLEN-1:0] m_result_wb,

    //
    // Outputs for forwarding (MEM stage result)
    //
    output logic [XLEN-1:0] result_mem,
    output logic [XLEN-1:0] load_data_mem
);

  `include "svc_rv_defs.svh"

  //
  // Store data formatting
  //
  // Stores use rs2_data_mem, which comes from fwd_rs2_ex in EX stage.
  // This means stores automatically get forwarded values.
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

  logic [     1:0] ld_fmt_addr;
  logic [     2:0] ld_fmt_funct3;
  logic [XLEN-1:0] ld_fmt_out;

  if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_ld_fmt_signals_sram
    assign ld_fmt_addr        = alu_result_mem[1:0];
    assign ld_fmt_funct3      = funct3_mem;
    assign dmem_rdata_ext_mem = ld_fmt_out;

  end else begin : g_ld_fmt_signals_bram
    //
    // Internal funct3_wb for BRAM load formatting
    //
    logic [2:0] funct3_wb;

    assign ld_fmt_addr        = alu_result_wb[1:0];
    assign ld_fmt_funct3      = funct3_wb;

    //
    // BRAM formatter output is already WB-stage timed
    //
    assign dmem_rdata_ext_mem = '0;
    assign dmem_rdata_ext_wb  = ld_fmt_out;
  end

  svc_rv_ld_fmt #(
      .XLEN(XLEN)
  ) ld_fmt (
      .data_in (dmem_rdata),
      .addr    (ld_fmt_addr),
      .funct3  (ld_fmt_funct3),
      .data_out(ld_fmt_out)
  );

  //
  // MEM stage result for forwarding
  //
  // Select the actual result in MEM stage based on res_src_mem.
  // This unified result is forwarded to resolve data hazards.
  //
  // RES_M: M extension (multiply/divide) result
  // RES_TGT: Jump/branch target (used by AUIPC)
  // Default: ALU result (most instructions)
  //
  always_comb begin
    case (res_src_mem)
      RES_M:   result_mem = m_result_mem;
      RES_TGT: result_mem = jb_target_mem;
      default: result_mem = alu_result_mem;
    endcase
  end

  assign load_data_mem = dmem_rdata_ext_mem;

  //
  // MEM/WB Pipeline Register
  //
  if (PIPELINED != 0) begin : g_registered
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        reg_write_wb  <= 1'b0;
        res_src_wb    <= '0;
        instr_wb      <= I_NOP;
        rd_wb         <= '0;
        alu_result_wb <= '0;
        pc_plus4_wb   <= '0;
        jb_target_wb  <= '0;
        csr_rdata_wb  <= '0;
        m_result_wb   <= '0;
      end else if (!mem_wb_stall) begin
        reg_write_wb  <= reg_write_mem;
        res_src_wb    <= res_src_mem;
        instr_wb      <= instr_mem;
        rd_wb         <= rd_mem;
        alu_result_wb <= alu_result_mem;
        pc_plus4_wb   <= pc_plus4_mem;
        jb_target_wb  <= jb_target_mem;
        csr_rdata_wb  <= csr_rdata_mem;
        m_result_wb   <= m_result_mem;
      end
    end

    //
    // Register funct3 for BRAM load formatting in WB stage
    //
    if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_funct3_reg
      always_ff @(posedge clk) begin
        if (!mem_wb_stall) begin
          g_ld_fmt_signals_bram.funct3_wb <= funct3_mem;
        end
      end
    end

    //
    // Pipeline SRAM load data
    //
    // BRAM data is already assigned in the formatter section above
    //
    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_dmem_rdata_sram
      logic [XLEN-1:0] dmem_rdata_ext_wb_piped;

      always_ff @(posedge clk) begin
        if (!rst_n) begin
          dmem_rdata_ext_wb_piped <= '0;
        end else if (!mem_wb_stall) begin
          dmem_rdata_ext_wb_piped <= dmem_rdata_ext_mem;
        end
      end

      assign dmem_rdata_ext_wb = dmem_rdata_ext_wb_piped;
    end

  end else begin : g_passthrough
    assign reg_write_wb  = reg_write_mem;
    assign res_src_wb    = res_src_mem;
    assign instr_wb      = instr_mem;
    assign rd_wb         = rd_mem;
    assign alu_result_wb = alu_result_mem;
    assign pc_plus4_wb   = pc_plus4_mem;
    assign jb_target_wb  = jb_target_mem;
    assign csr_rdata_wb  = csr_rdata_mem;
    assign m_result_wb   = m_result_mem;

    //
    // Pass through SRAM load data
    //
    // BRAM data is already assigned in the formatter section above
    //
    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_dmem_rdata_sram
      assign dmem_rdata_ext_wb = dmem_rdata_ext_mem;
    end

    //
    // For non-pipelined + BRAM mode, funct3 passthrough
    //
    if (MEM_TYPE == MEM_TYPE_BRAM) begin : g_funct3_passthrough
      assign g_ld_fmt_signals_bram.funct3_wb = funct3_mem;
    end

    `SVC_UNUSED({clk, rst_n, mem_wb_stall});
  end

endmodule

`endif
