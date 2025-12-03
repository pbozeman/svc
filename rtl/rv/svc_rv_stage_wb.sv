`ifndef SVC_RV_STAGE_WB_SV
`define SVC_RV_STAGE_WB_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_rv_ext_mul_wb.sv"
`include "svc_unused.sv"

//
// RISC-V Write-Back (WB) Stage
//
// Encapsulates all logic for the writeback pipeline stage:
// - Final result selection mux
// - EBREAK detection
// - Write-back to register file (handled by ID stage)
//
// This is the final stage of the pipeline that selects the final
// result value to be written back to the register file.
//
module svc_rv_stage_wb #(
    parameter int XLEN = 32
) (
    input logic clk,
    input logic rst_n,

    //
    // From MEM stage
    //
    input logic [     2:0] res_src_wb,
    input logic [    31:0] instr_wb,
    input logic [XLEN-1:0] alu_result_wb,
    input logic [XLEN-1:0] ld_data_wb,
    input logic [XLEN-1:0] pc_plus4_wb,
    input logic [XLEN-1:0] jb_target_wb,
    input logic [XLEN-1:0] csr_rdata_wb,
    input logic [XLEN-1:0] m_result_wb,
    input logic [     2:0] funct3_wb,
    input logic [XLEN-1:0] rs1_data_wb,
    input logic [XLEN-1:0] rs2_data_wb,
    input logic [    63:0] product_64_wb,
    input logic            trap_wb,
    input logic [     1:0] trap_code_wb,
    input logic            reg_write_wb,

`ifdef RISCV_FORMAL
    //
    // RVFI memory signals from MEM stage
    //
    input logic            f_mem_write_wb,
    input logic [XLEN-1:0] f_dmem_waddr_wb,
    input logic [XLEN-1:0] f_dmem_raddr_wb,
    input logic [XLEN-1:0] f_dmem_wdata_wb,
    input logic [     3:0] f_dmem_wstrb_wb,
    input logic [XLEN-1:0] f_dmem_rdata_wb,
    input logic [     3:0] f_dmem_rstrb_wb,
`endif

    //
    // Ready/valid interface from MEM stage
    //
    input  logic s_valid,
    output logic s_ready,

    //
    // Manager interface to svc_rv
    //
    output logic m_valid,
    input  logic m_ready,

    //
    // Retired instruction outputs
    //
    output logic [    31:0] instr_ret,
    output logic [XLEN-1:0] pc_ret,
    output logic [XLEN-1:0] rs1_data_ret,
    output logic [XLEN-1:0] rs2_data_ret,
    output logic [XLEN-1:0] rd_data_ret,
    output logic            trap_ret,
    output logic [     1:0] trap_code_ret,
    output logic            reg_write_ret,
    output logic            ebreak_ret,

`ifdef RISCV_FORMAL
    //
    // RVFI memory signals (registered on retirement)
    //
    output logic            f_mem_write_ret,
    output logic [XLEN-1:0] f_dmem_waddr_ret,
    output logic [XLEN-1:0] f_dmem_raddr_ret,
    output logic [XLEN-1:0] f_dmem_wdata_ret,
    output logic [     3:0] f_dmem_wstrb_ret,
    output logic [XLEN-1:0] f_dmem_rdata_ret,
    output logic [     3:0] f_dmem_rstrb_ret,
`endif

    //
    // Output to register file in ID stage (combinational, for same-cycle write)
    //
    output logic [XLEN-1:0] rd_data_wb
);
  //
  // Handshake: instruction accepted into stage
  //
  logic s_accept;
  assign s_accept = s_valid && s_ready;

  `include "svc_rv_defs.svh"

  //
  // Multiply sign correction (WB stage)
  //
  // Applies sign correction to unsigned product from MEM stage.
  // This is done in WB stage to improve timing (VexRiscv algorithm).
  //
  logic [XLEN-1:0] mul_result_wb;

  svc_rv_ext_mul_wb ext_mul_wb (
      .product_64(product_64_wb),
      .rs1_data  (rs1_data_wb),
      .rs2_data  (rs2_data_wb),
      .op        (funct3_wb),
      .result    (mul_result_wb)
  );

  //
  // M extension result selection
  //
  // Division results (m_result_wb) complete in MEM stage.
  // Multiply results (mul_result_wb) complete in WB stage.
  // Select based on operation type (funct3[2]: 0=multiply, 1=division).
  //
  logic [XLEN-1:0] m_ext_result_wb;

  assign m_ext_result_wb = funct3_wb[2] ? m_result_wb : mul_result_wb;

  //
  // Result mux
  //
  // Selects final result to write back to register file based on instruction type
  //
  svc_muxn #(
      .WIDTH(XLEN),
      .N    (6)
  ) mux_res (
      .sel(res_src_wb),
      .data({
        m_ext_result_wb,
        csr_rdata_wb,
        jb_target_wb,
        pc_plus4_wb,
        ld_data_wb,
        alu_result_wb
      }),
      .out(rd_data_wb)
  );

  //
  // Ready/valid interface
  //
  assign s_ready = !m_valid || m_ready;

  //
  // Pipeline
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      m_valid       <= 1'b0;
      instr_ret     <= '0;
      pc_ret        <= '0;
      rs1_data_ret  <= '0;
      rs2_data_ret  <= '0;
      rd_data_ret   <= '0;
      trap_ret      <= 1'b0;
      trap_code_ret <= '0;
      reg_write_ret <= 1'b0;
      ebreak_ret    <= 1'b0;
    end else begin
      if (s_accept) begin
        m_valid       <= 1'b1;
        instr_ret     <= instr_wb;
        pc_ret        <= pc_plus4_wb - XLEN'(32'd4);
        rs1_data_ret  <= rs1_data_wb;
        rs2_data_ret  <= rs2_data_wb;
        rd_data_ret   <= rd_data_wb;
        trap_ret      <= trap_wb;
        trap_code_ret <= trap_code_wb;
        reg_write_ret <= reg_write_wb;
        ebreak_ret    <= (instr_wb == I_EBREAK);
      end else if (m_ready) begin
        m_valid <= 1'b0;
      end
    end
  end

`ifdef RISCV_FORMAL
  //
  // RVFI memory signal registers
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_mem_write_ret  <= 1'b0;
      f_dmem_waddr_ret <= '0;
      f_dmem_raddr_ret <= '0;
      f_dmem_wdata_ret <= '0;
      f_dmem_wstrb_ret <= '0;
      f_dmem_rdata_ret <= '0;
      f_dmem_rstrb_ret <= '0;
    end else if (s_accept) begin
      f_mem_write_ret  <= f_mem_write_wb;
      f_dmem_waddr_ret <= f_dmem_waddr_wb;
      f_dmem_raddr_ret <= f_dmem_raddr_wb;
      f_dmem_wdata_ret <= f_dmem_wdata_wb;
      f_dmem_wstrb_ret <= f_dmem_wstrb_wb;
      f_dmem_rdata_ret <= f_dmem_rdata_wb;
      f_dmem_rstrb_ret <= f_dmem_rstrb_wb;
    end
  end
`endif

  //
  // Formal verification
  //
`ifdef FORMAL
`ifdef FORMAL_SVC_RV_STAGE_WB
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
  // Ready/valid relationship assertions
  //
  // Pipeline register semantics:
  // - s_ready allows accepting when empty (!m_valid) or output consumed (m_ready)
  // - m_valid goes high on s_accept, low on m_ready without s_accept
  //
  always_comb begin
    `FASSERT(a_s_ready_formula, s_ready == (!m_valid || m_ready));
  end

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      //
      // m_valid goes high after s_accept
      //
      if ($past(s_accept)) begin
        `FASSERT(a_m_valid_after_accept, m_valid);
      end

      //
      // m_valid goes low after m_ready without s_accept
      //
      if ($past(m_ready && !s_accept)) begin
        `FASSERT(a_m_valid_clears, !m_valid);
      end

      //
      // All outputs stable while m_valid && !m_ready
      //
      if ($past(m_valid && !m_ready)) begin
        `FASSERT(a_m_valid_stable, $stable(m_valid));
        `FASSERT(a_instr_ret_stable, $stable(instr_ret));
        `FASSERT(a_pc_ret_stable, $stable(pc_ret));
        `FASSERT(a_rs1_data_ret_stable, $stable(rs1_data_ret));
        `FASSERT(a_rs2_data_ret_stable, $stable(rs2_data_ret));
        `FASSERT(a_rd_data_ret_stable, $stable(rd_data_ret));
        `FASSERT(a_trap_ret_stable, $stable(trap_ret));
        `FASSERT(a_trap_code_ret_stable, $stable(trap_code_ret));
        `FASSERT(a_reg_write_ret_stable, $stable(reg_write_ret));
        `FASSERT(a_ebreak_ret_stable, $stable(ebreak_ret));
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
      // Cover halt conditions in retiring instruction
      //
      `FCOVER(c_ebreak_ret, ebreak_ret);
      `FCOVER(c_trap_ret, trap_ret);
    end
  end

  `undef FASSERT
  `undef FASSUME
  `undef FCOVER
`endif

endmodule

`endif
