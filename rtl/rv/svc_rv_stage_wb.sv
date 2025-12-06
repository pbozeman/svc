`ifndef SVC_RV_STAGE_WB_SV
`define SVC_RV_STAGE_WB_SV

`include "svc.sv"
`include "svc_muxn.sv"
`include "svc_rv_ext_mul_wb.sv"
`include "svc_rv_pipe_ctrl.sv"
`include "svc_rv_pipe_data.sv"
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
  // Computed input values
  //
  logic [XLEN-1:0] pc_wb;
  logic            ebreak_wb;

  assign pc_wb     = pc_plus4_wb - XLEN'(32'd4);
  assign ebreak_wb = (instr_wb == I_EBREAK);

  //
  // Pipeline control
  //
  logic pipe_advance;
  logic pipe_flush;
  logic pipe_bubble;

  svc_rv_pipe_ctrl pipe_ctrl (
      .clk      (clk),
      .rst_n    (rst_n),
      .valid_i  (s_valid),
      .valid_o  (m_valid),
      .ready_i  (m_ready),
      .flush_i  (1'b0),
      .bubble_i (1'b0),
      .advance_o(pipe_advance),
      .flush_o  (pipe_flush),
      .bubble_o (pipe_bubble)
  );

  assign s_ready = !m_valid || m_ready;

  //
  // Pipeline data register
  //
  localparam int PIPE_WIDTH = 32 + 4 * XLEN + 1 + 2 + 1 + 1;

  svc_rv_pipe_data #(
      .WIDTH(PIPE_WIDTH)
  ) pipe_data_inst (
      .clk(clk),
      .rst_n(rst_n),
      .advance(pipe_advance),
      .flush(pipe_flush),
      .bubble(pipe_bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(s_ready),
`endif
      .data_i({
        instr_wb,
        pc_wb,
        rs1_data_wb,
        rs2_data_wb,
        rd_data_wb,
        trap_wb,
        trap_code_wb,
        reg_write_wb,
        ebreak_wb
      }),
      .data_o({
        instr_ret,
        pc_ret,
        rs1_data_ret,
        rs2_data_ret,
        rd_data_ret,
        trap_ret,
        trap_code_ret,
        reg_write_ret,
        ebreak_ret
      })
  );

  //
  // RVFI interface
  //
`ifdef RISCV_FORMAL
  localparam int RVFI_WIDTH = 1 + 4 * XLEN + 4 + 4;

  svc_rv_pipe_data #(
      .WIDTH(RVFI_WIDTH)
  ) pipe_rvfi (
      .clk(clk),
      .rst_n(rst_n),
      .advance(pipe_advance),
      .flush(pipe_flush),
      .bubble(pipe_bubble),
`ifdef FORMAL
      .s_valid(s_valid),
      .s_ready(s_ready),
`endif
      .data_i({
        f_mem_write_wb,
        f_dmem_waddr_wb,
        f_dmem_raddr_wb,
        f_dmem_wdata_wb,
        f_dmem_wstrb_wb,
        f_dmem_rdata_wb,
        f_dmem_rstrb_wb
      }),
      .data_o({
        f_mem_write_ret,
        f_dmem_waddr_ret,
        f_dmem_raddr_ret,
        f_dmem_wdata_ret,
        f_dmem_wstrb_ret,
        f_dmem_rdata_ret,
        f_dmem_rstrb_ret
      })
  );
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

  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // res_src_wb must be valid (0-5 for 6-way mux)
      `FASSUME(a_res_src_valid, res_src_wb < 3'd6);

      // When backpressured, raw inputs must be stable
      if ($past(s_valid && !s_ready)) begin
        `FASSUME(a_res_src_stable, res_src_wb == $past(res_src_wb));
        `FASSUME(a_instr_stable, instr_wb == $past(instr_wb));
        `FASSUME(a_alu_result_stable, alu_result_wb == $past(alu_result_wb));
        `FASSUME(a_ld_data_stable, ld_data_wb == $past(ld_data_wb));
        `FASSUME(a_pc_plus4_stable, pc_plus4_wb == $past(pc_plus4_wb));
        `FASSUME(a_jb_target_stable, jb_target_wb == $past(jb_target_wb));
        `FASSUME(a_csr_rdata_stable, csr_rdata_wb == $past(csr_rdata_wb));
        `FASSUME(a_m_result_stable, m_result_wb == $past(m_result_wb));
        `FASSUME(a_funct3_stable, funct3_wb == $past(funct3_wb));
        `FASSUME(a_rs1_data_stable, rs1_data_wb == $past(rs1_data_wb));
        `FASSUME(a_rs2_data_stable, rs2_data_wb == $past(rs2_data_wb));
        `FASSUME(a_product_64_stable, product_64_wb == $past(product_64_wb));
        `FASSUME(a_trap_stable, trap_wb == $past(trap_wb));
        `FASSUME(a_trap_code_stable, trap_code_wb == $past(trap_code_wb));
        `FASSUME(a_reg_write_stable, reg_write_wb == $past(reg_write_wb));
        `FASSUME(a_s_valid_stable, s_valid == $past(s_valid));
      end
    end
  end

  // Cover properties
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      // Cover back-to-back valid transfers
      `FCOVER(c_back_to_back, $past(m_valid && m_ready) && m_valid);

      // Cover halt conditions in retiring instruction
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
