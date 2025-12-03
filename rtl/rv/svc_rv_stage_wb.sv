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
    parameter int XLEN
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

    //
    // Ready/valid interface from MEM stage
    //
    input  logic s_valid,
    output logic s_ready,

    //
    // Output to register file in ID stage
    //
    output logic [XLEN-1:0] rd_data_wb,

    //
    // Halt signals
    //
    output logic ebreak,
    output logic trap,
    output logic retired
);
  logic halted;
  logic halted_ebreak;
  logic halted_trap;

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
  // Retire on handshake
  //
  assign retired = s_valid && s_ready;

  //
  // Halt condition detection
  //
  logic is_ebreak;
  logic is_trap;

  assign is_ebreak = (instr_wb == I_EBREAK);
  assign is_trap   = trap_wb;

  //
  // Ready/valid interface
  //
  // s_ready is high until we enter halted state. This allows the ebreak/trap
  // instruction to complete its handshake before stopping the pipeline.
  //
  assign s_ready   = !halted;

  //
  // Halted state
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      halted        <= 1'b0;
      halted_ebreak <= 1'b0;
      halted_trap   <= 1'b0;
    end else if (retired && (is_ebreak || is_trap)) begin
      halted        <= 1'b1;
      halted_ebreak <= is_ebreak;
      halted_trap   <= is_trap;
    end
  end

  assign ebreak = (retired && is_ebreak) || halted_ebreak;
  assign trap   = (retired && trap_wb) || halted_trap;

endmodule

`endif
