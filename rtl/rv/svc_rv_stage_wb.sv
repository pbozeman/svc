`ifndef SVC_RV_STAGE_WB_SV
`define SVC_RV_STAGE_WB_SV

`include "svc.sv"
`include "svc_muxn.sv"
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
    input logic rst_n,

    //
    // From MEM stage
    //
    input logic [     2:0] res_src_wb,
    input logic [    31:0] instr_wb,
    input logic [XLEN-1:0] alu_result_wb,
    input logic [XLEN-1:0] dmem_rdata_ext_wb,
    input logic [XLEN-1:0] pc_plus4_wb,
    input logic [XLEN-1:0] jb_target_wb,
    input logic [XLEN-1:0] csr_rdata_wb,
    input logic [XLEN-1:0] m_result_wb,

    //
    // Output to register file in ID stage
    //
    output logic [XLEN-1:0] rd_data_wb,

    //
    // EBREAK signal
    //
    output logic ebreak
);

  `include "svc_rv_defs.svh"

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
        m_result_wb,
        csr_rdata_wb,
        jb_target_wb,
        pc_plus4_wb,
        dmem_rdata_ext_wb,
        alu_result_wb
      }),
      .out(rd_data_wb)
  );

  //
  // EBREAK detection
  //
  assign ebreak = (rst_n && instr_wb == I_EBREAK);

endmodule

`endif
