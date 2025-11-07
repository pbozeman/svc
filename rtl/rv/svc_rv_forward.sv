`ifndef SVC_RV_FORWARD_SV
`define SVC_RV_FORWARD_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V data forwarding unit
//
// Forwards ALU results from later pipeline stages back to EX stage to resolve
// data hazards without stalling.
//
// Two types of forwarding:
// - EX hazard (MEM→EX): Forward from MEM stage when it has the needed value
// - MEM hazard (WB→EX): Forward from WB stage when MEM doesn't have it
//
// Priority: MEM > WB > regfile (MEM is more recent)
//
// Cannot forward:
// - Load results in MEM stage for BRAM (data not ready until WB)
// - CSR results in MEM stage (data not ready until WB)
// - Load results for SRAM are available in MEM stage and CAN be forwarded
//
module svc_rv_forward #(
    parameter int XLEN     = 32,
    parameter int FWD      = 0,
    parameter int MEM_TYPE = 0
) (
    //
    // EX stage inputs (consumers)
    //
    input logic [     4:0] rs1_ex,
    input logic [     4:0] rs2_ex,
    input logic [XLEN-1:0] rs1_data_ex,
    input logic [XLEN-1:0] rs2_data_ex,

    //
    // MEM stage inputs (producer)
    //
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic            is_load_mem,
    input logic            is_csr_mem,
    input logic            is_zmmul_mem,
    input logic [XLEN-1:0] alu_result_mem,
    input logic [XLEN-1:0] zmmul_result_mem,
    input logic [XLEN-1:0] load_data_mem,

    //
    // WB stage inputs (producer)
    //
    input logic [     4:0] rd_wb,
    input logic            reg_write_wb,
    input logic [XLEN-1:0] rd_data,

    //
    // Forwarded outputs
    //
    output logic [XLEN-1:0] rs1_fwd_ex,
    output logic [XLEN-1:0] rs2_fwd_ex
);

  `include "svc_rv_defs.svh"

  if (FWD != 0) begin : g_forwarding
    //
    // MEM→EX ALU forwarding (common to both SRAM and BRAM)
    //
    // Forward ALU results from MEM stage (not loads or CSRs)
    //
    logic mem_to_ex_fwd_alu_a;
    logic mem_to_ex_fwd_alu_b;

    always_comb begin
      mem_to_ex_fwd_alu_a = 1'b0;
      mem_to_ex_fwd_alu_b = 1'b0;

      if (reg_write_mem && rd_mem != 5'd0 && !is_load_mem && !is_csr_mem &&
          !is_zmmul_mem) begin
        mem_to_ex_fwd_alu_a = (rd_mem == rs1_ex);
        mem_to_ex_fwd_alu_b = (rd_mem == rs2_ex);
      end
    end

    //
    // MEM→EX Zmmul forwarding (common to both SRAM and BRAM)
    //
    // Forward Zmmul results from MEM stage
    //
    logic mem_to_ex_fwd_zmmul_a;
    logic mem_to_ex_fwd_zmmul_b;

    always_comb begin
      mem_to_ex_fwd_zmmul_a = 1'b0;
      mem_to_ex_fwd_zmmul_b = 1'b0;

      if (reg_write_mem && rd_mem != 5'd0 && is_zmmul_mem) begin
        mem_to_ex_fwd_zmmul_a = (rd_mem == rs1_ex);
        mem_to_ex_fwd_zmmul_b = (rd_mem == rs2_ex);
      end
    end

    //
    // WB→EX forwarding (common to both SRAM and BRAM)
    //
    // Forward from WB stage when MEM doesn't have the value
    // Handles load results after stall, CSR reads, and older hazards
    //
    logic wb_to_ex_fwd_a;
    logic wb_to_ex_fwd_b;

    always_comb begin
      wb_to_ex_fwd_a = 1'b0;
      wb_to_ex_fwd_b = 1'b0;

      if (reg_write_wb && rd_wb != 5'd0) begin
        wb_to_ex_fwd_a = (rd_wb == rs1_ex);
        wb_to_ex_fwd_b = (rd_wb == rs2_ex);
      end
    end

    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_sram_load_fwd
      //
      // SRAM: Load data is ready in MEM stage, can forward
      //
      logic mem_to_ex_fwd_load_a;
      logic mem_to_ex_fwd_load_b;

      //
      // MEM→EX load forwarding (SRAM only)
      //
      always_comb begin
        mem_to_ex_fwd_load_a = 1'b0;
        mem_to_ex_fwd_load_b = 1'b0;

        if (reg_write_mem && rd_mem != 5'd0 && is_load_mem) begin
          mem_to_ex_fwd_load_a = (rd_mem == rs1_ex);
          mem_to_ex_fwd_load_b = (rd_mem == rs2_ex);
        end
      end

      //
      // Forwarding muxes with priority: MEM load > MEM Zmmul > MEM ALU > WB > regfile
      //
      assign rs1_fwd_ex = (
          mem_to_ex_fwd_load_a ? load_data_mem :
              mem_to_ex_fwd_zmmul_a ? zmmul_result_mem : mem_to_ex_fwd_alu_a ?
              alu_result_mem : wb_to_ex_fwd_a ? rd_data : rs1_data_ex);

      assign rs2_fwd_ex = (
          mem_to_ex_fwd_load_b ? load_data_mem :
              mem_to_ex_fwd_zmmul_b ? zmmul_result_mem : mem_to_ex_fwd_alu_b ?
              alu_result_mem : wb_to_ex_fwd_b ? rd_data : rs2_data_ex);

    end else begin : g_bram_no_load_fwd
      //
      // BRAM: Load data not ready in MEM stage, cannot forward
      //
      // Forwarding muxes with priority: MEM Zmmul > MEM ALU > WB > regfile
      //
      assign rs1_fwd_ex = (mem_to_ex_fwd_zmmul_a ? zmmul_result_mem :
                           mem_to_ex_fwd_alu_a ? alu_result_mem :
                           wb_to_ex_fwd_a ? rd_data : rs1_data_ex);

      assign rs2_fwd_ex = (mem_to_ex_fwd_zmmul_b ? zmmul_result_mem :
                           mem_to_ex_fwd_alu_b ? alu_result_mem :
                           wb_to_ex_fwd_b ? rd_data : rs2_data_ex);

      `SVC_UNUSED({load_data_mem});
    end

  end else begin : g_no_forwarding
    //
    // No forwarding, just pass through
    //
    assign rs1_fwd_ex = rs1_data_ex;
    assign rs2_fwd_ex = rs2_data_ex;

    // verilog_format: off
    `SVC_UNUSED({rs1_ex, rs2_ex, rd_mem, reg_write_mem, is_load_mem,
                 is_csr_mem, is_zmmul_mem, alu_result_mem, zmmul_result_mem,
                 load_data_mem, rd_wb, reg_write_wb, rd_data, MEM_TYPE});
    // verilog_format: on
  end

endmodule

`endif
