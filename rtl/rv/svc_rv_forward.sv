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
// - Load results in MEM stage (data not ready until WB)
// - CSR results in MEM stage (data not ready until WB)
//
module svc_rv_forward #(
    parameter int XLEN = 32,
    parameter int FWD  = 0
) (
    //
    // EX stage inputs (consumers)
    //
    input logic [     4:0] rs1_ex,
    input logic [     4:0] rs2_ex,
    input logic            rs1_used_ex,
    input logic            rs2_used_ex,
    input logic [XLEN-1:0] rs1_data_ex,
    input logic [XLEN-1:0] rs2_data_ex,

    //
    // MEM stage inputs (producer)
    //
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic            is_load_mem,
    input logic            is_csr_mem,
    input logic [XLEN-1:0] alu_result_mem,

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

  if (FWD != 0) begin : g_forwarding
    //
    // EX Hazard: Forward from MEM stage
    //
    // When instruction in MEM stage writes to a register that
    // instruction in EX stage reads, forward from MEM.
    //
    logic mem_to_ex_fwd_a;
    logic mem_to_ex_fwd_b;

    //
    // MEM→EX forwarding: Forward ALU result from MEM stage
    //
    // Don't forward if producer is a load or CSR (data not ready)
    //
    assign mem_to_ex_fwd_a = (reg_write_mem && (rd_mem != 5'd0) &&
                              (rd_mem == rs1_ex) && rs1_used_ex &&
                              !is_load_mem && !is_csr_mem);

    assign mem_to_ex_fwd_b = (reg_write_mem && (rd_mem != 5'd0) &&
                              (rd_mem == rs2_ex) && rs2_used_ex &&
                              !is_load_mem && !is_csr_mem);

    //
    // MEM Hazard: Forward from WB stage
    //
    // When instruction in WB stage writes to a register that
    // instruction in EX stage reads, forward from WB.
    //
    // This handles:
    // - Cycle after load-use stall (load result now in WB)
    // - CSR reads (only available in WB)
    // - Cases where MEM stage doesn't have the value
    //
    logic wb_to_ex_fwd_a;
    logic wb_to_ex_fwd_b;

    assign wb_to_ex_fwd_a = (reg_write_wb && (rd_wb != 5'd0) &&
                             (rd_wb == rs1_ex) && rs1_used_ex);

    assign wb_to_ex_fwd_b = (reg_write_wb && (rd_wb != 5'd0) &&
                             (rd_wb == rs2_ex) && rs2_used_ex);

    //
    // Forwarding muxes with priority: MEM > WB > regfile
    //
    // MEM stage is more recent (closer to EX) so it takes priority
    //
    assign rs1_fwd_ex = (mem_to_ex_fwd_a ? alu_result_mem :
                         wb_to_ex_fwd_a ? rd_data : rs1_data_ex);

    assign rs2_fwd_ex = (mem_to_ex_fwd_b ? alu_result_mem :
                         wb_to_ex_fwd_b ? rd_data : rs2_data_ex);

  end else begin : g_no_forwarding
    //
    // No forwarding, just pass through
    //
    assign rs1_fwd_ex = rs1_data_ex;
    assign rs2_fwd_ex = rs2_data_ex;

    // verilog_format: off
    `SVC_UNUSED({rs1_ex, rs2_ex, rs1_used_ex, rs2_used_ex, rd_mem,
                 reg_write_mem, is_load_mem, is_csr_mem,
                 alu_result_mem, rd_wb, reg_write_wb, rd_data });
    // verilog_format: on
  end

endmodule

`endif
