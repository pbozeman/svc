`ifndef SVC_RV_REG_EX_MEM_SV
`define SVC_RV_REG_EX_MEM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V pipeline register: EX to MEM
//
// This register stage separates execution from memory access,
// enabling pipelined execution. It captures control signals, ALU results,
// store data, and other execution results and presents them to the
// memory stage on the next cycle.
//
// When EX_MEM_REG=0, signals are passed through combinationally instead
// of being registered, effectively disabling the pipeline stage.
//
module svc_rv_reg_ex_mem #(
    parameter int XLEN       = 32,
    parameter int EX_MEM_REG = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // EX stage inputs (control signals)
    //
    input logic       reg_write_ex,
    input logic       mem_write_ex,
    input logic [2:0] res_src_ex,

    //
    // EX stage inputs (data)
    //
    input logic [    31:0] instr_ex,
    input logic [     4:0] rd_ex,
    input logic [     2:0] funct3_ex,
    input logic [XLEN-1:0] alu_result_ex,
    input logic [XLEN-1:0] rs2_data_ex,
    input logic [XLEN-1:0] pc_plus4_ex,
    input logic [XLEN-1:0] jb_target_ex,
    input logic [XLEN-1:0] csr_rdata_ex,

    //
    // MEM stage outputs (control signals)
    //
    output logic       reg_write_mem,
    output logic       mem_write_mem,
    output logic [2:0] res_src_mem,

    //
    // MEM stage outputs (data)
    //
    output logic [    31:0] instr_mem,
    output logic [     4:0] rd_mem,
    output logic [     2:0] funct3_mem,
    output logic [XLEN-1:0] alu_result_mem,
    output logic [XLEN-1:0] rs2_data_mem,
    output logic [XLEN-1:0] pc_plus4_mem,
    output logic [XLEN-1:0] jb_target_mem,
    output logic [XLEN-1:0] csr_rdata_mem
);

  if (EX_MEM_REG != 0) begin : g_registered
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        reg_write_mem  <= '0;
        mem_write_mem  <= '0;
        res_src_mem    <= '0;
        instr_mem      <= '0;
        rd_mem         <= '0;
        funct3_mem     <= '0;
        alu_result_mem <= '0;
        rs2_data_mem   <= '0;
        pc_plus4_mem   <= '0;
        jb_target_mem  <= '0;
        csr_rdata_mem  <= '0;
      end else begin
        reg_write_mem  <= reg_write_ex;
        mem_write_mem  <= mem_write_ex;
        res_src_mem    <= res_src_ex;
        instr_mem      <= instr_ex;
        rd_mem         <= rd_ex;
        funct3_mem     <= funct3_ex;
        alu_result_mem <= alu_result_ex;
        rs2_data_mem   <= rs2_data_ex;
        pc_plus4_mem   <= pc_plus4_ex;
        jb_target_mem  <= jb_target_ex;
        csr_rdata_mem  <= csr_rdata_ex;
      end
    end
  end else begin : g_passthrough
    assign reg_write_mem  = reg_write_ex;
    assign mem_write_mem  = mem_write_ex;
    assign res_src_mem    = res_src_ex;
    assign instr_mem      = instr_ex;
    assign rd_mem         = rd_ex;
    assign funct3_mem     = funct3_ex;
    assign alu_result_mem = alu_result_ex;
    assign rs2_data_mem   = rs2_data_ex;
    assign pc_plus4_mem   = pc_plus4_ex;
    assign jb_target_mem  = jb_target_ex;
    assign csr_rdata_mem  = csr_rdata_ex;

    `SVC_UNUSED({clk, rst_n});
  end

endmodule

`endif
