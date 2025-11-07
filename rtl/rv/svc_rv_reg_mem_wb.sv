`ifndef SVC_RV_REG_MEM_WB_SV
`define SVC_RV_REG_MEM_WB_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V pipeline register: MEM to WB
//
// This register stage separates memory access from writeback,
// enabling pipelined execution. It captures control signals and
// data results from the memory stage and presents them to the
// writeback stage on the next cycle.
//
// When PIPELINED=0, signals are passed through combinationally instead
// of being registered, effectively disabling the pipeline stage.
//
module svc_rv_reg_mem_wb #(
    parameter int XLEN      = 32,
    parameter int PIPELINED = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // MEM stage inputs (control signals)
    //
    input logic       reg_write_mem,
    input logic [2:0] res_src_mem,
    input logic [2:0] funct3_mem,

    //
    // MEM stage inputs (data)
    //
    input logic [    31:0] instr_mem,
    input logic [     4:0] rd_mem,
    input logic [XLEN-1:0] alu_result_mem,
    input logic [XLEN-1:0] dmem_rdata_ext_mem,
    input logic [XLEN-1:0] pc_plus4_mem,
    input logic [XLEN-1:0] jb_target_mem,
    input logic [XLEN-1:0] csr_rdata_mem,
    input logic [XLEN-1:0] zmmul_result_mem,

    //
    // WB stage outputs (control signals)
    //
    output logic       reg_write_wb,
    output logic [2:0] res_src_wb,
    output logic [2:0] funct3_wb,

    //
    // WB stage outputs (data)
    //
    output logic [    31:0] instr_wb,
    output logic [     4:0] rd_wb,
    output logic [XLEN-1:0] alu_result_wb,
    output logic [XLEN-1:0] dmem_rdata_ext_wb,
    output logic [XLEN-1:0] pc_plus4_wb,
    output logic [XLEN-1:0] jb_target_wb,
    output logic [XLEN-1:0] csr_rdata_wb,
    output logic [XLEN-1:0] zmmul_result_wb
);

  if (PIPELINED != 0) begin : g_registered
    //
    // Control signals with reset
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        reg_write_wb <= '0;
        funct3_wb    <= '0;
      end else begin
        reg_write_wb <= reg_write_mem;
        funct3_wb    <= funct3_mem;
      end
    end

    //
    // Instruction with reset to NOP (ADDI x0, x0, 0)
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        instr_wb <= 32'h00000013;
      end else begin
        instr_wb <= instr_mem;
      end
    end

    //
    // Datapath signals without reset
    //
    always_ff @(posedge clk) begin
      res_src_wb        <= res_src_mem;
      rd_wb             <= rd_mem;
      alu_result_wb     <= alu_result_mem;
      dmem_rdata_ext_wb <= dmem_rdata_ext_mem;
      pc_plus4_wb       <= pc_plus4_mem;
      jb_target_wb      <= jb_target_mem;
      csr_rdata_wb      <= csr_rdata_mem;
      zmmul_result_wb   <= zmmul_result_mem;
    end
  end else begin : g_passthrough
    assign reg_write_wb      = reg_write_mem;
    assign res_src_wb        = res_src_mem;
    assign funct3_wb         = funct3_mem;
    assign instr_wb          = instr_mem;
    assign rd_wb             = rd_mem;
    assign alu_result_wb     = alu_result_mem;
    assign dmem_rdata_ext_wb = dmem_rdata_ext_mem;
    assign pc_plus4_wb       = pc_plus4_mem;
    assign jb_target_wb      = jb_target_mem;
    assign csr_rdata_wb      = csr_rdata_mem;
    assign zmmul_result_wb   = zmmul_result_mem;

    `SVC_UNUSED({clk, rst_n});
  end

endmodule

`endif
