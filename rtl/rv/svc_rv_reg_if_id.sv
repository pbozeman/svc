`ifndef SVC_RV_REG_IF_ID_SV
`define SVC_RV_REG_IF_ID_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V pipeline register: IF to ID
//
// This register stage separates instruction fetch from instruction decode,
// enabling pipelined execution. It captures the instruction, PC, and PC+4
// from the fetch stage and presents them to the decode stage on the next cycle.
//
// When IF_ID_REG=0, signals are passed through combinationally instead
// of being registered, effectively disabling the pipeline stage.
//
module svc_rv_reg_if_id #(
    parameter int XLEN      = 32,
    parameter int IF_ID_REG = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic stall,

    //
    // IF stage inputs
    //
    input logic [    31:0] instr_if,
    input logic [XLEN-1:0] pc_if,
    input logic [XLEN-1:0] pc_plus4_if,

    //
    // ID stage outputs
    //
    output logic [    31:0] instr_id,
    output logic [XLEN-1:0] pc_id,
    output logic [XLEN-1:0] pc_plus4_id
);
  `include "svc_rv_defs.svh"

  if (IF_ID_REG != 0) begin : g_registered
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        instr_id    <= '0;
        pc_id       <= '0;
        pc_plus4_id <= '0;
      end else if (!stall) begin
        instr_id    <= instr_if;
        pc_id       <= pc_if;
        pc_plus4_id <= pc_plus4_if;
      end
    end
  end else begin : g_passthrough
    assign instr_id    = instr_if;
    assign pc_id       = pc_if;
    assign pc_plus4_id = pc_plus4_if;

    `SVC_UNUSED({clk, rst_n, stall});
  end

endmodule

`endif
