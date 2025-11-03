`ifndef SVC_RV_REG_PC_IF_SV
`define SVC_RV_REG_PC_IF_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V pipeline register: PC delay for registered memories
//
// This register delays PC values by one cycle to match the latency of
// registered memories (BRAM). When using BRAM with 1-cycle read latency,
// the instruction arrives one cycle after the PC that requested it. This
// register delays PC/PC+4 to keep them synchronized with the instruction.
//
// When PC_DELAY=0, signals are passed through combinationally for
// combinational memories (SRAM).
//
module svc_rv_reg_pc_if #(
    parameter int XLEN     = 32,
    parameter int PC_DELAY = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // Hazard control
    //
    input logic stall,

    //
    // PC inputs
    //
    input logic [XLEN-1:0] pc_in,
    input logic [XLEN-1:0] pc_plus4_in,

    //
    // PC outputs (delayed for registered memories)
    //
    output logic [XLEN-1:0] pc_out,
    output logic [XLEN-1:0] pc_plus4_out
);

  if (PC_DELAY != 0) begin : g_registered
    //
    // PC values with reset
    //
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        pc_out       <= '0;
        pc_plus4_out <= 4;
      end else if (!stall) begin
        pc_out       <= pc_in;
        pc_plus4_out <= pc_plus4_in;
      end
    end
  end else begin : g_passthrough
    assign pc_out       = pc_in;
    assign pc_plus4_out = pc_plus4_in;

    `SVC_UNUSED({clk, rst_n, stall});
  end

endmodule

`endif
