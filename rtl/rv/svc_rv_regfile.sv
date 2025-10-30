`ifndef SVC_RV_REGFILE_SV
`define SVC_RV_REGFILE_SV

`include "svc.sv"

// RISC-V Register File (x0-x31)
//
// Implements 32 registers with:
// - x0 hardwired to zero
// - Two combinational read ports (zero latency)
// - One synchronous write port

module svc_rv_regfile #(
    parameter int XLEN = 32
) (
    input logic clk,
    input logic rst_n,

    // register source 1
    input  logic [     4:0] rs1_addr,
    output logic [XLEN-1:0] rs1_data,

    // register source 2
    input  logic [     4:0] rs2_addr,
    output logic [XLEN-1:0] rs2_data,

    // register destination (with en)
    input logic            rd_en,
    input logic [     4:0] rd_addr,
    input logic [XLEN-1:0] rd_data
);
  logic [XLEN-1:0] regs  [32];
  logic [XLEN-1:0] wdata;

  assign rs1_data = regs[rs1_addr];
  assign rs2_data = regs[rs2_addr];

  assign wdata    = (rd_addr == 0) ? 0 : rd_data;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
`ifndef SYNTHESIS
      for (int i = 0; i < 32; i++) begin
        regs[i] <= '0;
      end
`endif
    end else if (rd_en) begin
      regs[rd_addr] <= wdata;
    end
  end

endmodule

`endif

