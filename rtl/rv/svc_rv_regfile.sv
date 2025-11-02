`ifndef SVC_RV_REGFILE_SV
`define SVC_RV_REGFILE_SV

`include "svc.sv"

// RISC-V Register File (x0-x31)
//
// Implements 32 registers with:
// - x0 hardwired to zero
// - Two combinational read ports (zero latency)
// - One synchronous write port
// - Optional internal forwarding for pipelined designs

module svc_rv_regfile #(
    parameter int XLEN             = 32,
    parameter int INTERNAL_FORWARD = 1
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
  logic [XLEN-1:0] regs         [32];
  logic [XLEN-1:0] wdata;
  logic [XLEN-1:0] rs1_data_raw;
  logic [XLEN-1:0] rs2_data_raw;

  assign rs1_data_raw = regs[rs1_addr];
  assign rs2_data_raw = regs[rs2_addr];

  assign wdata        = (rd_addr == 0) ? 0 : rd_data;

  //
  // Internal forwarding (only for pipelined designs)
  //
  // In pipelined designs, internal forwarding eliminates WB-stage hazards by
  // forwarding write data directly to read ports when addresses match.
  // In single-cycle designs, this creates a combinational loop, so it must
  // be disabled.
  //
  if (INTERNAL_FORWARD != 0) begin : g_forward
    assign rs1_data = ((rd_en && (rd_addr != 0) && (rd_addr == rs1_addr)) ?
                       wdata : rs1_data_raw);
    assign rs2_data = ((rd_en && (rd_addr != 0) && (rd_addr == rs2_addr)) ?
                       wdata : rs2_data_raw);
  end else begin : g_no_forward
    assign rs1_data = rs1_data_raw;
    assign rs2_data = rs2_data_raw;
  end

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

