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
    parameter int XLEN,
    parameter int FWD_REGFILE
) (
    input logic clk,

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
  logic [XLEN-1:0] regs   [32];

  // Debug: expose ra (x1) and sp (x2) for ILA
  // verilator lint_off UNUSEDSIGNAL
  logic [XLEN-1:0] dbg_ra;
  logic [XLEN-1:0] dbg_sp;
  // verilator lint_on UNUSEDSIGNAL
  assign dbg_ra = regs[1];
  assign dbg_sp = regs[2];

  logic [XLEN-1:0] rs1_data_raw;
  logic [XLEN-1:0] rs2_data_raw;

  //
  // Internal forwarding (only for pipelined designs)
  //
  // In pipelined designs, internal forwarding eliminates WB-stage hazards by
  // forwarding write data directly to read ports when addresses match.
  // In single-cycle designs, this creates a combinational loop, so it must
  // be disabled.
  //

  assign rs1_data_raw = (rs1_addr == 5'd0) ? '0 : regs[rs1_addr];
  assign rs2_data_raw = (rs2_addr == 5'd0) ? '0 : regs[rs2_addr];

  if (FWD_REGFILE != 0) begin : g_forward
    assign rs1_data = ((rd_en && (rd_addr != 5'd0) && (rd_addr == rs1_addr)) ?
                       rd_data : rs1_data_raw);

    assign rs2_data = ((rd_en && (rd_addr != 5'd0) && (rd_addr == rs2_addr)) ?
                       rd_data : rs2_data_raw);
  end else begin : g_no_forward
    assign rs1_data = rs1_data_raw;
    assign rs2_data = rs2_data_raw;
  end

  always_ff @(posedge clk) begin
    // We don't need the addr 0 check here because we set to 0 on read.
    if (rd_en) begin
      regs[rd_addr] <= rd_data;
    end
  end

endmodule

`endif
