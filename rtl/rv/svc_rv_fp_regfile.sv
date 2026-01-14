`ifndef SVC_RV_FP_REGFILE_SV
`define SVC_RV_FP_REGFILE_SV

`include "svc.sv"

//
// RISC-V Floating-Point Register File (f0-f31)
//
// Implements 32 FP registers with:
// - All registers writable (unlike x0, f0 is NOT hardwired)
// - Three combinational read ports (for FMA rs3 operand)
// - One synchronous write port
// - Optional internal forwarding for pipelined designs
//
module svc_rv_fp_regfile #(
    parameter int XLEN        = 32,
    parameter int FWD_REGFILE = 0
) (
    input logic clk,

    // FP register source 1
    input  logic [     4:0] fp_rs1_addr,
    output logic [XLEN-1:0] fp_rs1_data,

    // FP register source 2
    input  logic [     4:0] fp_rs2_addr,
    output logic [XLEN-1:0] fp_rs2_data,

    // FP register source 3 (for FMA instructions)
    input  logic [     4:0] fp_rs3_addr,
    output logic [XLEN-1:0] fp_rs3_data,

    // FP register destination (with en)
    input logic            fp_rd_en,
    input logic [     4:0] fp_rd_addr,
    input logic [XLEN-1:0] fp_rd_data
);
  logic [XLEN-1:0] regs            [32];

  logic [XLEN-1:0] fp_rs1_data_raw;
  logic [XLEN-1:0] fp_rs2_data_raw;
  logic [XLEN-1:0] fp_rs3_data_raw;

  //
  // Read ports (no hardwired zero - all 32 registers readable)
  //
  assign fp_rs1_data_raw = regs[fp_rs1_addr];
  assign fp_rs2_data_raw = regs[fp_rs2_addr];
  assign fp_rs3_data_raw = regs[fp_rs3_addr];

  //
  // Internal forwarding (only for pipelined designs)
  //
  // In pipelined designs, internal forwarding eliminates WB-stage hazards by
  // forwarding write data directly to read ports when addresses match.
  // In single-cycle designs, this creates a combinational loop, so it must
  // be disabled.
  //
  if (FWD_REGFILE != 0) begin : g_forward
    assign fp_rs1_data = ((fp_rd_en && (fp_rd_addr == fp_rs1_addr)) ?
                          fp_rd_data : fp_rs1_data_raw);

    assign fp_rs2_data = ((fp_rd_en && (fp_rd_addr == fp_rs2_addr)) ?
                          fp_rd_data : fp_rs2_data_raw);

    assign fp_rs3_data = ((fp_rd_en && (fp_rd_addr == fp_rs3_addr)) ?
                          fp_rd_data : fp_rs3_data_raw);
  end else begin : g_no_forward
    assign fp_rs1_data = fp_rs1_data_raw;
    assign fp_rs2_data = fp_rs2_data_raw;
    assign fp_rs3_data = fp_rs3_data_raw;
  end

  always_ff @(posedge clk) begin
    if (fp_rd_en) begin
      regs[fp_rd_addr] <= fp_rd_data;
    end
  end

endmodule

`endif
