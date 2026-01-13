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
    input  logic [     4:0] frs1_addr,
    output logic [XLEN-1:0] frs1_data,

    // FP register source 2
    input  logic [     4:0] frs2_addr,
    output logic [XLEN-1:0] frs2_data,

    // FP register source 3 (for FMA instructions)
    input  logic [     4:0] frs3_addr,
    output logic [XLEN-1:0] frs3_data,

    // FP register destination (with en)
    input logic            frd_en,
    input logic [     4:0] frd_addr,
    input logic [XLEN-1:0] frd_data
);
  logic [XLEN-1:0] regs          [32];

  logic [XLEN-1:0] frs1_data_raw;
  logic [XLEN-1:0] frs2_data_raw;
  logic [XLEN-1:0] frs3_data_raw;

  //
  // Read ports (no hardwired zero - all 32 registers readable)
  //
  assign frs1_data_raw = regs[frs1_addr];
  assign frs2_data_raw = regs[frs2_addr];
  assign frs3_data_raw = regs[frs3_addr];

  //
  // Internal forwarding (only for pipelined designs)
  //
  // In pipelined designs, internal forwarding eliminates WB-stage hazards by
  // forwarding write data directly to read ports when addresses match.
  // In single-cycle designs, this creates a combinational loop, so it must
  // be disabled.
  //
  if (FWD_REGFILE != 0) begin : g_forward
    assign frs1_data = ((frd_en && (frd_addr == frs1_addr)) ? frd_data :
                        frs1_data_raw);

    assign frs2_data = ((frd_en && (frd_addr == frs2_addr)) ? frd_data :
                        frs2_data_raw);

    assign frs3_data = ((frd_en && (frd_addr == frs3_addr)) ? frd_data :
                        frs3_data_raw);
  end else begin : g_no_forward
    assign frs1_data = frs1_data_raw;
    assign frs2_data = frs2_data_raw;
    assign frs3_data = frs3_data_raw;
  end

  always_ff @(posedge clk) begin
    if (frd_en) begin
      regs[frd_addr] <= frd_data;
    end
  end

endmodule

`endif
