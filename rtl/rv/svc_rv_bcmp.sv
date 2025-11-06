`ifndef SVC_RV_BCMP_SV
`define SVC_RV_BCMP_SV

`include "svc.sv"

//
// RISC-V Branch Comparator
//
// Dedicated comparison unit for branch instructions. Compares two operands
// and produces a branch taken signal based on the funct3 field.
//
// Supports all six RISC-V branch types:
// - BEQ/BNE: Equality comparison
// - BLT/BGE: Signed less-than comparison
// - BLTU/BGEU: Unsigned less-than comparison
//
// All comparison logic is performed in the EX stage.
//
module svc_rv_bcmp #(
    parameter int XLEN = 32
) (
    //
    // EX stage inputs
    //
    input logic [XLEN-1:0] a_ex,
    input logic [XLEN-1:0] b_ex,
    input logic [     2:0] funct3,

    //
    // EX stage output
    //
    output logic branch_taken_ex
);
  `include "svc_rv_defs.svh"

  //
  // EX stage: Full comparisons
  //
  logic rs_eq;
  logic rs_lt_s;
  logic rs_lt_u;

  //
  // Equality comparison
  //
  assign rs_eq   = (a_ex == b_ex);

  //
  // Unsigned less-than comparison
  //
  assign rs_lt_u = (a_ex < b_ex);

  //
  // Signed less-than comparison
  //
  assign rs_lt_s = ($signed(a_ex) < $signed(b_ex));

  //
  // Branch decision based on funct3
  //
  always_comb begin
    case (funct3)
      FUNCT3_BEQ:  branch_taken_ex = rs_eq;
      FUNCT3_BNE:  branch_taken_ex = ~rs_eq;
      FUNCT3_BLT:  branch_taken_ex = rs_lt_s;
      FUNCT3_BGE:  branch_taken_ex = ~rs_lt_s;
      FUNCT3_BLTU: branch_taken_ex = rs_lt_u;
      FUNCT3_BGEU: branch_taken_ex = ~rs_lt_u;
      default:     branch_taken_ex = 1'b0;
    endcase
  end

endmodule

`endif
