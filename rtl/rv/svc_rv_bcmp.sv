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
// The module uses direct comparison rather than subtraction to avoid
// complexity in extracting unsigned borrow flags.
//
module svc_rv_bcmp #(
    parameter int XLEN = 32
) (
    input logic [XLEN-1:0] a,
    input logic [XLEN-1:0] b,
    input logic [     2:0] funct3,

    output logic branch_taken
);
  `include "svc_rv_defs.svh"

  logic eq;
  logic lt_signed;
  logic lt_unsigned;

  //
  // Comparison operations
  //
  assign eq          = (a == b);
  assign lt_signed   = $signed(a) < $signed(b);
  assign lt_unsigned = (a < b);

  //
  // Branch decision based on funct3
  //
  // RISC-V funct3 encoding:
  //   BEQ:  000 - branch if equal
  //   BNE:  001 - branch if not equal
  //   BLT:  100 - branch if less than (signed)
  //   BGE:  101 - branch if greater/equal (signed)
  //   BLTU: 110 - branch if less than (unsigned)
  //   BGEU: 111 - branch if greater/equal (unsigned)
  //
  always_comb begin
    case (funct3)
      FUNCT3_BEQ:  branch_taken = eq;
      FUNCT3_BNE:  branch_taken = ~eq;
      FUNCT3_BLT:  branch_taken = lt_signed;
      FUNCT3_BGE:  branch_taken = ~lt_signed;
      FUNCT3_BLTU: branch_taken = lt_unsigned;
      FUNCT3_BGEU: branch_taken = ~lt_unsigned;
      default:     branch_taken = 1'b0;
    endcase
  end

endmodule

`endif
