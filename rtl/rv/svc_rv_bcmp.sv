`ifndef SVC_RV_BCMP_SV
`define SVC_RV_BCMP_SV

`include "svc.sv"
`include "svc_unused.sv"

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
// Two-stage comparison optimization:
// - ID stage: Computes partial comparison on lower 16 bits (outputs)
// - EX stage: Finishes using upper 16 bits + partial results (inputs)
//
// Splitting into 2 phases was a huge improvement in early testing on
// an hx8k, whereas this was consistently the critical path when all in EX.
//
module svc_rv_bcmp #(
    parameter int XLEN = 32
) (
    //
    // ID stage: compute partial comparisons on lower 16 bits
    //
    input  logic [XLEN-1:0] a_id,
    input  logic [XLEN-1:0] b_id,
    output logic            rs_eq_lo_id,
    output logic            rs_lt_u_lo_id,
    output logic            rs_lt_s_lo_id,
    output logic            rs_sign_a_id,
    output logic            rs_sign_b_id,

    //
    // EX stage: complete comparison using upper 16 bits + registered partials
    //
    input logic [XLEN-1:0] a_ex,
    input logic [XLEN-1:0] b_ex,
    input logic [     2:0] funct3,
    input logic            rs_eq_lo_ex,
    input logic            rs_lt_u_lo_ex,
    input logic            rs_lt_s_lo_ex,
    input logic            rs_sign_a_ex,
    input logic            rs_sign_b_ex,

    output logic branch_taken_ex
);
  `include "svc_rv_defs.svh"

  //
  // ID stage: Lower 16-bit partial comparisons and sign extraction
  //
  assign rs_eq_lo_id   = (a_id[15:0] == b_id[15:0]);
  assign rs_lt_u_lo_id = (a_id[15:0] < b_id[15:0]);
  assign rs_lt_s_lo_id = (a_id[14:0] < b_id[14:0]);
  assign rs_sign_a_id  = a_id[XLEN-1];
  assign rs_sign_b_id  = b_id[XLEN-1];

  //
  // EX stage: Upper 16-bit comparisons
  //
  logic rs_eq;
  logic rs_lt_s;
  logic rs_lt_u;

  logic rs_eq_hi;
  logic rs_lt_u_hi;
  logic rs_lt_s_hi;

  assign rs_eq_hi   = (a_ex[XLEN-1:16] == b_ex[XLEN-1:16]);
  assign rs_lt_u_hi = (a_ex[XLEN-1:16] < b_ex[XLEN-1:16]);

  //
  // For signed, compare upper 15 bits as magnitude
  //
  assign rs_lt_s_hi = (a_ex[XLEN-2:16] < b_ex[XLEN-2:16]);

  //
  // Combine with partial results from ID stage (now registered in EX stage)
  //
  // eq: both halves must be equal
  assign rs_eq      = rs_eq_hi & rs_eq_lo_ex;

  //
  // lt_unsigned: upper half less, OR upper half equal and lower half less
  //
  assign rs_lt_u    = rs_lt_u_hi | (rs_eq_hi & rs_lt_u_lo_ex);

  //
  // lt_signed: handle sign bits, then check magnitude
  // - If sign bits differ: negative < positive
  // - If sign bits same: compare magnitudes (upper 15 + lower 16 bits)
  //
  // Sign bits come from ID stage (registered in EX stage)
  //
  logic rs_mag_lt;

  //
  // Magnitude less than: upper bits less, OR upper bits equal and lower partial
  // says less
  //
  assign rs_mag_lt = rs_lt_s_hi | (rs_eq_hi & rs_lt_s_lo_ex);

  assign rs_lt_s = ((rs_sign_a_ex & ~rs_sign_b_ex) |
                    ((rs_sign_a_ex ~^ rs_sign_b_ex) & rs_mag_lt));

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

  `SVC_UNUSED({a_id[XLEN-2:16], b_id[XLEN-2:16], a_ex[15:0], b_ex[15:0]});

endmodule

`endif
