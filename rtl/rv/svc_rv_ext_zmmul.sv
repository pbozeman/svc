`ifndef SVC_RV_EXT_ZMMUL_SV
`define SVC_RV_EXT_ZMMUL_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Zmmul extension unit
//
// Implements MUL, MULH, MULHSU, MULHU instructions using combinational
// multiply. All operations complete in 1 cycle.
//
// Operation encoding (matches funct3[1:0]):
//   00 (MUL):    Lower 32 bits of rs1 * rs2 (signed × signed)
//   01 (MULH):   Upper 32 bits of rs1 * rs2 (signed × signed)
//   10 (MULHSU): Upper 32 bits of rs1 * rs2 (signed × unsigned)
//   11 (MULHU):  Upper 32 bits of rs1 * rs2 (unsigned × unsigned)
//
module svc_rv_ext_zmmul (
    input logic clk,
    input logic rst_n,

    input  logic        en,
    input  logic [31:0] rs1,
    input  logic [31:0] rs2,
    input  logic [ 2:0] op,
    output logic        busy,

    output logic [31:0] result,
    output logic        result_valid
);

  //
  // Sign-extend operands based on op[1:0]
  //
  // MUL (00):    signed × signed, lower 32
  // MULH (01):   signed × signed, upper 32
  // MULHSU (10): signed × unsigned, upper 32
  // MULHU (11):  unsigned × unsigned, upper 32
  //
  logic [32:0] rs1_ext;
  logic [32:0] rs2_ext;
  logic [65:0] product;
  logic [31:0] result_bits;

  assign rs1_ext      = (op[1:0] == 2'b11) ? {1'b0, rs1} : {rs1[31], rs1};
  assign rs2_ext      = (op[1]) ? {1'b0, rs2} : {rs2[31], rs2};

  //
  // Single multiply
  //
  assign product      = $signed(rs1_ext) * $signed(rs2_ext);

  //
  // Select upper or lower 32 bits
  //
  assign result_bits  = (op[1:0] == 2'b00) ? product[31:0] : product[63:32];

  //
  // Result selection (combinational)
  //
  assign result       = result_bits;
  assign result_valid = en;
  assign busy         = 1'b0;

  `SVC_UNUSED({clk, rst_n, op[2], product[65:64]});

endmodule

`endif
