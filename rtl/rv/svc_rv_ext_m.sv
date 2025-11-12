`ifndef SVC_RV_EXT_M_SV
`define SVC_RV_EXT_M_SV

`include "svc.sv"
`include "svc_divu.sv"
`include "svc_unused.sv"

//
// RISC-V M extension unit
//
// Implements MUL, MULH, MULHSU, MULHU, DIV, DIVU, REM, REMU instructions.
//
// Multiplication operations complete in 1 cycle (combinational).
// Division/remainder operations take 32 cycles using restoring division.
//
// Operation encoding (matches funct3):
//   000 (MUL):    Lower 32 bits of rs1 * rs2 (signed × signed)
//   001 (MULH):   Upper 32 bits of rs1 * rs2 (signed × signed)
//   010 (MULHSU): Upper 32 bits of rs1 * rs2 (signed × unsigned)
//   011 (MULHU):  Upper 32 bits of rs1 * rs2 (unsigned × unsigned)
//   100 (DIV):    Signed division quotient
//   101 (DIVU):   Unsigned division quotient
//   110 (REM):    Signed division remainder
//   111 (REMU):   Unsigned division remainder
//
module svc_rv_ext_m (
    input logic clk,
    input logic rst_n,

    input  logic        en,
    input  logic [31:0] rs1,
    input  logic [31:0] rs2,
    input  logic [ 2:0] op,
    output logic        busy,

    output logic [31:0] result
);

  //
  // Operation type decode
  //
  logic is_mul;
  logic is_div;

  assign is_mul = !op[2];
  assign is_div = op[2];

  //
  // Multiplication logic (combinational, from zmmul)
  //
  logic [32:0] rs1_ext;
  logic [32:0] rs2_ext;
  logic [65:0] product;
  logic [31:0] mul_result;

  assign rs1_ext    = (op[1:0] == 2'b11) ? {1'b0, rs1} : {rs1[31], rs1};
  assign rs2_ext    = (op[1]) ? {1'b0, rs2} : {rs2[31], rs2};

  assign product    = $signed(rs1_ext) * $signed(rs2_ext);

  //
  // Select upper or lower 32 bits
  //
  assign mul_result = (op[1:0] == 2'b00) ? product[31:0] : product[63:32];

  //
  // Division logic (sequential, using svc_divu)
  //
  logic        div_en;
  logic        div_busy;
  logic        div_valid;
  logic        div_zero;
  logic [31:0] quotient;
  logic [31:0] remainder;

  //
  // Signed division requires special handling
  //
  logic        is_signed_div;
  logic        rs1_neg;
  logic        rs2_neg;
  logic        negate_result;

  logic [31:0] dividend_abs;
  logic [31:0] divisor_abs;
  logic [31:0] quotient_signed;
  logic [31:0] remainder_signed;

  assign is_signed_div = is_div && !op[0];
  assign rs1_neg = rs1[31];
  assign rs2_neg = rs2[31];

  //
  // For signed operations, compute absolute values
  //
  assign dividend_abs = (is_signed_div && rs1_neg) ? -rs1 : rs1;
  assign divisor_abs = (is_signed_div && rs2_neg) ? -rs2 : rs2;

  //
  // Negate quotient if signs differ, negate remainder if dividend is negative
  //
  assign negate_result = is_signed_div && (rs1_neg ^ rs2_neg);
  assign quotient_signed = negate_result ? -quotient : quotient;
  assign remainder_signed = (is_signed_div && rs1_neg) ? -remainder : remainder;

  //
  // Division unit instantiation
  //
  assign div_en = en && is_div;

  svc_divu #(
      .WIDTH(32)
  ) divu (
      .clk      (clk),
      .rst_n    (rst_n),
      .en       (div_en),
      .dividend (dividend_abs),
      .divisor  (divisor_abs),
      .busy     (div_busy),
      .valid    (div_valid),
      .div_zero (div_zero),
      .quotient (quotient),
      .remainder(remainder)
  );

  //
  // Result selection
  //
  logic [31:0] div_result;
  logic        div_result_is_rem;

  //
  // Handle division by zero per RISC-V spec
  //
  // When divisor is zero, svc_divu immediately sets div_zero=1, busy=0
  // and we can return the result immediately
  //
  assign div_result_is_rem = op[1];

  always_comb begin
    if (div_zero) begin
      if (div_result_is_rem) begin
        div_result = rs1;
      end else begin
        div_result = 32'hFFFFFFFF;
      end
    end else begin
      if (div_result_is_rem) begin
        div_result = remainder_signed;
      end else begin
        div_result = quotient_signed;
      end
    end
  end

  //
  // Output selection
  //
  // Result selection and busy signal
  //
  assign result = is_mul ? mul_result : div_result;
  assign busy   = div_busy;

  `SVC_UNUSED({product[65:64], div_valid, div_zero});

endmodule

`endif
