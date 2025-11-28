`ifndef SVC_RV_EXT_DIV_SV
`define SVC_RV_EXT_DIV_SV

`include "svc.sv"
`include "svc_divu.sv"
`include "svc_unused.sv"

//
// RISC-V M extension division unit
//
// Implements DIV, DIVU, REM, REMU instructions using restoring division.
//
// Division is a 32-cycle sequential operation.
//
// Operation encoding (matches funct3):
//   100 (DIV):  Signed division quotient
//   101 (DIVU): Unsigned division quotient
//   110 (REM):  Signed division remainder
//   111 (REMU): Unsigned division remainder
//
module svc_rv_ext_div (
    input logic clk,
    input logic rst_n,

    input  logic        en,
    input  logic [31:0] rs1,
    input  logic [31:0] rs2,
    input  logic [ 2:0] op,
    output logic        busy,
    output logic [31:0] result
);

`ifndef RISCV_FORMAL_ALTOPS
  //
  // Division unit (unsigned restoring division)
  //
  logic        div_busy;
  logic        div_valid;
  logic        div_zero;
  logic [31:0] quotient;
  logic [31:0] remainder;

  //
  // Signed division requires special handling
  //
  // Sign bits and rs1 must be latched when division starts because the
  // forwarded operand values may change during multi-cycle execution
  // (MEM/WB stages drain while EX stalls for multi-cycle ops).
  //
  logic        is_signed_div;
  logic        rs1_neg;
  logic        rs2_neg;
  logic        rs1_neg_reg;
  logic        rs2_neg_reg;
  logic [31:0] rs1_reg;
  logic        negate_result;

  logic [31:0] dividend_abs;
  logic [31:0] divisor_abs;
  logic [31:0] quotient_signed;
  logic [31:0] remainder_signed;

  assign is_signed_div = !op[0];
  assign rs1_neg       = rs1[31];
  assign rs2_neg       = rs2[31];

  //
  // Latch sign bits and rs1 when division starts
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rs1_neg_reg <= 1'b0;
      rs2_neg_reg <= 1'b0;
      rs1_reg     <= '0;
    end else if (en) begin
      rs1_neg_reg <= rs1_neg;
      rs2_neg_reg <= rs2_neg;
      rs1_reg     <= rs1;
    end
  end

  //
  // For signed operations, compute absolute values
  //
  assign dividend_abs = (is_signed_div && rs1_neg) ? -rs1 : rs1;
  assign divisor_abs = (is_signed_div && rs2_neg) ? -rs2 : rs2;

  //
  // Negate quotient if signs differ, negate remainder if dividend is negative
  //
  // Use registered sign bits to handle forwarding changes during multi-cycle op
  //
  assign negate_result = is_signed_div && (rs1_neg_reg ^ rs2_neg_reg);
  assign quotient_signed = negate_result ? -quotient : quotient;
  assign remainder_signed = (is_signed_div && rs1_neg_reg) ? -remainder :
      remainder;

  //
  // Division unit instantiation
  //
  svc_divu #(
      .WIDTH(32)
  ) divu (
      .clk      (clk),
      .rst_n    (rst_n),
      .en       (en),
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
  logic div_result_is_rem;

  //
  // Handle division by zero per RISC-V spec
  //
  // When divisor is zero, svc_divu immediately sets div_zero=1, busy=0
  // and we can return the result immediately
  //
  assign div_result_is_rem = op[1];

  always_comb begin
    if (div_zero) begin
      //
      // Use registered rs1 to handle forwarding changes during multi-cycle op
      //
      if (div_result_is_rem) begin
        result = rs1_reg;
      end else begin
        result = 32'hFFFFFFFF;
      end
    end else begin
      if (div_result_is_rem) begin
        result = remainder_signed;
      end else begin
        result = quotient_signed;
      end
    end
  end

  //
  // Output busy signal
  //
  assign busy = div_busy;

  `SVC_UNUSED({div_valid, div_zero, op[2]});

`else
  //
  // RISCV_FORMAL_ALTOPS: Alternative operations for formal verification.
  //
  // Division is beyond practical capabilities of hardware model checkers.
  // riscv-formal defines alternative operations using simple sub + XOR
  // to verify bypassing and pipeline behavior.
  //
  // See: https://yosyshq.readthedocs.io/projects/riscv-formal/en/latest/rvfi.html#alternative-arithmetic-operations
  //
  localparam int ALTOPS_CYCLES = 3;

  logic [1:0] f_count;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      f_count <= '0;
    end else if (en) begin
      f_count <= 2'd1;
    end else if (busy) begin
      f_count <= f_count + 2'd1;
    end
  end

  assign busy = (f_count != '0) && (f_count != 2'(ALTOPS_CYCLES));

  always_comb begin
    case (op[1:0])
      2'b00:   result = (rs1 - rs2) ^ 32'h7f8529ec;
      2'b01:   result = (rs1 - rs2) ^ 32'h10e8fd70;
      2'b10:   result = (rs1 - rs2) ^ 32'h8da68fa5;
      2'b11:   result = (rs1 - rs2) ^ 32'h3138d0e1;
      default: result = '0;
    endcase
  end

  `SVC_UNUSED({op[2]});

`endif

endmodule

`endif
