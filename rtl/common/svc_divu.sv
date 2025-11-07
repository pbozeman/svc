`ifndef SVC_DIVU_SV
`define SVC_DIVU_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Unsigned integer divider with remainder
//
// Based on Project F's divu_int.sv (MIT License)
// https://projectf.io/verilog-lib/
//
// Implements restoring division algorithm that processes one bit per clock
// cycle over WIDTH iterations.
//
module svc_divu #(
    parameter int WIDTH = 32
) (
    input logic clk,
    input logic rst_n,

    input  logic             en,
    input  logic [WIDTH-1:0] dividend,
    input  logic [WIDTH-1:0] divisor,
    output logic             busy,

    output logic             valid,
    output logic             div_zero,
    output logic [WIDTH-1:0] quotient,
    output logic [WIDTH-1:0] remainder
);

  logic [        WIDTH-1:0] divisor_reg;
  logic [        WIDTH-1:0] quo;
  logic [        WIDTH-1:0] quo_next;
  logic [          WIDTH:0] acc;
  logic [          WIDTH:0] acc_next;

  logic [$clog2(WIDTH)-1:0] count;

  //
  // Division algorithm iteration
  //
  logic [          WIDTH:0] acc_sub;
  logic [        WIDTH-1:0] acc_sub_lower;

  assign acc_sub       = acc - {1'b0, divisor_reg};
  assign acc_sub_lower = acc_sub[WIDTH-1:0];

  always_comb begin
    if (acc >= {1'b0, divisor_reg}) begin
      {acc_next, quo_next} = {acc_sub_lower, quo, 1'b1};
    end else begin
      {acc_next, quo_next} = {acc, quo} << 1;
    end
  end

  //
  // Control logic
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      busy        <= 1'b0;
      valid       <= 1'b0;
      div_zero    <= 1'b0;
      quotient    <= '0;
      remainder   <= '0;
      count       <= '0;
      divisor_reg <= '0;
      quo         <= '0;
      acc         <= '0;
    end else begin
      if (en) begin
        valid <= 1'b0;
        count <= '0;

        if (divisor == '0) begin
          busy     <= 1'b0;
          div_zero <= 1'b1;
        end else begin
          busy        <= 1'b1;
          div_zero    <= 1'b0;
          divisor_reg <= divisor;
          {acc, quo}  <= {{WIDTH{1'b0}}, dividend, 1'b0};
        end
      end else if (busy) begin
        if (count == $clog2(WIDTH)'(WIDTH - 1)) begin
          busy      <= 1'b0;
          valid     <= 1'b1;
          quotient  <= quo_next;
          remainder <= acc_next[WIDTH:1];
        end else begin
          count <= count + 1;
          acc   <= acc_next;
          quo   <= quo_next;
        end
      end
    end
  end

  `SVC_UNUSED(acc_sub[WIDTH]);

endmodule

`endif
