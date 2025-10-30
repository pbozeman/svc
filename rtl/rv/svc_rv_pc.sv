`ifndef SVC_RV_PC_SV
`define SVC_RV_PC_SV

`include "svc.sv"

module svc_rv_pc #(
    parameter int XLEN = 32
) (
    input logic clk,
    input logic rst_n,

    output logic [XLEN-1:0] pc
);
  logic [XLEN-1:0] pc_next;

  always_comb begin
    pc_next = pc + 4;
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= 0;
    end else begin
      pc <= pc_next;
    end
  end

endmodule

`endif
