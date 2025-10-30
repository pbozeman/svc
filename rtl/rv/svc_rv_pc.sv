`ifndef SVC_RV_PC_SV
`define SVC_RV_PC_SV

`include "svc.sv"

module svc_rv_pc #(
    parameter int XLEN = 32
) (
    input logic clk,
    input logic rst_n,

    output logic [XLEN-1:0] pc,
    output logic [XLEN-1:0] pc_plus4
);
  assign pc_plus4 = pc + 4;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= 0;
    end else begin
      pc <= pc_plus4;
    end
  end

endmodule

`endif
