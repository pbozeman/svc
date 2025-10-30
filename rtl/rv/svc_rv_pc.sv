`ifndef SVC_RV_PC_SV
`define SVC_RV_PC_SV

`include "svc.sv"

module svc_rv_pc #(
    parameter int XLEN = 32
) (
    input logic clk,
    input logic rst_n,

    input logic            pc_sel,
    input logic [XLEN-1:0] jb_target,

    output logic [XLEN-1:0] pc,
    output logic [XLEN-1:0] pc_plus4
);
  logic [XLEN-1:0] pc_next;

  assign pc_plus4 = pc + 4;
  assign pc_next  = pc_sel ? jb_target : pc_plus4;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= '0;
    end else begin
      pc <= pc_next;
    end
  end

endmodule

`endif
