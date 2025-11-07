`ifndef SVC_RV_PC_SV
`define SVC_RV_PC_SV

`include "svc.sv"

module svc_rv_pc #(
    parameter int XLEN = 32
) (
    input logic clk,
    input logic rst_n,

    input logic            stall,
    input logic            pc_sel,
    input logic [XLEN-1:0] jb_target,
    input logic            pred_taken,
    input logic [XLEN-1:0] pred_target,

    output logic [XLEN-1:0] pc,
    output logic [XLEN-1:0] pc_plus4
);
  logic [XLEN-1:0] pc_next;

  assign pc_plus4 = pc + 4;

  //
  // PC next calculation with 3-way priority:
  // 1. Actual branch/jump taken (pc_sel) - highest priority
  // 2. Predicted branch taken (pred_taken) - speculative fetch
  // 3. Sequential (pc_plus4) - default
  //
  always_comb begin
    case (1'b1)
      pc_sel:     pc_next = jb_target;
      pred_taken: pc_next = pred_target;
      default:    pc_next = pc_plus4;
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      pc <= '0;
    end else if (!stall) begin
      pc <= pc_next;
    end
  end

endmodule

`endif
