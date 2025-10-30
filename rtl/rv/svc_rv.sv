`ifndef SVC_RV_SV
`define SVC_RV_SV

`include "svc.sv"
`include "svc_rv_imem.sv"

module svc_rv #(
    parameter int IMEM_AW = 10,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter IMEM_INIT = ""
) (
    input logic clk,
    input logic rst_n
);

  //
  // Instruction memory signals
  //
  logic               imem_en;
  logic [IMEM_AW-1:0] imem_addr;
  // logic [       31:0] imem_data;

  //
  // Instruction memory
  //
  svc_rv_imem #(
      .AW       (IMEM_AW),
      .INIT_FILE(IMEM_INIT)
  ) u_imem (
      .clk  (clk),
      .rst_n(rst_n),
      .en   (imem_en),
      .addr (imem_addr),
      .data ()
  );

  assign imem_en   = 1'b1;
  assign imem_addr = '0;

endmodule

`endif
