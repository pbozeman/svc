`ifndef SVC_RV_IMEM_SV
`define SVC_RV_IMEM_SV

`include "svc.sv"

// Synchronous read memory with registered output to infer Block RAM.
//
// Enable signal allows holding the output register during pipeline stalls

module svc_rv_imem #(
    parameter integer AW = 10,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter INIT_FILE = ""
) (
    input logic clk,
    input logic rst_n,
    input logic en,

    input  logic [AW-1:0] addr,
    output logic [  31:0] data
);
  (* ram_style = "block" *)
  logic [31:0] mem[2**AW];

  // Initialize memory
  //
  // If INIT_FILE is specified, load from hex file, otherwise initialize to zero
  // for testbench access.
  initial begin : init_block

`ifndef SYNTHESIS
    for (int i = 0; i < 2 ** AW; i = i + 1) begin
      mem[i] = 32'b0;
    end
`endif

    if (INIT_FILE != "") begin
      $readmemh(INIT_FILE, mem);
    end
  end

  // Synchronous read with registered output (critical for BRAM inference)
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      data <= 32'b0;
    end else if (en) begin
      data <= mem[addr];
    end
  end

endmodule

`endif
