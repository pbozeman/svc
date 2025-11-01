`ifndef SVC_RV_IMEM_SV
`define SVC_RV_IMEM_SV

`include "svc.sv"
`include "svc_unused.sv"

// Instruction memory with optional registered output.
//
// When REGISTERED=1: Output is registered to infer Block RAM (adds 1 cycle latency)
// When REGISTERED=0: Output is combinational (for single-cycle designs)
//
// Enable signal allows holding the output register during pipeline stalls

module svc_rv_imem #(
    parameter integer AW         = 10,
    parameter bit     REGISTERED = 1,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter INIT_FILE = ""
) (
    input logic clk,
    input logic rst_n,
    input logic en,

    input  logic [AW-1:0] addr,
    output logic [  31:0] data
);
  logic [31:0] mem       [2**AW];
  logic [31:0] data_next;

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

  //
  // Combinational read
  //
  assign data_next = mem[addr];

  //
  // Output path: registered or combinational based on parameter
  //
  if (REGISTERED) begin : gen_registered
    // Registered version
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        data <= 32'b0;
      end else if (en) begin
        data <= data_next;
      end
    end
  end else begin : gen_combinational
    // Unregistered version
    assign data = data_next;

    `SVC_UNUSED({clk, rst_n, en});
  end

endmodule

`endif
