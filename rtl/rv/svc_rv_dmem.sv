`ifndef SVC_RV_DMEM_SV
`define SVC_RV_DMEM_SV

`include "svc.sv"

//
// RISC-V Data Memory (BRAM)
//
// When REGISTERED=1: Output is registered to infer Block RAM (adds 1 cycle latency)
// When REGISTERED=0: Output is combinational (for single-cycle designs)
//
// Supports byte-level write strobes for LB/LH/LBU/LHU/SB/SH/SW instructions.
// Read-during-write behavior: reads return OLD data (standard BRAM behavior)
//
module svc_rv_dmem #(
    parameter integer DW         = 32,
    parameter integer AW         = 10,
    parameter bit     REGISTERED = 1
) (
    input logic clk,
    input logic rst_n,

    input logic [AW-1:0] addr,

    input logic [  DW-1:0] wdata,
    input logic            we,
    input logic [DW/8-1:0] wstrb,

    output logic [DW-1:0] rdata
);

  //
  // Synthesis attributes for BRAM inference
  // Xilinx: ram_style, Altera/Intel: ramstyle
  //
  (* ram_style = "block" *)
  (* ramstyle  = "block" *)
  logic [DW-1:0] mem        [2**AW];
  logic [DW-1:0] rdata_next;

  //
  // Initialize memory to zero
  // This allows hierarchical testbench access and predictable behavior
  //
  initial begin : init_block
    integer i;
    for (i = 0; i < 2 ** AW; i = i + 1) begin
      mem[i] = {DW{1'b0}};
    end
  end

  //
  // Combinational read
  //
  assign rdata_next = mem[addr];

  //
  // Output path: registered or combinational based on parameter
  //
  if (REGISTERED) begin : gen_registered
    // Registered version for BRAM inference
    always_ff @(posedge clk) begin
      if (!rst_n) begin
        rdata <= {DW{1'b0}};
      end else begin
        rdata <= rdata_next;
      end
    end
  end else begin : gen_combinational
    // Unregistered version for single-cycle designs
    assign rdata = rdata_next;
  end

  //
  // Synchronous write with byte write strobes
  // Each byte can be individually written based on wstrb
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
`ifndef SYNTHESIS
      for (int i = 0; i < 2 ** AW; i++) begin
        mem[i] <= '0;
      end
`endif
    end else if (we) begin
      for (int i = 0; i < DW / 8; i++) begin
        if (wstrb[i]) begin
          mem[addr][i*8+:8] <= wdata[i*8+:8];
        end
      end
    end
  end

endmodule

`endif
