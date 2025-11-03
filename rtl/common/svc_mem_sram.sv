`ifndef SVC_MEM_SRAM_SV
`define SVC_MEM_SRAM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Synchronous SRAM with simple memory interface
//
// Read behavior:
// - Combinational reads (0-cycle latency)
// - rd_data available same cycle as rd_addr
// - Always ready to accept new address
//
// Write behavior:
// - Synchronous writes with byte strobes
// - wr_en must be asserted for write to occur
// - Writes complete immediately (no write response)
//
// Read-during-write:
// - Returns OLD data (standard SRAM behavior)
//
module svc_mem_sram #(
    parameter integer DW = 32,
    parameter integer AW = 10,

    // verilog_lint: waive explicit-parameter-storage-type
    parameter INIT_FILE = ""
) (
    input logic clk,
    input logic rst_n,

    // Read interface
    input  logic [  31:0] rd_addr,
    output logic [DW-1:0] rd_data,

    // Write interface
    input logic [    31:0] wr_addr,
    input logic [  DW-1:0] wr_data,
    input logic [DW/8-1:0] wr_strb,
    input logic            wr_en
);
  logic [DW-1:0] mem          [2**AW];

  // Word address extraction (shift off byte offset)
  logic [AW-1:0] word_addr_rd;
  logic [AW-1:0] word_addr_wr;

  assign word_addr_rd = rd_addr[AW-1+2:2];
  assign word_addr_wr = wr_addr[AW-1+2:2];

  // Initialize memory
  initial begin : init_block
`ifndef SYNTHESIS
    for (int i = 0; i < 2 ** AW; i = i + 1) begin
      mem[i] = {DW{1'b0}};
    end
`endif

    if (INIT_FILE != "") begin
      $readmemh(INIT_FILE, mem);
    end
  end

  // Combinational read (0-cycle latency)
  assign rd_data = mem[word_addr_rd];

  // Synchronous write with byte strobes
  always_ff @(posedge clk) begin
    if (!rst_n) begin
`ifndef SYNTHESIS
      if (INIT_FILE == "") begin
        for (int i = 0; i < 2 ** AW; i++) begin
          mem[i] <= '0;
        end
      end
`endif
    end else if (wr_en) begin
      for (int i = 0; i < DW / 8; i++) begin
        if (wr_strb[i]) begin
          mem[word_addr_wr][i*8+:8] <= wr_data[i*8+:8];
        end
      end
    end
  end

  `SVC_UNUSED({rd_addr[31:AW+2], rd_addr[1:0], wr_addr[31:AW+2], wr_addr[1:0]});

endmodule

`endif
