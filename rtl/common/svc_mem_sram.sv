`ifndef SVC_MEM_SRAM_SV
`define SVC_MEM_SRAM_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Synchronous SRAM with AXI4-Lite-ish interface
//
// Read behavior:
// - Combinational reads (0-cycle latency)
// - arvalid & arready → rvalid & rdata in SAME cycle
// - arready can backpressure if previous read not consumed (rready=0)
// - Read data held stable until rready asserted
//
// Write behavior:
// - Synchronous writes with byte strobes
// - Always accepts write requests (awready/wready always high)
// - Writes complete immediately (no write response channel)
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

    //
    // Read address channel
    //
    input  logic [31:0] araddr,
    input  logic        arvalid,
    output logic        arready,

    //
    // Read data channel
    //
    output logic [DW-1:0] rdata,
    output logic          rvalid,
    input  logic          rready,

    //
    // Write address channel
    //
    input  logic [31:0] awaddr,
    input  logic        awvalid,
    output logic        awready,

    //
    // Write data channel
    //
    input  logic [  DW-1:0] wdata,
    input  logic [DW/8-1:0] wstrb,
    input  logic            wvalid,
    output logic            wready
);

  logic [DW-1:0] mem          [2**AW];

  //
  // Word address extraction (shift off byte offset)
  //
  logic [AW-1:0] word_addr_rd;
  logic [AW-1:0] word_addr_wr;

  assign word_addr_rd = araddr[AW-1+2:2];
  assign word_addr_wr = awaddr[AW-1+2:2];

  //
  // Read response holding register
  //
  logic [DW-1:0] rdata_hold;
  logic          rvalid_hold;

  //
  // Initialize memory
  //
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

  //
  // Read address channel
  //
  // Can only accept new read if:
  // - No outstanding response (rvalid_hold=0), OR
  // - Outstanding response being consumed (rvalid_hold=1 && rready=1)
  //
  assign arready = !rvalid_hold || rready;

  //
  // Read data channel
  //
  // If holding previous response, use held data
  // Otherwise use fresh data from memory
  //
  assign rdata   = rvalid_hold ? rdata_hold : mem[word_addr_rd];
  assign rvalid  = rvalid_hold || arvalid;

  //
  // Read response holding
  //
  // Hold response if arvalid but rready not asserted
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rvalid_hold <= 1'b0;
      rdata_hold  <= '0;
    end else if (rvalid && !rready) begin
      rvalid_hold <= 1'b1;
      rdata_hold  <= rdata;
    end else if (rready) begin
      rvalid_hold <= 1'b0;
    end
  end

  //
  // Synchronous write with byte strobes
  //
  assign awready = 1'b1;
  assign wready  = 1'b1;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
`ifndef SYNTHESIS
      if (INIT_FILE == "") begin
        for (int i = 0; i < 2 ** AW; i++) begin
          mem[i] <= '0;
        end
      end
`endif
    end else if (awvalid && wvalid) begin
      for (int i = 0; i < DW / 8; i++) begin
        if (wstrb[i]) begin
          mem[word_addr_wr][i*8+:8] <= wdata[i*8+:8];
        end
      end
    end
  end

  `SVC_UNUSED({araddr[31:AW+2], araddr[1:0], awaddr[31:AW+2], awaddr[1:0]});

endmodule

`endif
