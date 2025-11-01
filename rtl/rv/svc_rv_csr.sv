`ifndef SVC_RV_CSR_SV
`define SVC_RV_CSR_SV

`include "svc.sv"

//
// RISC-V CSR (Control and Status Register) module
//
// Implements Zicntr extension (base counters and timers):
// - CYCLE/CYCLEH: 64-bit cycle counter
// - INSTRET/INSTRETH: 64-bit retired instruction counter
//
// Read-only counters - no write support needed for Zicntr.
//
module svc_rv_csr (
    input logic clk,
    input logic rst_n,

    //
    // CSR read interface
    //
    input  logic [11:0] csr_addr,
    output logic [31:0] csr_rdata,

    //
    // Counter controls
    //
    input logic instret_inc
);

  `include "svc_rv_defs.svh"

  logic [31:0] cycle;
  logic [31:0] cycleh;
  logic [31:0] instret;
  logic [31:0] instreth;

  logic [31:0] cycle_next;
  logic [31:0] cycleh_next;
  logic [31:0] instret_next;
  logic [31:0] instreth_next;

  //
  // CSR reads
  //
  always_comb begin
    case (csr_addr)
      CSR_CYCLE:    csr_rdata = cycle;
      CSR_CYCLEH:   csr_rdata = cycleh;
      CSR_INSTRET:  csr_rdata = instret;
      CSR_INSTRETH: csr_rdata = instreth;
      default:      csr_rdata = 32'h0;
    endcase
  end

  //
  // Counters
  //
  always_comb begin
    //
    // CYCLE counter (always increments)
    //
    {cycleh_next, cycle_next} = {cycleh, cycle} + 64'h1;

    //
    // INSTRET counter (increments on instruction retirement)
    //
    if (instret_inc) begin
      {instreth_next, instret_next} = {instreth, instret} + 64'h1;
    end else begin
      instreth_next = instreth;
      instret_next  = instret;
    end
  end

  //
  // Register counters
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      cycle    <= 32'h0;
      cycleh   <= 32'h0;
      instret  <= 32'h0;
      instreth <= 32'h0;
    end else begin
      cycle    <= cycle_next;
      cycleh   <= cycleh_next;
      instret  <= instret_next;
      instreth <= instreth_next;
    end
  end

endmodule

`endif
