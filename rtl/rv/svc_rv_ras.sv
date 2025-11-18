`ifndef SVC_RV_RAS_SV
`define SVC_RV_RAS_SV

`include "svc.sv"

//
// Return Address Stack (RAS)
//
// A circular return address stack for predicting function return targets.
// Used to improve branch prediction for JALR return instructions.
//
// Architecture:
//   - Circular buffer with configurable depth (default 8 entries)
//   - Stack pointer (SP) points to the top of stack
//   - On push: SP increments (wraps at DEPTH), write return address
//   - On pop: SP decrements (wraps at 0)
//   - Valid when count > 0 (tracks number of valid entries)
//
// Operation:
//   - Lookup (combinational): Read top of stack for prediction
//   - Push (sequential): Write return address when JAL/JALR with rd != x0
//   - Pop (sequential): Decrement SP when JALR executed
//
// Note on Overflow/Underflow:
//   - Overflow: Oldest entries are overwritten (circular behavior)
//   - Underflow: Pop when empty keeps SP at 0, valid stays 0
//   - Mispredictions are detected in EX stage like other branches
//
module svc_rv_ras #(
    parameter int XLEN  = 32,
    parameter int DEPTH = 8
) (
    input logic clk,
    input logic rst_n,

    //
    // Lookup Interface (combinational, used in Fetch Stage)
    //
    output logic            ras_valid,
    output logic [XLEN-1:0] ras_target,

    //
    // Update Interface (sequential, used in MEM Stage)
    //
    input logic            push_en,
    input logic [XLEN-1:0] push_addr,
    input logic            pop_en
);

  //
  // Localparams
  //
  localparam int SP_BITS = $clog2(DEPTH);
  localparam int COUNT_BITS = $clog2(DEPTH + 1);

  //
  // RAS Storage
  //
  logic [      XLEN-1:0] stack         [DEPTH];
  logic [   SP_BITS-1:0] sp;
  logic [COUNT_BITS-1:0] count;

  //
  // Next-cycle signals
  //
  logic [   SP_BITS-1:0] sp_next;
  logic [COUNT_BITS-1:0] count_next;

  //
  // Lookup path (combinational)
  //
  // Forward push data for simultaneous push/lookup in same cycle.
  // When JAL pushes in MEM stage while JALR looks up in IF stage (same cycle),
  // we need to see the updated count and forward the push_addr being written.
  //
  // Use count_next only when push is active to see the incremented count.
  // Otherwise use registered count (already reflects completed push/pop).
  //
  logic                  lookup_valid;
  logic [      XLEN-1:0] lookup_target;

  assign lookup_valid  = push_en ? (count_next > 0) : (count > 0);
  assign lookup_target = push_en ? push_addr : stack[sp];

  assign ras_valid     = lookup_valid;
  assign ras_target    = lookup_valid ? lookup_target : '0;

  //
  // Update path (combinational next-state logic)
  //
  always_comb begin
    sp_next    = sp;
    count_next = count;

    //
    // Handle simultaneous push and pop (net effect: replace top)
    //
    if (push_en && pop_en) begin
      sp_next    = sp;
      count_next = count;
    end else if (push_en) begin
      //
      // Push: increment SP (wrap at DEPTH), increment count (saturate at DEPTH)
      //
      sp_next = (sp == SP_BITS'(DEPTH - 1)) ? '0 : sp + 1'b1;
      if (count < COUNT_BITS'(DEPTH)) begin
        count_next = count + 1'b1;
      end
    end else if (pop_en) begin
      //
      // Pop: decrement SP (wrap at 0), decrement count (saturate at 0)
      //
      if (count > 0) begin
        sp_next    = (sp == '0) ? SP_BITS'(DEPTH - 1) : sp - 1'b1;
        count_next = count - 1'b1;
      end
    end
  end

  //
  // Sequential logic: Update RAS
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      sp    <= '0;
      count <= '0;
    end else begin
      sp    <= sp_next;
      count <= count_next;

      //
      // Write to stack on push
      //
      if (push_en) begin
        stack[sp_next] <= push_addr;
      end
    end
  end

endmodule

`endif
