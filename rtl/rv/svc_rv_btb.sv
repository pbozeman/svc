`ifndef SVC_RV_BTB_SV
`define SVC_RV_BTB_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// Branch Target Buffer (BTB)
//
// A direct-mapped BTB for branch prediction in the RISC-V processor.
// Stores branch/jump targets and uses 2-bit saturating counters for
// direction prediction.
//
// Architecture:
//   - Direct-mapped: One entry per index
//   - Index: PC[INDEX_MSB:2] (skip low 2 bits for alignment)
//   - Tag: PC[XLEN-1:INDEX_MSB+1] for hit detection
//   - 2-bit saturating counter: 00,01 = not-taken, 10,11 = taken
//
// Operation:
//   - Lookup (combinational): Query with PC, get hit/target/prediction
//   - Update (sequential): Write entry on branch resolution
//
// Note on Direct-Mapped Collisions:
//   - Multiple PCs can map to same index (e.g. PC=0x18 and PC=0x58 both
//     map to index 6 when NENTRIES=16)
//   - When collision occurs, newer entry evicts older entry
//   - This can cause temporary BTB misses until entry is re-learned
//   - Static BTFNT prediction handles misses, so collisions affect
//     performance but not correctness
//
module svc_rv_btb #(
    parameter int XLEN     = 32,
    parameter int NENTRIES = 16
) (
    input logic clk,
    input logic rst_n,

    //
    // Lookup Interface (combinational, used in Fetch Stage)
    //
    input  logic [XLEN-1:0] lookup_pc,
    output logic            hit,
    output logic [XLEN-1:0] predicted_target,
    output logic            predicted_taken,
    output logic            is_return,

    //
    // Update Interface (sequential, used in Execute Stage)
    //
    input logic            update_en,
    input logic [XLEN-1:0] update_pc,
    input logic [XLEN-1:0] update_target,
    input logic            update_taken,
    input logic            update_is_return,
    input logic            update_is_jal
);

  //
  // Localparams
  //
  localparam int INDEX_BITS = $clog2(NENTRIES);
  localparam int INDEX_LSB = 2;
  localparam int INDEX_MSB = INDEX_LSB + INDEX_BITS - 1;
  localparam int TAG_BITS = XLEN - INDEX_MSB - 1;

  //
  // BTB Storage
  //
  logic [  NENTRIES-1:0] valid;
  logic [  TAG_BITS-1:0] tags            [NENTRIES];
  logic [      XLEN-1:0] targets         [NENTRIES];
  logic [           1:0] counters        [NENTRIES];
  logic [  NENTRIES-1:0] is_return_flags;

  //
  // Lookup path signals
  //
  logic [INDEX_BITS-1:0] lookup_index;
  logic [  TAG_BITS-1:0] lookup_tag;
  logic                  tag_match;

  //
  // Update path signals
  //
  logic [INDEX_BITS-1:0] update_index;
  logic [  TAG_BITS-1:0] update_tag;
  logic [           1:0] counter_next;
  logic                  tag_changes;
  logic                  always_taken;

  //
  // Lookup path (combinational)
  //
  assign lookup_index = lookup_pc[INDEX_MSB:INDEX_LSB];
  assign lookup_tag = lookup_pc[XLEN-1:INDEX_MSB+1];
  assign tag_match = (tags[lookup_index] == lookup_tag);
  assign hit = valid[lookup_index] && tag_match;

  //
  // Output predicted target, taken signal, and return flag
  //
  // Only output valid predictions on a hit, otherwise output zeros
  //
  assign predicted_target = hit ? targets[lookup_index] : '0;
  assign predicted_taken = hit ? counters[lookup_index][1] : 1'b0;
  assign is_return = hit ? is_return_flags[lookup_index] : 1'b0;

  //
  // Update path (combinational next-state logic)
  //
  assign update_index = update_pc[INDEX_MSB:INDEX_LSB];
  assign update_tag = update_pc[XLEN-1:INDEX_MSB+1];

  //
  // Tag change detection: entry exists but with different tag
  //
  assign
      tag_changes = valid[update_index] && (tags[update_index] != update_tag);

  //
  // JAL and returns are always taken - force counter to strongly taken
  //
  assign always_taken = update_is_jal || update_is_return;

  //
  // 2-bit saturating counter logic
  //
  always_comb begin
    if (always_taken) begin
      //
      // JAL/return: always strongly taken
      //
      counter_next = 2'b11;
    end else if (!valid[update_index] || tag_changes) begin
      //
      // New entry or tag change: reset counter
      //
      counter_next = update_taken ? 2'b10 : 2'b01;
    end else begin
      //
      // Branch with same tag: 2-bit saturating counter
      //
      counter_next = counters[update_index];
      if (update_taken) begin
        if (counter_next != 2'b11) begin
          counter_next = counter_next + 2'b01;
        end
      end else begin
        if (counter_next != 2'b00) begin
          counter_next = counter_next - 2'b01;
        end
      end
    end
  end

  //
  // Sequential logic: Update BTB on branch resolution
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      valid           <= '0;
      is_return_flags <= '0;
    end else begin
      if (update_en) begin
        valid[update_index]           <= 1'b1;
        tags[update_index]            <= update_tag;
        targets[update_index]         <= update_target;
        counters[update_index]        <= counter_next;
        is_return_flags[update_index] <= update_is_return;
      end
    end
  end

  `SVC_UNUSED({lookup_pc[INDEX_LSB-1:0], update_pc[INDEX_LSB-1:0]});

endmodule

`endif
