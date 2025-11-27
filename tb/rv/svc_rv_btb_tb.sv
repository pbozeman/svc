`include "svc_unit.sv"

`include "svc_rv_btb.sv"

//
// BTB Testbench
//
module svc_rv_btb_tb;
  localparam int XLEN = 32;
  localparam int NENTRIES = 16;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  //
  // UUT signals
  //
  logic [XLEN-1:0] lookup_pc;
  logic            hit;
  logic [XLEN-1:0] predicted_target;
  logic            predicted_taken;
  logic            is_return;

  logic            update_en;
  logic [XLEN-1:0] update_pc;
  logic [XLEN-1:0] update_target;
  logic            update_taken;
  logic            update_is_return;
  logic            update_is_jal;

  //
  // UUT instantiation
  //
  svc_rv_btb #(
      .XLEN    (XLEN),
      .NENTRIES(NENTRIES)
  ) uut (
      .clk             (clk),
      .rst_n           (rst_n),
      .lookup_pc       (lookup_pc),
      .hit             (hit),
      .predicted_target(predicted_target),
      .predicted_taken (predicted_taken),
      .is_return       (is_return),
      .update_en       (update_en),
      .update_pc       (update_pc),
      .update_target   (update_target),
      .update_taken    (update_taken),
      .update_is_return(update_is_return),
      .update_is_jal   (update_is_jal)
  );

  `SVC_UNUSED({is_return});

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      lookup_pc        <= '0;
      update_en        <= 1'b0;
      update_pc        <= '0;
      update_target    <= '0;
      update_taken     <= 1'b0;
      update_is_return <= 1'b0;
      update_is_jal    <= 1'b0;
    end
  end

  //
  // Reset behavior
  //
  task automatic test_reset;
    int i;

    //
    // Check all lookups miss after reset
    //
    for (i = 0; i < 32; i++) begin
      lookup_pc = 32'h1000 + (i * 4);
      `TICK(clk);
      `CHECK_FALSE(hit);
    end
  endtask

  //
  // Single entry write and read
  //
  task automatic test_single_entry;
    //
    // Write one entry
    //
    update_en     = 1'b1;
    update_pc     = 32'h0000_1000;
    update_target = 32'h0000_2000;
    update_taken  = 1'b1;
    `TICK(clk);

    //
    // Stop updating
    //
    update_en = 1'b0;
    `TICK(clk);

    //
    // Lookup the same PC
    //
    lookup_pc = 32'h0000_1000;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_EQ(predicted_target, 32'h0000_2000);
    `CHECK_TRUE(predicted_taken);

    //
    // Lookup different PC with different index
    //
    lookup_pc = 32'h0000_1004;
    `TICK(clk);
    `CHECK_FALSE(hit);
  endtask

  //
  // Counter saturation (taken direction)
  //
  task automatic test_counter_saturation_taken;

    //
    // Initialize entry to weakly taken (first update)
    //
    update_en     = 1'b1;
    update_pc     = 32'h0000_3000;
    update_target = 32'h0000_4000;
    update_taken  = 1'b1;
    `TICK(clk);

    //
    // Counter should be at 10 (weakly taken) after first taken update
    //
    lookup_pc = 32'h0000_3000;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_TRUE(predicted_taken);

    //
    // Update taken again to move to 11 (strongly taken)
    //
    update_taken = 1'b1;
    `TICK(clk);

    lookup_pc = 32'h0000_3000;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_TRUE(predicted_taken);

    //
    // Update taken again (should saturate at 11)
    //
    update_taken = 1'b1;
    `TICK(clk);

    lookup_pc = 32'h0000_3000;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_TRUE(predicted_taken);

    update_en = 1'b0;
  endtask

  //
  // Counter saturation (not-taken direction)
  //
  task automatic test_counter_saturation_not_taken;
    //
    // Initialize entry to weakly not-taken
    //
    update_en     = 1'b1;
    update_pc     = 32'h0000_5000;
    update_target = 32'h0000_6000;
    update_taken  = 1'b0;
    `TICK(clk);

    //
    // Counter should be at 01 (weakly not-taken) after first not-taken update
    //
    lookup_pc = 32'h0000_5000;
    `TICK(clk);
    `CHECK_FALSE(predicted_taken);

    //
    // Update not-taken again to move to 00 (strongly not-taken)
    //
    update_taken = 1'b0;
    `TICK(clk);

    lookup_pc = 32'h0000_5000;
    `TICK(clk);
    `CHECK_FALSE(predicted_taken);

    //
    // Update not-taken again (should saturate at 00)
    //
    update_taken = 1'b0;
    `TICK(clk);

    lookup_pc = 32'h0000_5000;
    `TICK(clk);
    `CHECK_FALSE(predicted_taken);

    update_en = 1'b0;
  endtask

  //
  // Counter transition through all states
  //
  task automatic test_counter_transitions;
    //
    // Start with taken (initialize to 10 -> weakly taken)
    //
    update_en     = 1'b1;
    update_pc     = 32'h0000_7000;
    update_target = 32'h0000_8000;
    update_taken  = 1'b1;
    `TICK(clk);

    update_en = 1'b0;
    lookup_pc = 32'h0000_7000;
    `TICK(clk);
    `CHECK_TRUE(predicted_taken);

    //
    // Increment to 11 (strongly taken)
    //
    update_en    = 1'b1;
    update_taken = 1'b1;
    `TICK(clk);

    update_en = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(predicted_taken);

    //
    // Decrement to 10 (weakly taken)
    //
    update_en    = 1'b1;
    update_taken = 1'b0;
    `TICK(clk);

    update_en = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(predicted_taken);

    //
    // Decrement to 01 (weakly not-taken)
    //
    update_en    = 1'b1;
    update_taken = 1'b0;
    `TICK(clk);

    update_en = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(predicted_taken);

    //
    // Decrement to 00 (strongly not-taken)
    //
    update_en    = 1'b1;
    update_taken = 1'b0;
    `TICK(clk);

    update_en = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(predicted_taken);

    //
    // Increment back to 01 (weakly not-taken)
    //
    update_en    = 1'b1;
    update_taken = 1'b1;
    `TICK(clk);

    update_en = 1'b0;
    `TICK(clk);
    `CHECK_FALSE(predicted_taken);

    //
    // Increment to 10 (weakly taken)
    //
    update_en    = 1'b1;
    update_taken = 1'b1;
    `TICK(clk);

    update_en = 1'b0;
    `TICK(clk);
    `CHECK_TRUE(predicted_taken);
  endtask

  //
  // Full table fill
  //
  task automatic test_full_table;
    int              i;
    logic [XLEN-1:0] pc_base;

    pc_base   = 32'h0001_0000;

    //
    // Fill all 16 entries
    //
    update_en = 1'b1;
    for (i = 0; i < 16; i++) begin
      update_pc     = pc_base + (i * 4);
      update_target = pc_base + 32'h1000 + (i * 4);
      update_taken  = (i % 2 == 0);
      `TICK(clk);
    end
    update_en = 1'b0;

    `TICK(clk);

    //
    // Verify all 16 entries hit with correct targets
    //
    for (i = 0; i < 16; i++) begin
      lookup_pc = pc_base + (i * 4);
      `TICK(clk);
      `CHECK_TRUE(hit);
      `CHECK_EQ(predicted_target, pc_base + 32'h1000 + (i * 4));
      `CHECK_EQ(predicted_taken, (i % 2 == 0));
    end
  endtask

  //
  // Index aliasing (tag mismatch)
  //
  task automatic test_aliasing;
    logic [XLEN-1:0] pc_a;
    logic [XLEN-1:0] pc_b;

    //
    // Create two PCs with same index but different tags
    // Index uses bits [5:2], so we change upper bits
    //
    pc_a          = 32'h0000_1000;
    pc_b          = 32'h0001_1000;

    //
    // Write PC_A
    //
    update_en     = 1'b1;
    update_pc     = pc_a;
    update_target = 32'hAAAA_AAAA;
    update_taken  = 1'b1;
    `TICK(clk);

    //
    // Verify PC_A hits
    //
    update_en = 1'b0;
    lookup_pc = pc_a;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_EQ(predicted_target, 32'hAAAA_AAAA);

    //
    // Write PC_B (same index, different tag - replaces PC_A)
    //
    update_en     = 1'b1;
    update_pc     = pc_b;
    update_target = 32'hBBBB_BBBB;
    update_taken  = 1'b0;
    `TICK(clk);
    update_en = 1'b0;

    `TICK(clk);

    //
    // Lookup PC_A should MISS (tag mismatch)
    //
    lookup_pc = pc_a;
    `TICK(clk);
    `CHECK_FALSE(hit);

    //
    // Lookup PC_B should HIT
    //
    lookup_pc = pc_b;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_EQ(predicted_target, 32'hBBBB_BBBB);
    `CHECK_FALSE(predicted_taken);
  endtask

  //
  // Concurrent lookup and update
  //
  task automatic test_concurrent_access;
    //
    // Setup two entries
    //
    update_en     = 1'b1;
    update_pc     = 32'h0002_0000;
    update_target = 32'h0002_1000;
    update_taken  = 1'b1;
    `TICK(clk);

    update_pc     = 32'h0002_0004;
    update_target = 32'h0002_2000;
    update_taken  = 1'b0;
    `TICK(clk);

    //
    // Update entry 0 while looking up entry 1 (different indices)
    //
    update_pc     = 32'h0002_0000;
    update_target = 32'h0002_9000;
    update_taken  = 1'b0;
    lookup_pc     = 32'h0002_0004;
    `TICK(clk);

    //
    // Lookup should see old value (before update)
    //
    `CHECK_TRUE(hit);
    `CHECK_EQ(predicted_target, 32'h0002_2000);

    //
    // Next cycle, lookup entry 0 to see new value
    //
    update_en = 1'b0;
    lookup_pc = 32'h0002_0000;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_EQ(predicted_target, 32'h0002_9000);
    `CHECK_FALSE(predicted_taken);
  endtask

  //
  // Target update on same PC
  //
  task automatic test_target_update;
    //
    // Write initial target
    //
    update_en     = 1'b1;
    update_pc     = 32'h0003_0000;
    update_target = 32'h0003_1000;
    update_taken  = 1'b1;
    `TICK(clk);

    update_en = 1'b0;
    lookup_pc = 32'h0003_0000;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_EQ(predicted_target, 32'h0003_1000);

    //
    // Update with new target
    //
    update_en     = 1'b1;
    update_target = 32'h0003_2000;
    update_taken  = 1'b1;
    `TICK(clk);

    update_en = 1'b0;
    `TICK(clk);

    //
    // Verify new target
    //
    lookup_pc = 32'h0003_0000;
    `TICK(clk);
    `CHECK_TRUE(hit);
    `CHECK_EQ(predicted_target, 32'h0003_2000);
  endtask

  //
  // Test suite
  //
  `TEST_SUITE_BEGIN(svc_rv_btb_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_single_entry);
  `TEST_CASE(test_counter_saturation_taken);
  `TEST_CASE(test_counter_saturation_not_taken);
  `TEST_CASE(test_counter_transitions);
  `TEST_CASE(test_full_table);
  `TEST_CASE(test_aliasing);
  `TEST_CASE(test_concurrent_access);
  `TEST_CASE(test_target_update);
  `TEST_SUITE_END();

endmodule
