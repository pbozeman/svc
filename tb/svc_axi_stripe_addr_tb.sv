`include "svc_unit.sv"
`include "svc_axi_stripe_addr.sv"

// The tb breaks from convention and has multiple UUTs since it's necessary to
// test various parameters of the addr calcs.
//
// There is no clock, so #10 was manually added between checks in order to
// visualize signals in gtkwave.

module svc_axi_stripe_addr_tb;
  // UUT1: 2 subordinates, 16-bit data (2 bytes per word)
  parameter U1_NUM_S = 2;
  parameter U1_AW = 8;
  parameter U1_DW = 16;
  parameter U1_SW = $clog2(U1_NUM_S);
  parameter U1_SAW = U1_AW - $clog2(U1_NUM_S);
  logic [ U1_AW-1:0] u1_s_axi_axaddr;
  logic [ U1_SW-1:0] u1_sub_idx;
  logic              u1_word_aligned;
  logic [U1_SAW-1:0] u1_m_axi_axaddr;

  // UUT2: 4 subordinates, 32-bit data (4 bytes per word)
  parameter U2_NUM_S = 4;
  parameter U2_AW = 16;
  parameter U2_DW = 32;
  parameter U2_SW = $clog2(U2_NUM_S);
  parameter U2_SAW = U2_AW - $clog2(U2_NUM_S);
  logic [ U2_AW-1:0] u2_s_axi_axaddr;
  logic [ U2_SW-1:0] u2_sub_idx;
  logic              u2_word_aligned;
  logic [U2_SAW-1:0] u2_m_axi_axaddr;

  // UUT3: 2 subordinates, 8-bit data (single byte words)
  parameter U3_NUM_S = 2;
  parameter U3_AW = 8;
  parameter U3_DW = 8;
  parameter U3_SW = $clog2(U3_NUM_S);
  parameter U3_SAW = U3_AW - $clog2(U3_NUM_S);
  logic [ U3_AW-1:0] u3_s_axi_axaddr;
  logic [ U3_SW-1:0] u3_sub_idx;
  logic              u3_word_aligned;
  logic [U3_SAW-1:0] u3_m_axi_axaddr;

  svc_axi_stripe_addr #(
      .NUM_S         (U1_NUM_S),
      .AXI_ADDR_WIDTH(U1_AW),
      .AXI_DATA_WIDTH(U1_DW)
  ) uut1 (
      .s_axi_axaddr(u1_s_axi_axaddr),
      .sub_idx     (u1_sub_idx),
      .word_aligned(u1_word_aligned),
      .m_axi_axaddr(u1_m_axi_axaddr)
  );

  svc_axi_stripe_addr #(
      .NUM_S         (U2_NUM_S),
      .AXI_ADDR_WIDTH(U2_AW),
      .AXI_DATA_WIDTH(U2_DW)
  ) uut2 (
      .s_axi_axaddr(u2_s_axi_axaddr),
      .sub_idx     (u2_sub_idx),
      .word_aligned(u2_word_aligned),
      .m_axi_axaddr(u2_m_axi_axaddr)
  );

  svc_axi_stripe_addr #(
      .NUM_S         (U3_NUM_S),
      .AXI_ADDR_WIDTH(U3_AW),
      .AXI_DATA_WIDTH(U3_DW)
  ) uut3 (
      .s_axi_axaddr(u3_s_axi_axaddr),
      .sub_idx     (u3_sub_idx),
      .word_aligned(u3_word_aligned),
      .m_axi_axaddr(u3_m_axi_axaddr)
  );

  // Test UUT1: 2 subordinates, 16-bit data
  task automatic test_u1;
    // Test case 1: Address 0
    #10;
    u1_s_axi_axaddr = 0;
    `CHECK_EQ(u1_sub_idx, 0);
    `CHECK_TRUE(u1_word_aligned);
    `CHECK_EQ(u1_m_axi_axaddr, 0);

    // Test case 2: Address that should go to subordinate 1
    #10;
    u1_s_axi_axaddr = 8'b1000_0010;
    `CHECK_EQ(u1_sub_idx, 1);
    `CHECK_TRUE(u1_word_aligned);
    `CHECK_EQ(u1_m_axi_axaddr, 7'b1000_000);

    // Test case 3: Unaligned address
    #10;
    u1_s_axi_axaddr = 8'b1000_0001;
    `CHECK_EQ(u1_sub_idx, 0);
    `CHECK_FALSE(u1_word_aligned);
    `CHECK_EQ(u1_m_axi_axaddr, 7'b1000_001);

    // Test case 4: Maximum address
    #10;
    u1_s_axi_axaddr = 8'hFF;
    `CHECK_EQ(u1_sub_idx, 1);
    `CHECK_FALSE(u1_word_aligned);
  endtask

  // Test UUT2: 4 subordinates, 32-bit data
  task automatic test_u2;
    // Test case 1: Address 0
    #10;
    u2_s_axi_axaddr = 0;
    `CHECK_EQ(u2_sub_idx, 0);
    `CHECK_TRUE(u2_word_aligned);
    `CHECK_EQ(u2_m_axi_axaddr, 0);

    // Test case 2: Address to subordinate 2, word aligned
    #10;
    u2_s_axi_axaddr = 16'b1000_0000_0000_1000;
    `CHECK_EQ(u2_sub_idx, 2);
    `CHECK_TRUE(u2_word_aligned);
    `CHECK_EQ(u2_m_axi_axaddr, 14'h2000);

    // Test case 2: Address to subordinate 2, word aligned (duplicate pattern)
    #10;
    u2_s_axi_axaddr = 16'b0100_0000_0000_1000;
    `CHECK_EQ(u2_sub_idx, 2);
    `CHECK_TRUE(u2_word_aligned);
    `CHECK_EQ(u2_m_axi_axaddr, 14'h1000);

    // Test case 3: Address with byte offset
    #10;
    u2_s_axi_axaddr = 16'b1000_0000_0000_1111;
    `CHECK_EQ(u2_sub_idx, 3);
    `CHECK_FALSE(u2_word_aligned);
    `CHECK_EQ(u2_m_axi_axaddr, 14'h2003);

    // Test case 3: Address with byte offset (duplicate pattern)
    #10;
    u2_s_axi_axaddr = 16'b0100_0000_0000_1111;
    `CHECK_EQ(u2_sub_idx, 3);
    `CHECK_FALSE(u2_word_aligned);
    `CHECK_EQ(u2_m_axi_axaddr, 14'h1003);

    // Test case 4: Maximum address
    #10;
    u2_s_axi_axaddr = 16'hFFFF;
    `CHECK_EQ(u2_sub_idx, 3);
    `CHECK_FALSE(u2_word_aligned);
    `CHECK_EQ(u2_m_axi_axaddr, 14'h3FFF);
  endtask

  // Test UUT3: 2 subordinates, 8-bit data (single byte words)
  task automatic test_u3;
    // Test case 1: Address 0
    #10;
    u3_s_axi_axaddr = 0;
    `CHECK_EQ(u3_sub_idx, 0);
    `CHECK_TRUE(u3_word_aligned);
    `CHECK_EQ(u3_m_axi_axaddr, 0);

    // Test case 2: Address to subordinate 1
    #10;
    u3_s_axi_axaddr = 8'b1000_0001;
    `CHECK_EQ(u3_sub_idx, 1);
    `CHECK_TRUE(u3_word_aligned);
    `CHECK_EQ(u3_m_axi_axaddr, 7'b1000_000);

    // Test case 3: Maximum address
    #10;
    u3_s_axi_axaddr = 8'hFF;
    `CHECK_EQ(u3_sub_idx, 1);
    `CHECK_EQ(u3_m_axi_axaddr, '1);
    `CHECK_TRUE(u3_word_aligned);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_stripe_addr_tb);
  `TEST_CASE(test_u1);
  `TEST_CASE(test_u2);
  `TEST_CASE(test_u3);
  `TEST_SUITE_END();
endmodule
