`include "svc_unit.sv"
`include "svc_axi_stripe_ax.sv"

// The tb breaks from convention and has multiple UUTs since it's necessary to
// test various parameters of the addr calcs.
//
// There is no clock, so #10 was manually added between checks in order to
// visualize signals in gtkwave.

module svc_axi_stripe_ax_tbi;
  // UUT1: 2 subordinates, 8-bit addr, 16-bit data
  parameter U1_NUM_S = 2;
  parameter U1_AW = 8;
  parameter U1_DW = 16;
  parameter U1_SW = $clog2(U1_NUM_S);
  parameter U1_SAW = U1_AW - $clog2(U1_NUM_S);
  logic [   U1_AW-1:0]             u1_s_addr;
  logic [         7:0]             u1_s_len;
  logic [   U1_SW-1:0]             u1_start_idx;
  logic [   U1_SW-1:0]             u1_end_idx;
  logic                            u1_alignment_error;
  logic [U1_NUM_S-1:0]             u1_m_valid;
  logic [U1_NUM_S-1:0][U1_SAW-1:0] u1_m_addr;
  logic [U1_NUM_S-1:0][       7:0] u1_m_len;

  // UUT2: 4 subordinates, 32-bit data (4 bytes per word)
  parameter U2_NUM_S = 4;
  parameter U2_AW = 16;
  parameter U2_DW = 32;
  parameter U2_SW = $clog2(U2_NUM_S);
  parameter U2_SAW = U2_AW - $clog2(U2_NUM_S);
  logic [   U2_AW-1:0]             u2_s_addr;
  logic [         7:0]             u2_s_len;
  logic [   U2_SW-1:0]             u2_start_idx;
  logic [   U2_SW-1:0]             u2_end_idx;
  logic                            u2_alignment_error;
  logic [U2_NUM_S-1:0]             u2_m_valid;
  logic [U2_NUM_S-1:0][U2_SAW-1:0] u2_m_addr;
  logic [U2_NUM_S-1:0][       7:0] u2_m_len;

  // UUT3: 2 subordinates, 8-bit data (single byte words)
  parameter U3_NUM_S = 2;
  parameter U3_AW = 8;
  parameter U3_DW = 8;
  parameter U3_SW = $clog2(U3_NUM_S);
  parameter U3_SAW = U3_AW - $clog2(U3_NUM_S);
  logic [   U3_AW-1:0]             u3_s_addr;
  logic [         7:0]             u3_s_len;
  logic [   U3_SW-1:0]             u3_start_idx;
  logic [   U3_SW-1:0]             u3_end_idx;
  logic                            u3_alignment_error;
  logic [U3_NUM_S-1:0]             u3_m_valid;
  logic [U3_NUM_S-1:0][U3_SAW-1:0] u3_m_addr;
  logic [U3_NUM_S-1:0][       7:0] u3_m_len;

  svc_axi_stripe_ax #(
      .NUM_S         (U1_NUM_S),
      .AXI_ADDR_WIDTH(U1_AW),
      .AXI_DATA_WIDTH(U1_DW)
  ) uut1 (
      .s_addr         (u1_s_addr),
      .s_len          (u1_s_len),
      .start_idx      (u1_start_idx),
      .end_idx        (u1_end_idx),
      .alignment_error(u1_alignment_error),
      .m_valid        (u1_m_valid),
      .m_addr         (u1_m_addr),
      .m_len          (u1_m_len)
  );

  svc_axi_stripe_ax #(
      .NUM_S         (U2_NUM_S),
      .AXI_ADDR_WIDTH(U2_AW),
      .AXI_DATA_WIDTH(U2_DW)
  ) uut2 (
      .s_addr         (u2_s_addr),
      .s_len          (u2_s_len),
      .start_idx      (u2_start_idx),
      .end_idx        (u2_end_idx),
      .alignment_error(u2_alignment_error),
      .m_valid        (u2_m_valid),
      .m_addr         (u2_m_addr),
      .m_len          (u2_m_len)
  );

  svc_axi_stripe_ax #(
      .NUM_S         (U3_NUM_S),
      .AXI_ADDR_WIDTH(U3_AW),
      .AXI_DATA_WIDTH(U3_DW)
  ) uut3 (
      .s_addr         (u3_s_addr),
      .s_len          (u3_s_len),
      .start_idx      (u3_start_idx),
      .end_idx        (u3_end_idx),
      .alignment_error(u3_alignment_error),
      .m_valid        (u3_m_valid),
      .m_addr         (u3_m_addr),
      .m_len          (u3_m_len)
  );

  //
  // The naming convention is:
  // test_<subs>x<addr>x<data>_<stripes>_full_<remaining>_b_s_<start_idx>
  //

  //
  // Tests for UUT1 2 x 8 addr x 16 data
  //
  task automatic test_2x8x16_0_full_1_b_s_0;
    #10;
    u1_s_addr = 8'b1000_0000;
    u1_s_len  = 0;
    `CHECK_EQ(u1_start_idx, 0);
    `CHECK_EQ(u1_end_idx, 0);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b01);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_len[0], 0);
  endtask

  task automatic test_2x8x16_0_full_1_b_s_1;
    #10;
    u1_s_addr = 8'b1000_0010;
    u1_s_len  = 0;
    `CHECK_EQ(u1_start_idx, 1);
    `CHECK_EQ(u1_end_idx, 1);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b10);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_len[1], 0);
  endtask

  task automatic test_2x8x16_1_full_0_b_s_0;
    #10;
    u1_s_addr = 8'b1000_0000;
    u1_s_len  = 1;
    `CHECK_EQ(u1_start_idx, 0);
    `CHECK_EQ(u1_end_idx, 1);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b11);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_addr[1], 7'b100_0000);
    `CHECK_EQ(u1_m_len[0], 0);
    `CHECK_EQ(u1_m_len[1], 0);
  endtask

  task automatic test_2x8x16_1_full_0_b_s_1;
    #10;
    u1_s_addr = 8'b1000_0010;
    u1_s_len  = 1;
    `CHECK_EQ(u1_start_idx, 1);
    `CHECK_EQ(u1_end_idx, 0);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b11);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_addr[1], 7'b100_0000);
    `CHECK_EQ(u1_m_len[0], 0);
    `CHECK_EQ(u1_m_len[1], 0);
  endtask

  task automatic test_2x8x16_2_full_0_b_s_0;
    #10;
    u1_s_addr = 8'b1000_0000;
    u1_s_len  = 3;
    `CHECK_EQ(u1_start_idx, 0);
    `CHECK_EQ(u1_end_idx, 1);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b11);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_addr[1], 7'b100_0000);
    `CHECK_EQ(u1_m_len[0], 1);
    `CHECK_EQ(u1_m_len[1], 1);
  endtask

  task automatic test_2x8x16_2_full_0_b_s_1;
    #10;
    u1_s_addr = 8'b1000_0010;
    u1_s_len  = 3;
    `CHECK_EQ(u1_start_idx, 1);
    `CHECK_EQ(u1_end_idx, 0);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b11);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_addr[1], 7'b100_0000);
    `CHECK_EQ(u1_m_len[0], 1);
    `CHECK_EQ(u1_m_len[1], 1);
  endtask

  task automatic test_2x8x16_unaligned;
    #10;
    u1_s_addr = 8'b1000_0001;
    u1_s_len  = 0;
    `CHECK_EQ(u1_start_idx, 0);
    `CHECK_EQ(u1_end_idx, 0);
    `CHECK_TRUE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b01);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0001);
    `CHECK_EQ(u1_m_len[0], 0);
  endtask

  task automatic test_2x8x16_1_full_1_b_s_0;
    #10;
    u1_s_addr = 8'b1000_0000;
    u1_s_len  = 2;
    `CHECK_EQ(u1_start_idx, 0);
    `CHECK_EQ(u1_end_idx, 0);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b11);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_addr[1], 7'b100_0000);
    `CHECK_EQ(u1_m_len[0], 1);
    `CHECK_EQ(u1_m_len[1], 0);
  endtask

  task automatic test_2x8x16_1_full_1_b_s_1;
    #10;
    u1_s_addr = 8'b1000_0010;
    u1_s_len  = 2;
    `CHECK_EQ(u1_start_idx, 1);
    `CHECK_EQ(u1_end_idx, 1);
    `CHECK_FALSE(u1_alignment_error);
    `CHECK_EQ(u1_m_valid, 2'b11);
    `CHECK_EQ(u1_m_addr[0], 7'b100_0000);
    `CHECK_EQ(u1_m_addr[1], 7'b100_0000);
    `CHECK_EQ(u1_m_len[0], 0);
    `CHECK_EQ(u1_m_len[1], 1);
  endtask

  task automatic test_4x16x32_0_full_1_b_s_0;
    #10;
    u2_s_addr = 16'b1000_0000_0000_0000;
    u2_s_len  = 0;
    `CHECK_EQ(u2_start_idx, 0);
    `CHECK_EQ(u2_end_idx, 0);
    `CHECK_FALSE(u2_alignment_error);
    `CHECK_EQ(u2_m_valid, 4'b0001);
    `CHECK_EQ(u2_m_addr[0], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[0], 0);
  endtask

  task automatic test_4x16x32_0_full_1_b_s_2;
    #10;
    u2_s_addr = 16'b1000_0000_0000_1000;
    u2_s_len  = 0;
    `CHECK_EQ(u2_start_idx, 2);
    `CHECK_EQ(u2_end_idx, 2);
    `CHECK_FALSE(u2_alignment_error);
    `CHECK_EQ(u2_m_valid, 4'b0100);
    `CHECK_EQ(u2_m_addr[2], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[2], 0);
  endtask

  task automatic test_4x16x32_1_full_0_b_s_0;
    #10;
    u2_s_addr = 16'b1000_0000_0000_0000;
    u2_s_len  = 3;
    `CHECK_EQ(u2_start_idx, 0);
    `CHECK_EQ(u2_end_idx, 3);
    `CHECK_FALSE(u2_alignment_error);
    `CHECK_EQ(u2_m_valid, 4'b1111);
    `CHECK_EQ(u2_m_addr[0], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[0], 0);
    `CHECK_EQ(u2_m_addr[1], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[1], 0);
    `CHECK_EQ(u2_m_addr[2], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[2], 0);
    `CHECK_EQ(u2_m_addr[3], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[3], 0);
  endtask

  task automatic test_4x16x32_1_full_0_b_s_2;
    #10;
    u2_s_addr = 16'b1000_0000_0000_1000;
    u2_s_len  = 3;
    `CHECK_EQ(u2_start_idx, 2);
    `CHECK_EQ(u2_end_idx, 1);
    `CHECK_FALSE(u2_alignment_error);
    `CHECK_EQ(u2_m_addr[0], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[0], 0);
    `CHECK_EQ(u2_m_addr[1], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[1], 0);
    `CHECK_EQ(u2_m_addr[2], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[2], 0);
    `CHECK_EQ(u2_m_addr[3], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[3], 0);
  endtask

  task automatic test_4x16x32_2_full_3_b_s_3;
    #10;
    u2_s_addr = 16'b1000_0000_0000_1100;
    u2_s_len  = 10;
    `CHECK_EQ(u2_start_idx, 3);
    `CHECK_EQ(u2_end_idx, 1);
    `CHECK_FALSE(u2_alignment_error);
    `CHECK_EQ(u2_m_addr[0], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[0], 2);
    `CHECK_EQ(u2_m_addr[1], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[1], 2);
    `CHECK_EQ(u2_m_addr[2], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[2], 1);
    `CHECK_EQ(u2_m_addr[3], 14'b10_0000_0000_0000);
    `CHECK_EQ(u2_m_len[3], 2);
  endtask

  task automatic test_4x16x32_unaligned;
    #10;
    u2_s_addr = 16'b1000_0000_0000_0001;
    u2_s_len  = 0;
    `CHECK_EQ(u2_start_idx, 0);
    `CHECK_EQ(u2_end_idx, 0);
    `CHECK_TRUE(u2_alignment_error);
    `CHECK_EQ(u2_m_valid, 4'b0001);
    `CHECK_EQ(u2_m_addr[0], 14'b10_0000_0000_0001);
    `CHECK_EQ(u2_m_len[0], 0);

    u2_s_addr = 16'b1000_0000_0000_0010;
    u2_s_len  = 0;
    `CHECK_EQ(u2_start_idx, 0);
    `CHECK_EQ(u2_end_idx, 0);
    `CHECK_TRUE(u2_alignment_error);
    `CHECK_EQ(u2_m_valid, 4'b0001);
    `CHECK_EQ(u2_m_addr[0], 14'b10_0000_0000_0010);
    `CHECK_EQ(u2_m_len[0], 0);

    u2_s_addr = 16'b1000_0000_0000_0011;
    u2_s_len  = 0;
    `CHECK_EQ(u2_start_idx, 0);
    `CHECK_EQ(u2_end_idx, 0);
    `CHECK_TRUE(u2_alignment_error);
    `CHECK_EQ(u2_m_valid, 4'b0001);
    `CHECK_EQ(u2_m_addr[0], 14'b10_0000_0000_0011);
    `CHECK_EQ(u2_m_len[0], 0);
  endtask

  task automatic test_2x8x8_3_full_1_b_s_1;
    #10;
    u3_s_addr = 8'b1000_0011;
    u3_s_len  = 6;
    `CHECK_EQ(u3_start_idx, 1);
    `CHECK_EQ(u3_end_idx, 1);
    `CHECK_FALSE(u3_alignment_error);
    `CHECK_EQ(u3_m_valid, 2'b11);
    `CHECK_EQ(u3_m_addr[0], 7'b100_0001);
    `CHECK_EQ(u3_m_addr[1], 7'b100_0001);
    `CHECK_EQ(u3_m_len[0], 2);
    `CHECK_EQ(u3_m_len[1], 3);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_stripe_ax_tbi);

  // uut1
  `TEST_CASE(test_2x8x16_0_full_1_b_s_0);
  `TEST_CASE(test_2x8x16_0_full_1_b_s_1);
  `TEST_CASE(test_2x8x16_1_full_0_b_s_0);
  `TEST_CASE(test_2x8x16_1_full_0_b_s_1);
  `TEST_CASE(test_2x8x16_2_full_0_b_s_0);
  `TEST_CASE(test_2x8x16_2_full_0_b_s_1);
  `TEST_CASE(test_2x8x16_1_full_1_b_s_0);
  `TEST_CASE(test_2x8x16_1_full_1_b_s_1);
  `TEST_CASE(test_2x8x16_unaligned);

  // uut2
  `TEST_CASE(test_4x16x32_0_full_1_b_s_0);
  `TEST_CASE(test_4x16x32_0_full_1_b_s_2);
  `TEST_CASE(test_4x16x32_1_full_0_b_s_0);
  `TEST_CASE(test_4x16x32_1_full_0_b_s_2);
  `TEST_CASE(test_4x16x32_2_full_3_b_s_3);
  `TEST_CASE(test_4x16x32_unaligned);

  // uut3
  `TEST_CASE(test_2x8x8_3_full_1_b_s_1);

  `TEST_SUITE_END();
endmodule
