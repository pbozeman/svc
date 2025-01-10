`include "svc_unit.sv"

`include "svc_axi_burst_iter_ax.sv"

// This is just a quick smoke test. The formal verifier is more comprehensive.

module svc_axi_burst_iter_ax_tb;
  parameter AW = 16;
  parameter IW = 4;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic          m_valid;
  logic [AW-1:0] m_addr;
  logic [IW-1:0] m_id;
  logic [   7:0] m_len;
  logic [   2:0] m_size;
  logic [   1:0] m_burst;
  logic          m_ready;

  logic          s_valid;
  logic [AW-1:0] s_addr;
  logic [IW-1:0] s_id;
  logic [   7:0] s_len;
  logic [   2:0] s_size;
  logic [   1:0] s_burst;
  logic          s_last;
  logic          s_ready;

  svc_axi_burst_iter_ax #(
      .AXI_ADDR_WIDTH(AW),
      .AXI_ID_WIDTH  (IW)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_valid(m_valid),
      .s_addr (m_addr),
      .s_id   (m_id),
      .s_len  (m_len),
      .s_size (m_size),
      .s_burst(m_burst),
      .s_ready(m_ready),

      .m_valid(s_valid),
      .m_addr (s_addr),
      .m_id   (s_id),
      .m_len  (s_len),
      .m_size (s_size),
      .m_burst(s_burst),
      .m_last (s_last),
      .m_ready(s_ready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_valid <= 1'b0;
      m_addr  <= 0;
      m_len   <= 8'h0;
      m_size  <= 3'h0;
      m_burst <= 2'h0;
      m_id    <= 0;

      s_ready <= 1'b0;
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(s_valid);
  endtask

  always_ff @(posedge clk) begin
    if (m_valid && m_ready) begin
      m_valid <= 1'b0;
    end
  end

  // Basic smoke test
  task automatic test_basic;
    begin
      logic [AW-1:0] addr = AW'(16'hA000);

      // setup the burst
      // length 4, INCR, 2 byte stride
      m_valid = 1'b1;
      m_addr  = addr;
      m_id    = 4'hD;
      m_len   = 8'h03;
      m_burst = 2'b01;
      m_size  = 3'b001;

      s_ready = 1'b1;

      `CHECK_TRUE(m_valid && m_ready);
      for (int i = 0; i < 4; i++) begin
        `CHECK_TRUE(s_valid && s_ready);
        `CHECK_EQ(s_addr, addr + AW'(i * 2));
        `CHECK_EQ(s_id, 4'hD);
        `CHECK_EQ(s_len, 0);
        `CHECK_EQ(s_size, 3'b001);
        `CHECK_EQ(s_burst, 2'b00);
        `CHECK_TRUE(s_last || i < 3);

        `TICK(clk);
      end

      `CHECK_FALSE(s_valid);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_axi_burst_iter_ax_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_basic);
  `TEST_SUITE_END();

endmodule
