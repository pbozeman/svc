`include "svc_unit.sv"

`include "svc_skidbuf.sv"

module svc_skidbuf_tb;
  parameter DATA_WIDTH = 8;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic                  s_valid;
  logic                  s_ready;
  logic [DATA_WIDTH-1:0] s_data;

  logic                  m_valid;
  logic                  m_ready;
  logic [DATA_WIDTH-1:0] m_data;

  logic                  auto_valid;

  svc_skidbuf #(
      .DATA_WIDTH(DATA_WIDTH),
      .OPT_OUTREG(0)
  ) uut (
      .clk    (clk),
      .rst_n  (rst_n),
      .s_valid(m_valid),
      .s_ready(m_ready),
      .s_data (m_data),
      .m_valid(s_valid),
      .m_ready(s_ready),
      .m_data (s_data)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_valid <= 0;
      m_data  <= 0;
      s_ready <= 0;
    end
  end

  always @(posedge clk) begin
    if (auto_valid) begin
      if (m_valid && m_ready) begin
        m_valid <= 0;
      end
    end
  end

  // Test basic data flow
  task test_basic_flow;
    begin
      s_ready    = 1;
      m_valid    = 1;
      m_data     = 8'hA5;
      auto_valid = 1;

      #1;
      `CHECK_EQ(s_data, 8'hA5);
      `CHECK_EQ(s_valid, 1'b1);

      @(posedge clk);
      #1;
      `CHECK_EQ(s_valid, 1'b0);
    end
  endtask

  // Test back pressure handling
  task test_backpressure;
    begin
      s_ready = 0;
      m_valid = 1;
      m_data  = 8'h55;
      @(posedge clk);
      #1;
      `CHECK_EQ(s_data, 8'h55);
      `CHECK_EQ(s_valid, 1'b1);
      `CHECK_EQ(m_ready, 1'b0);

      m_valid = 1;
      m_data  = 8'hAA;
      @(posedge clk);
      #1;
      `CHECK_EQ(s_data, 8'h55);
      `CHECK_EQ(m_ready, 1'b0);

      s_ready = 1;
      @(posedge clk);
      #1;
      `CHECK_EQ(s_data, 8'hAA);
      `CHECK_EQ(s_valid, 1'b1);
      `CHECK_EQ(m_ready, 1'b1);
    end
  endtask

  // Test continuous data flow
  task test_continious_flow;
    begin
      auto_valid = 0;
      s_ready    = 1;

      for (int i = 0; i < 4; i++) begin
        m_valid = 1;
        m_data  = DATA_WIDTH'(i);
        @(posedge clk);
        `CHECK_EQ(s_data, DATA_WIDTH'(i));
      end
    end
  endtask

  // Test reset behavior
  task test_reset;
    begin
      s_ready = 0;
      m_valid = 1;
      m_data  = 8'h42;
      @(posedge clk);
      #1;

      rst_n = 0;
      @(posedge clk);
      #1;
      `CHECK_EQ(s_valid, 1'b0);
      `CHECK_EQ(m_ready, 1'b1);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_skidbuf_tb);

  `TEST_CASE(test_basic_flow);
  `TEST_CASE(test_backpressure);
  `TEST_CASE(test_continious_flow);
  `TEST_CASE(test_reset);

  `TEST_SUITE_END();

endmodule
