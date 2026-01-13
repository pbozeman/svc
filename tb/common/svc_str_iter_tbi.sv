`include "svc_unit.sv"
`include "svc_str_iter.sv"

// This is a cleaned up tb from claude. It could use a real overhaul.

module svc_str_iter_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  localparam MAX_STR_LEN = 16;
  localparam MSG_WIDTH = MAX_STR_LEN * 8;

  logic                 m_valid;
  logic [MSG_WIDTH-1:0] m_msg;
  logic                 m_bin;
  logic [          3:0] m_bin_len;
  logic                 m_ready;

  logic                 s_valid;
  logic [          7:0] s_char;
  logic                 s_ready;

  svc_str_iter #(
      .MAX_STR_LEN(MAX_STR_LEN)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .s_valid  (m_valid),
      .s_msg    (m_msg),
      .s_bin    (m_bin),
      .s_bin_len(m_bin_len),
      .s_ready  (m_ready),

      .m_valid(s_valid),
      .m_char (s_char),
      .m_ready(s_ready)
  );

  logic auto_valid;

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_valid    <= 1'b0;
      s_ready    <= 1'b0;
      m_bin      <= 1'b0;
      m_bin_len  <= 0;

      auto_valid <= 1'b1;

      for (int i = 0; i < MAX_STR_LEN; i++) begin
        m_msg[8*i+:8] <= 8'h00;
      end
    end else begin
      if (m_valid && m_ready && auto_valid) begin
        m_valid <= 1'b0;
      end
    end
  end

  task automatic verify_string(input string test_str);
    int str_len;
    int char_idx;

    str_len  = test_str.len();
    m_valid  = 1'b1;

    char_idx = 0;
    s_ready  = 1'b1;

    while (char_idx < str_len) begin
      `CHECK_WAIT_FOR(clk, s_valid, 128);
      `CHECK_EQ(s_char, test_str[char_idx]);
      `TICK(clk);
      char_idx++;
    end

    repeat (5) `TICK(clk);
    `CHECK_FALSE(s_valid);
  endtask

  task automatic test_empty_string();
    m_msg   = "";
    m_valid = 1'b1;
    s_ready = 1'b1;

    repeat (10) begin
      `CHECK_FALSE(s_valid);
    end
  endtask

  task automatic test_short_string();
    m_msg = "Hello";
    verify_string("Hello");
  endtask

  task automatic test_backpressure_handling();
    int    char_idx;

    string str = "Test123";
    m_msg    = "Test123";

    m_valid  = 1'b1;

    char_idx = 0;
    s_ready  = 1'b0;

    while (char_idx < str.len()) begin
      `CHECK_WAIT_FOR(clk, s_valid, 128);
      repeat (3) `TICK(clk);
      `CHECK_TRUE(s_valid);

      if (s_valid) begin
        `CHECK_EQ(s_char, str[char_idx]);
      end

      s_ready = 1'b1;
      `TICK(clk);
      s_ready = 1'b0;

      char_idx++;
    end

    s_ready = 1'b1;

    repeat (5) `TICK(clk);
    `CHECK_FALSE(s_valid);
  endtask

  task automatic test_sequential_messages();
    string first_msg;
    string second_msg;
    int    char_idx;

    auto_valid = 1'b0;

    first_msg  = "First";
    second_msg = "Second";

    m_msg      = "First";
    m_valid    = 1'b1;

    char_idx   = 0;
    s_ready    = 1'b1;

    while (char_idx < first_msg.len()) begin
      `CHECK_WAIT_FOR(clk, s_valid, 128);
      `CHECK_EQ(s_char, first_msg[char_idx]);
      `TICK(clk);
      char_idx++;
    end

    `CHECK_WAIT_FOR(clk, m_ready, 16);
    `TICK(clk);
    m_msg      = "Second";

    char_idx   = 0;
    s_ready    = 1'b1;
    auto_valid = 1'b1;

    while (char_idx < second_msg.len()) begin
      `CHECK_WAIT_FOR(clk, s_valid, 128);
      `CHECK_EQ(s_char, second_msg[char_idx]);
      `TICK(clk);
      char_idx++;
    end


    repeat (5) `TICK(clk);
    `CHECK_FALSE(s_valid);
  endtask

  task automatic test_bin_to_hex_2();
    string expected = "cafe";
    int    char_idx;

    s_ready   = 1'b1;

    m_valid   = 1'b1;
    m_msg     = MSG_WIDTH'(16'hCAFE);
    m_bin     = 1'b1;
    m_bin_len = 2;
    `TICK(clk);

    char_idx = 0;
    while (char_idx < expected.len()) begin
      `CHECK_WAIT_FOR(clk, s_valid, 16);
      `CHECK_EQ(s_char, expected[char_idx]);
      `TICK(clk);
      char_idx++;
    end
  endtask

  task automatic test_bin_to_hex_8();
    string expected = "cafe0000babef00d";
    int    char_idx;

    s_ready   = 1'b1;

    m_valid   = 1'b1;
    m_msg     = MSG_WIDTH'(64'hCAFE0000BABEF00D);
    m_bin     = 1'b1;
    m_bin_len = 8;
    `TICK(clk);

    char_idx = 0;
    while (char_idx < expected.len()) begin
      `CHECK_WAIT_FOR(clk, s_valid, 16);
      `CHECK_EQ(s_char, expected[char_idx]);
      `TICK(clk);
      char_idx++;
    end
  endtask

  `TEST_SUITE_BEGIN(svc_str_iter_tbi);
  `TEST_CASE(test_empty_string);
  `TEST_CASE(test_short_string);
  `TEST_CASE(test_backpressure_handling);
  `TEST_CASE(test_sequential_messages);
  `TEST_CASE(test_bin_to_hex_2);
  `TEST_CASE(test_bin_to_hex_8);
  `TEST_SUITE_END();
endmodule
