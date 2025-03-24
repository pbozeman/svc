`include "svc_unit.sv"
`include "svc_str_iter.sv"

module svc_str_iter_tb;
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

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      m_valid   <= 1'b0;
      s_ready   <= 1'b0;
      m_bin     <= 1'b0;
      m_bin_len <= 0;

      for (int i = 0; i < MAX_STR_LEN; i++) begin
        m_msg[8*i+:8] <= 8'h00;
      end
    end else begin
      if (m_valid && m_ready) begin
        m_valid <= 1'b0;
      end
    end
  end

  task automatic set_test_string(input string test_str);
    int str_len;

    str_len = test_str.len();

    if (str_len > MAX_STR_LEN - 1) begin
      $display("Warning: String too long, truncating to %0d characters",
               MAX_STR_LEN - 1);
      str_len = MAX_STR_LEN - 1;
    end

    for (int i = 0; i < MAX_STR_LEN; i++) begin
      m_msg[8*i+:8] = 8'h00;
    end

    for (int i = 0; i < str_len; i++) begin
      m_msg[8*i+:8] = test_str[i];
    end

    m_msg[8*str_len+:8] = 8'h00;
  endtask

  task automatic send_and_verify_string(input string test_str);
    int str_len;
    int char_idx;

    str_len = test_str.len();

    set_test_string(test_str);
    m_valid  = 1'b1;

    char_idx = 0;
    s_ready  = 1'b1;

    while (char_idx < str_len) begin
      `CHECK_WAIT_FOR(clk, s_valid, 16);
      `CHECK_EQ(s_char, test_str[char_idx]);
      `TICK(clk);
      char_idx++;
    end

    repeat (5) `TICK(clk);
    `CHECK_FALSE(s_valid);
  endtask

  task automatic test_with_backpressure(input string test_str);
    int str_len;
    int char_idx;

    str_len = test_str.len();

    set_test_string(test_str);
    m_valid  = 1'b1;

    char_idx = 0;
    s_ready  = 1'b0;

    while (char_idx < str_len) begin
      `CHECK_WAIT_FOR(clk, s_valid, 16);
      repeat (3) `TICK(clk);
      `CHECK_TRUE(s_valid);

      if (s_valid) begin
        `CHECK_EQ(s_char, test_str[char_idx]);
      end

      s_ready = 1'b1;
      `TICK(clk);
      s_ready = 1'b0;

      char_idx++;
    end

    s_ready = 1'b1;

    m_valid = 1'b0;
    repeat (5) `TICK(clk);
    `CHECK_FALSE(s_valid);
  endtask

  task automatic test_reset();
    `CHECK_FALSE(s_valid);
    `CHECK_FALSE(m_valid);
  endtask

  task automatic test_empty_string();
    set_test_string("");
    m_valid = 1'b1;
    s_ready = 1'b1;

    repeat (10) begin
      `CHECK_FALSE(s_valid);
    end
  endtask

  task automatic test_short_string();
    send_and_verify_string("Hello");
  endtask

  task automatic test_long_string();
    string long_str;
    long_str = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghij";

    if (long_str.len() > MAX_STR_LEN - 1) begin
      long_str = long_str.substr(0, MAX_STR_LEN - 2);
    end

    send_and_verify_string(long_str);
  endtask

  task automatic test_with_null_chars();
    string test_str;
    int    char_idx;

    for (int i = 0; i < MAX_STR_LEN; i++) begin
      m_msg[8*i+:8] = 8'h00;
    end

    m_msg[8*0+:8]  = "H";
    m_msg[8*1+:8]  = "e";
    m_msg[8*2+:8]  = "l";
    m_msg[8*3+:8]  = "l";
    m_msg[8*4+:8]  = "o";
    m_msg[8*5+:8]  = 8'h00;
    m_msg[8*6+:8]  = "W";
    m_msg[8*7+:8]  = "o";
    m_msg[8*8+:8]  = "r";
    m_msg[8*9+:8]  = "l";
    m_msg[8*10+:8] = "d";
    m_msg[8*11+:8] = 8'h00;

    m_valid        = 1'b1;
    s_ready        = 1'b1;

    test_str       = "Hello";
    char_idx       = 0;

    while (char_idx < 5) begin
      `CHECK_WAIT_FOR(clk, s_valid, 16);
      `CHECK_EQ(s_char, test_str[char_idx]);
      `TICK(clk);
      char_idx++;
    end

    m_valid = 1'b0;
    repeat (5) `TICK(clk);
    `CHECK_FALSE(s_valid);
  endtask

  task automatic test_backpressure_handling();
    test_with_backpressure("Test123");
  endtask

  task automatic test_sequential_messages();
    string first_msg;
    string second_msg;
    int    char_idx;

    first_msg  = "First";
    second_msg = "Second";

    set_test_string(first_msg);
    m_valid  = 1'b1;

    char_idx = 0;
    s_ready  = 1'b1;

    while (char_idx < first_msg.len()) begin
      `CHECK_WAIT_FOR(clk, s_valid, 16);
      `CHECK_EQ(s_char, first_msg[char_idx]);
      `TICK(clk);
      char_idx++;
    end

    `CHECK_WAIT_FOR(clk, s_ready, 16);
    set_test_string(second_msg);
    m_valid  = 1'b1;

    char_idx = 0;
    s_ready  = 1'b1;

    while (char_idx < second_msg.len()) begin
      `CHECK_WAIT_FOR(clk, s_valid, 16);
      `CHECK_EQ(s_char, second_msg[char_idx]);
      `TICK(clk);
      char_idx++;
    end

    m_valid = 1'b0;
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

  `TEST_SUITE_BEGIN(svc_str_iter_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_empty_string);
  `TEST_CASE(test_short_string);
  `TEST_CASE(test_long_string);
  `TEST_CASE(test_with_null_chars);
  `TEST_CASE(test_backpressure_handling);
  `TEST_CASE(test_sequential_messages);
  `TEST_CASE(test_bin_to_hex_2);
  `TEST_CASE(test_bin_to_hex_8);
  `TEST_SUITE_END();
endmodule
