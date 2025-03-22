`include "svc_unit.sv"
`include "svc_str.sv"

module svc_str_tb;
  logic [8*SVC_STR_MAX_LEN-1:0] str_out;
  logic [8*SVC_STR_MAX_LEN-1:0] literal;
  int                           length;

  task automatic test_basic_string();
    literal = "hello";
    length  = 5;

    svc_str_init(str_out, literal, length);

    `CHECK_EQ(str_out[7:0], 8'h68);
    `CHECK_EQ(str_out[15:8], 8'h65);
    `CHECK_EQ(str_out[23:16], 8'h6C);
    `CHECK_EQ(str_out[31:24], 8'h6C);
    `CHECK_EQ(str_out[39:32], 8'h6F);

    for (int i = 5; i < SVC_STR_MAX_LEN; i++) begin
      `CHECK_EQ(str_out[8*i+:8], 8'h00);
    end
  endtask

  task automatic test_empty_string();
    literal = "";
    length  = 0;

    svc_str_init(str_out, literal, length);

    for (int i = 0; i < SVC_STR_MAX_LEN; i++) begin
      `CHECK_EQ(str_out[8*i+:8], 8'h00);
    end
  endtask

  task automatic test_macro_usage();
    str_out = '0;
    `SVC_STR_INIT(str_out, "test");

    `CHECK_EQ(str_out[7:0], 8'h74);
    `CHECK_EQ(str_out[15:8], 8'h65);
    `CHECK_EQ(str_out[23:16], 8'h73);
    `CHECK_EQ(str_out[31:24], 8'h74);

    for (int i = 4; i < SVC_STR_MAX_LEN; i++) begin
      `CHECK_EQ(str_out[8*i+:8], 8'h00);
    end
  endtask


  task automatic test_long_string();
    literal = "This is a longer test string to verify proper handling";
    length  = 54;

    svc_str_init(str_out, literal, length);

    `CHECK_EQ(str_out[7:0], 8'h54);
    `CHECK_EQ(str_out[15:8], 8'h68);
    `CHECK_EQ(str_out[23:16], 8'h69);

    // ... skip the middle

    `CHECK_EQ(str_out[431:424], 8'h67);

    for (int i = 54; i < SVC_STR_MAX_LEN; i++) begin
      `CHECK_EQ(str_out[8*i+:8], 8'h00);
    end
  endtask

  task automatic test_partial_update();
    `SVC_STR_INIT(str_out, "initial");

    // update with a shorter string
    svc_str_init(str_out, "new", 3);

    // Check new string characters
    `CHECK_EQ(str_out[7:0], 8'h6E);
    `CHECK_EQ(str_out[15:8], 8'h65);
    `CHECK_EQ(str_out[23:16], 8'h77);

    for (int i = 3; i < SVC_STR_MAX_LEN; i++) begin
      `CHECK_EQ(str_out[8*i+:8], 8'h00);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_str_tb);
  `TEST_CASE(test_basic_string);
  `TEST_CASE(test_empty_string);
  `TEST_CASE(test_macro_usage);
  `TEST_CASE(test_long_string);
  `TEST_CASE(test_partial_update);
  `TEST_SUITE_END();
endmodule
