`include "svc_unit.sv"

`undef CHECK_MSG_1
`undef CHECK_MSG_2

`define CHECK_MSG_1(op, file, line, a) \
  test_msg_called = 1'b1;

`define CHECK_MSG_2(op, file, line, a, b) \
  test_msg_called = 1'b1;

module svc_unit_check_tb;
  parameter NUM_CHECKS = 128;

  logic       test_msg_called;

  int         int_true = 1;
  int         int_false = 0;
  logic [2:0] bits_true = 1;
  logic [2:0] bits_false = 0;

  task test_check_true();
    test_msg_called = 1'b0;
    `CHECK_TRUE('bx);
    assert (test_msg_called)
    else begin
      $display("check_true failed for %d", 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_TRUE('bz);
    assert (test_msg_called)
    else begin
      $display("check_true failed for %d", 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_TRUE(int_true);
    assert (!test_msg_called)
    else begin
      $display("check_true failed for %d", int_true);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_TRUE(int_false);
    assert (test_msg_called)
    else begin
      $display("check_true failed for %d", int_false);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_TRUE(bits_true);
    assert (!test_msg_called)
    else begin
      $display("check_true failed for %d", bits_true);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_TRUE(bits_false);
    assert (test_msg_called)
    else begin
      $display("check_true failed for %d", bits_false);
      $fatal();
    end
  endtask

  task test_check_false();
    test_msg_called = 1'b0;
    `CHECK_FALSE('bx);
    assert (test_msg_called)
    else begin
      $display("check_false failed for %d", 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_FALSE('bz);
    assert (test_msg_called)
    else begin
      $display("check_false failed for %d", 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_FALSE(int_true);
    assert (test_msg_called)
    else begin
      $display("check_false failed for %d", int_true);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_FALSE(int_false);
    assert (!test_msg_called)
    else begin
      $display("check_false failed for %d", int_false);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_FALSE(bits_true);
    assert (test_msg_called)
    else begin
      $display("check_false failed for %d", bits_true);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_FALSE(bits_false);
    assert (!test_msg_called)
    else begin
      $display("check_false failed for %d", bits_false);
      $fatal();
    end
  endtask

  task test_check_eq();
    int a;
    int b;

    for (int i = 0; i < NUM_CHECKS; i++) begin
      a               = $random();
      b               = $random();

      test_msg_called = 1'b0;
      `CHECK_EQ(a, b);
      if (a === b) begin
        assert (!test_msg_called)
        else begin
          $display("check_eq failed for %d %d", a, b);
          $fatal();
        end
      end

      test_msg_called = 1'b0;
      `CHECK_EQ(a, a);
      assert (!test_msg_called)
      else begin
        $display("check_eq failed for %d %d", a, a);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_EQ(a, 'bx);
      assert (test_msg_called)
      else begin
        $display("check_eq failed for %d %d", a, 'bx);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_EQ(a, 'bz);
      assert (test_msg_called)
      else begin
        $display("check_eq failed for %d %d", a, 'bz);
        $fatal();
      end
    end

    test_msg_called = 1'b0;
    `CHECK_EQ('bx, 'bx);
    assert (!test_msg_called)
    else begin
      $display("check_eq failed for %d %d", 'bx, 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_EQ('bz, 'bz);
    assert (!test_msg_called)
    else begin
      $display("check_eq failed for %d %d", 'bz, 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_EQ('bx, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_eq failed for %d %d", 'bx, 'bz);
      $fatal();
    end
  endtask

  task test_check_neq();
    int a;
    int b;

    for (int i = 0; i < NUM_CHECKS; i++) begin
      a               = $random();
      b               = $random();

      test_msg_called = 1'b0;
      `CHECK_NEQ(a, b);
      if (a !== b) begin
        assert (!test_msg_called)
        else begin
          $display("check_neq failed for %d %d", a, b);
          $fatal();
        end
      end

      test_msg_called = 1'b0;
      `CHECK_NEQ(a, a);
      assert (test_msg_called)
      else begin
        $display("check_neq failed for %d %d", a, a);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_NEQ(a, 'bx);
      assert (!test_msg_called)
      else begin
        $display("check_neq failed for %d %d", a, 'bx);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_NEQ(a, 'bz);
      assert (!test_msg_called)
      else begin
        $display("check_neq failed for %d %d", a, 'bz);
        $fatal();
      end
    end

    test_msg_called = 1'b0;
    `CHECK_NEQ('bx, 'bx);
    assert (test_msg_called)
    else begin
      $display("check_neq failed for %d %d", 'bx, 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_NEQ('bz, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_neq failed for %d %d", 'bz, 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_NEQ('bx, 'bz);
    assert (!test_msg_called)
    else begin
      $display("check_neq failed for %d %d", 'bx, 'bz);
      $fatal();
    end
  endtask

  task test_check_lt();
    int a;
    int b;

    for (int i = 0; i < NUM_CHECKS; i++) begin
      a               = $random();
      b               = $random();

      test_msg_called = 1'b0;
      `CHECK_LT(a, b);
      if (a >= b) begin
        assert (test_msg_called)
        else begin
          $display("check_lt failed for %d %d", a, b);
          $fatal();
        end
      end

      test_msg_called = 1'b0;
      `CHECK_LT(a, a);
      assert (test_msg_called)
      else begin
        $display("check_lt failed for %d %d", a, a);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_LT(a, 'bx);
      assert (test_msg_called)
      else begin
        $display("check_lt failed for %d %d", a, 'bx);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_LT(a, 'bz);
      assert (test_msg_called)
      else begin
        $display("check_lt failed for %d %d", a, 'bz);
        $fatal();
      end
    end

    test_msg_called = 1'b0;
    `CHECK_LT('bx, 'bx);
    assert (test_msg_called)
    else begin
      $display("check_lt failed for %d %d", 'bx, 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_LT('bz, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_lt failed for %d %d", 'bz, 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_LT('bx, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_lt failed for %d %d", 'bx, 'bz);
      $fatal();
    end
  endtask

  task test_check_lte();
    int a;
    int b;

    for (int i = 0; i < NUM_CHECKS; i++) begin
      a               = $random();
      b               = $random();

      test_msg_called = 1'b0;
      `CHECK_LTE(a, b);
      if (a > b) begin
        assert (test_msg_called)
        else begin
          $display("check_lte failed for %d %d", a, b);
          $fatal();
        end
      end

      test_msg_called = 1'b0;
      `CHECK_LTE(a, a);
      assert (!test_msg_called)
      else begin
        $display("check_lte failed for %d %d", a, a);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_LTE(a, 'bx);
      assert (test_msg_called)
      else begin
        $display("check_lte failed for %d %d", a, 'bx);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_LTE(a, 'bz);
      assert (test_msg_called)
      else begin
        $display("check_lte failed for %d %d", a, 'bz);
        $fatal();
      end
    end

    test_msg_called = 1'b0;
    `CHECK_LTE('bx, 'bx);
    assert (test_msg_called)
    else begin
      $display("check_lte failed for %d %d", 'bx, 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_LTE('bz, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_lte failed for %d %d", 'bz, 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_LTE('bx, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_lte failed for %d %d", 'bx, 'bz);
      $fatal();
    end
  endtask

  task test_check_gt();
    int a;
    int b;

    for (int i = 0; i < NUM_CHECKS; i++) begin
      a               = $random();
      b               = $random();

      test_msg_called = 1'b0;
      `CHECK_GT(a, b);
      if (a <= b) begin
        assert (test_msg_called)
        else begin
          $display("check_gt failed for %d %d", a, b);
          $fatal();
        end
      end

      test_msg_called = 1'b0;
      `CHECK_GT(a, a);
      assert (test_msg_called)
      else begin
        $display("check_gt failed for %d %d", a, a);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_GT(a, 'bx);
      assert (test_msg_called)
      else begin
        $display("check_gt failed for %d %d", a, 'bx);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_GT(a, 'bz);
      assert (test_msg_called)
      else begin
        $display("check_gt failed for %d %d", a, 'bz);
        $fatal();
      end
    end

    test_msg_called = 1'b0;
    `CHECK_GT('bx, 'bx);
    assert (test_msg_called)
    else begin
      $display("check_gt failed for %d %d", 'bx, 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_GT('bz, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_gt failed for %d %d", 'bz, 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_GT('bx, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_gt failed for %d %d", 'bx, 'bz);
      $fatal();
    end
  endtask

  task test_check_gte();
    int a;
    int b;

    for (int i = 0; i < NUM_CHECKS; i++) begin
      a               = $random();
      b               = $random();

      test_msg_called = 1'b0;
      `CHECK_GTE(a, b);
      if (a < b) begin
        assert (test_msg_called)
        else begin
          $display("check_gte failed for %d %d", a, b);
          $fatal();
        end
      end

      test_msg_called = 1'b0;
      `CHECK_GTE(a, a);
      assert (!test_msg_called)
      else begin
        $display("check_gte failed for %d %d", a, a);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_GTE(a, 'bx);
      assert (test_msg_called)
      else begin
        $display("check_gte failed for %d %d", a, 'bx);
        $fatal();
      end

      test_msg_called = 1'b0;
      `CHECK_GTE(a, 'bz);
      assert (test_msg_called)
      else begin
        $display("check_gte failed for %d %d", a, 'bz);
        $fatal();
      end
    end

    test_msg_called = 1'b0;
    `CHECK_GTE('bx, 'bx);
    assert (test_msg_called)
    else begin
      $display("check_gte failed for %d %d", 'bx, 'bx);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_GTE('bz, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_gte failed for %d %d", 'bz, 'bz);
      $fatal();
    end

    test_msg_called = 1'b0;
    `CHECK_GTE('bx, 'bz);
    assert (test_msg_called)
    else begin
      $display("check_gte failed for %d %d", 'bx, 'bz);
      $fatal();
    end
  endtask

  `TEST_SUITE_BEGIN(svc_unit_check_tb);

  `TEST_CASE(test_check_true);
  `TEST_CASE(test_check_false);
  `TEST_CASE(test_check_eq);
  `TEST_CASE(test_check_neq);
  `TEST_CASE(test_check_lt);
  `TEST_CASE(test_check_lte);
  `TEST_CASE(test_check_gt);
  `TEST_CASE(test_check_gte);

  `TEST_SUITE_END();

endmodule
