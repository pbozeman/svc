`include "svc_tb_unit.sv"

`undef ASSERT_MSG

`define ASSERT_MSG(op, file, line, a, b) \
  test_msg_called = 1'b1;


module svc_tb_unit_asserts_tb;
  parameter NUM_CHECKS = 128;

  logic test_msg_called;

  task test_assert_eq();
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
          $display("assert_eq failed for %d %d", a, b);
        end
      end

      test_msg_called = 1'b0;
      `CHECK_EQ(a, a);
      assert (!test_msg_called)
      else begin
        $display("assert_eq failed for %d %d", a, a);
      end

      test_msg_called = 1'b0;
      `CHECK_EQ(a, 'bx);
      assert (test_msg_called)
      else begin
        $display("assert_eq failed for %d %d", a, 'bx);
      end

      test_msg_called = 1'b0;
      `CHECK_EQ(a, 'bz);
      assert (test_msg_called)
      else begin
        $display("assert_eq failed for %d %d", a, 'bz);
      end
    end

    test_msg_called = 1'b0;
    `CHECK_EQ('bx, 'bx);
    assert (!test_msg_called)
    else begin
      $display("assert_eq failed for %d %d", 'bx, 'bx);
    end

    test_msg_called = 1'b0;
    `CHECK_EQ('bz, 'bz);
    assert (!test_msg_called)
    else begin
      $display("assert_eq failed for %d %d", 'bz, 'bz);
    end

    test_msg_called = 1'b0;
    `CHECK_EQ('bx, 'bz);
    assert (test_msg_called)
    else begin
      $display("assert_eq failed for %d %d", 'bx, 'bz);
    end
  endtask

  task test_assert_neq();
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
          $display("assert_neq failed for %d %d", a, b);
        end
      end

      test_msg_called = 1'b0;
      `CHECK_NEQ(a, a);
      assert (test_msg_called)
      else begin
        $display("assert_neq failed for %d %d", a, a);
      end

      test_msg_called = 1'b0;
      `CHECK_NEQ(a, 'bx);
      assert (!test_msg_called)
      else begin
        $display("assert_neq failed for %d %d", a, 'bx);
      end

      test_msg_called = 1'b0;
      `CHECK_NEQ(a, 'bz);
      assert (!test_msg_called)
      else begin
        $display("assert_neq failed for %d %d", a, 'bz);
      end
    end

    test_msg_called = 1'b0;
    `CHECK_NEQ('bx, 'bx);
    assert (test_msg_called)
    else begin
      $display("assert_neq failed for %d %d", 'bx, 'bx);
    end

    test_msg_called = 1'b0;
    `CHECK_NEQ('bz, 'bz);
    assert (test_msg_called)
    else begin
      $display("assert_neq failed for %d %d", 'bz, 'bz);
    end

    test_msg_called = 1'b0;
    `CHECK_NEQ('bx, 'bz);
    assert (!test_msg_called)
    else begin
      $display("assert_neq failed for %d %d", 'bx, 'bz);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_tb_unit_asserts_tb);

  `TEST_CASE(test_assert_eq);
  `TEST_CASE(test_assert_neq);

  `TEST_SUITE_END();

endmodule
