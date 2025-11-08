//
// Zmmul extension test case list
//
// Additional tests for Zmmul multiply extension.
// These are included alongside standard RV32I tests.
//

`TEST_CASE(test_mul_basic);
`TEST_CASE(test_mulh_basic);
`TEST_CASE(test_mulhsu_basic);
`TEST_CASE(test_mulhu_basic);
`TEST_CASE(test_mul_raw_dependency);
`TEST_CASE(test_mul_chained_dependencies);
`TEST_CASE(test_mul_mixed_ops);
`TEST_CASE(test_mul_zero);
`TEST_CASE(test_mul_large_values);
