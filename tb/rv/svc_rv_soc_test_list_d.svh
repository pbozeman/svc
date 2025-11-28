//
// Division/remainder extension test case list
//
// Additional tests for division and remainder instructions.
// These are included alongside standard RV32I and multiply tests.
//

`TEST_CASE(test_div_basic);
`TEST_CASE(test_divu_basic);
`TEST_CASE(test_rem_basic);
`TEST_CASE(test_remu_basic);
`TEST_CASE(test_div_by_zero);
`TEST_CASE(test_div_overflow);
`TEST_CASE(test_div_raw_dependency);
`TEST_CASE(test_div_chained_dependencies);
`TEST_CASE(test_div_mixed_ops);
`TEST_CASE(test_mul_div_mixed);
`TEST_CASE(test_store_div_mmio_write);
`TEST_CASE(test_load_div_mmio_read);
`TEST_CASE(test_load_div_use);
`TEST_CASE(test_misaligned_load_div_trap);
`TEST_CASE(test_div_instret_count);
