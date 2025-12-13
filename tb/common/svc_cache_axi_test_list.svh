//
// Test case list for svc_cache_axi
//

`TEST_CASE(test_reset);
`TEST_CASE(test_read_miss);
`TEST_CASE(test_read_miss_data);
`TEST_CASE(test_cache_hit);
`TEST_CASE(test_stress);
`TEST_CASE(test_write_miss);
`TEST_CASE(test_write_hit);
`TEST_CASE(test_write_strobe);
`TEST_CASE(test_read_after_write_hit);
`TEST_CASE(test_read_after_write_miss);
`TEST_CASE(test_read_during_write_diff_line);
`TEST_CASE(test_read_during_write_same_line);
