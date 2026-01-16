//
// Floating-point extension test case list
//
// Additional tests for RV32F floating-point extension.
// These are included alongside standard RV32I tests.
//

// Load/Store tests
`TEST_CASE(test_flw_basic);
`TEST_CASE(test_fsw_basic);
`TEST_CASE(test_flw_offset);

// Basic arithmetic
`TEST_CASE(test_fadd_basic);
`TEST_CASE(test_fsub_basic);
`TEST_CASE(test_fmul_basic);
`TEST_CASE(test_fdiv_basic);
`TEST_CASE(test_fsqrt_basic);

// FMA
`TEST_CASE(test_fmadd_basic);
`TEST_CASE(test_fmsub_basic);

// Comparisons
`TEST_CASE(test_feq_basic);
`TEST_CASE(test_flt_basic);
`TEST_CASE(test_fminmax_basic);

// Move/Convert
`TEST_CASE(test_fmv_w_x_basic);
`TEST_CASE(test_fmv_x_w_basic);
`TEST_CASE(test_fcvt_w_s_basic);
`TEST_CASE(test_fcvt_s_w_basic);

// Sign manipulation
`TEST_CASE(test_fsgnj_basic);

// Hazard/Forwarding tests
`TEST_CASE(test_fp_raw_hazard);
`TEST_CASE(test_fp_chain);
`TEST_CASE(test_fp_load_use);
`TEST_CASE(test_fp_mixed_int_fp);

// RoPE-style FMUL->FSUB pattern (regression for cache+FPU hazard)
`TEST_CASE(test_fp_fmul_fsub_pattern);
`TEST_CASE(test_fp_fmul_fsub_loop);

// CSR tests
`TEST_CASE(test_fp_csr_frm);
`TEST_CASE(test_fp_csr_fflags);
`TEST_CASE(test_fp_csr_fcsr);
