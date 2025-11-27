//
// Test case list
//

// Basic tests
`TEST_CASE(test_ebreak);

// Tests with no register dependencies (all read from x0)
`TEST_CASE(test_addi_from_x0);
`TEST_CASE(test_logical_from_x0);
`TEST_CASE(test_shift_from_x0);
`TEST_CASE(test_compare_from_x0);
`TEST_CASE(test_r_type_from_x0);
`TEST_CASE(test_x0_immutable);

// I-type tests with register dependencies
`TEST_CASE(test_addi);
`TEST_CASE(test_i_type_logical);
`TEST_CASE(test_i_type_compare);
`TEST_CASE(test_i_type_shift);

// R-type tests with register dependencies
`TEST_CASE(test_r_type_arithmetic);
`TEST_CASE(test_r_type_logical);
`TEST_CASE(test_r_type_shift);
`TEST_CASE(test_r_type_compare);

// Read-after-write dependency tests
`TEST_CASE(test_raw_dependency);

// Dependency stress test - deep chains that stress forwarding/stalls
`TEST_CASE(test_chained_dependencies);

// Jump tests (JAL/JALR)
`TEST_CASE(test_jal_simple);
`TEST_CASE(test_jalr_simple);
`TEST_CASE(test_jal_short);
`TEST_CASE(test_jalr_lsb_clear);
`TEST_CASE(test_jalr_with_base_register);
`TEST_CASE(test_call_return_pattern);
`TEST_CASE(test_jal_misaligned);
`TEST_CASE(test_jalr_misaligned);
`TEST_CASE(test_jal_misaligned_backward);

// Pipeline stress tests - validate instruction flushing on control flow
`TEST_CASE(test_jal_forward_pipeline);
`TEST_CASE(test_jal_short_forward_pipeline);
`TEST_CASE(test_jalr_forward_pipeline);
`TEST_CASE(test_ras_jalr_return_flush);
`TEST_CASE(test_jalr_mispred_ex_flush);

// jal/jalr result forwarding
`TEST_CASE(test_jal_forwarding);
`TEST_CASE(test_jalr_forwarding);
`TEST_CASE(test_jalr_base_forwarding);

// BTB JAL misprediction test
`TEST_CASE(test_jal_btb_not_taken);

// Branch tests
`TEST_CASE(test_beq_taken_forward);
`TEST_CASE(test_beq_not_taken);
`TEST_CASE(test_bne_taken_backward);
`TEST_CASE(test_bne_not_taken);
`TEST_CASE(test_blt_taken_signed);
`TEST_CASE(test_blt_not_taken_signed);
`TEST_CASE(test_bge_taken_signed);
`TEST_CASE(test_bge_not_taken_signed);
`TEST_CASE(test_bge_equal);
`TEST_CASE(test_bltu_taken_unsigned);
`TEST_CASE(test_bltu_not_taken_unsigned);
`TEST_CASE(test_bgeu_taken_unsigned);
`TEST_CASE(test_bgeu_not_taken_unsigned);
`TEST_CASE(test_bgeu_zero);
`TEST_CASE(test_branch_loop);
`TEST_CASE(test_beq_misaligned);
`TEST_CASE(test_bne_misaligned);
`TEST_CASE(test_blt_misaligned_backward);

// LUI and AUIPC tests
`TEST_CASE(test_lui_basic);
`TEST_CASE(test_lui_zero);
`TEST_CASE(test_lui_negative);
`TEST_CASE(test_auipc_basic);
`TEST_CASE(test_auipc_zero);
`TEST_CASE(test_auipc_negative);
`TEST_CASE(test_auipc_forwarding);
`TEST_CASE(test_li_pseudo_small);

// LI pseudo-instruction for large values has LUI+ADDI hazard
`TEST_CASE(test_li_pseudo_large);

// LUI+ADDI combination has data hazard
`TEST_CASE(test_lui_addi_combination);

// Load/store tests - word operations supported
`TEST_CASE(test_lw_sw_basic);
`TEST_CASE(test_sw_lw_forwarding);
`TEST_CASE(test_sw_lw_different_regs);
`TEST_CASE(test_load_use_hazard);
`TEST_CASE(test_lw_sw_multiple);

// Byte/halfword operations
`TEST_CASE(test_lb_basic);
`TEST_CASE(test_lbu_basic);
`TEST_CASE(test_lh_basic);
`TEST_CASE(test_lhu_basic);
`TEST_CASE(test_sb_basic);
`TEST_CASE(test_sh_basic);
`TEST_CASE(test_sb_partial_word);
`TEST_CASE(test_sh_partial_word);
`TEST_CASE(test_mixed_byte_halfword_word);

// Alignment
`TEST_CASE(test_word_aligned_mem_addr);

// Trap tests
`TEST_CASE(test_trap_misaligned_sh);
`TEST_CASE(test_trap_misaligned_lh);

// CSR tests (Zicntr - performance counters)
`TEST_CASE(test_rdcycle);
`TEST_CASE(test_rdcycleh);
`TEST_CASE(test_rdinstret);
`TEST_CASE(test_rdinstreth);
`TEST_CASE(test_csr_cycle_increments);
`TEST_CASE(test_csr_instret_increments);

// CPI micro-benchmarks - characterize pipeline performance
`TEST_CASE(test_cpi_alu_independent);
`TEST_CASE(test_cpi_alu_chain);
`TEST_CASE(test_cpi_branch_taken);
`TEST_CASE(test_cpi_branch_not_taken);
`TEST_CASE(test_cpi_load_use);
`TEST_CASE(test_cpi_mixed_alu);
`TEST_CASE(test_cpi_function_calls);

// Memory-mapped I/O tests
`TEST_CASE(test_mmio_write_basic);
`TEST_CASE(test_mmio_read_basic);
`TEST_CASE(test_mmio_read_write_sequence);
`TEST_CASE(test_mmio_byte_ops);
`TEST_CASE(test_mmio_isolation);

// Smoke tests
`TEST_CASE(test_fib12);
`TEST_CASE(test_fib100);
`TEST_CASE(test_bubble_sort);

// BTB stress test - forward taken branch (anti-BTFNT)
`TEST_CASE(test_forward_taken_loop);
