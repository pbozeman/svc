//
// Floating-point extension test tasks
//
// These tests verify RV32F floating-point instructions.
// Used by testbenches with EXT_F=1.
//

//
// IEEE 754 single-precision constants
//
localparam logic [31:0] FP_ZERO = 32'h00000000;  // 0.0
localparam logic [31:0] FP_ONE = 32'h3F800000;  // 1.0
localparam logic [31:0] FP_TWO = 32'h40000000;  // 2.0
localparam logic [31:0] FP_THREE = 32'h40400000;  // 3.0
localparam logic [31:0] FP_FOUR = 32'h40800000;  // 4.0
localparam logic [31:0] FP_FIVE = 32'h40A00000;  // 5.0
localparam logic [31:0] FP_SIX = 32'h40C00000;  // 6.0
localparam logic [31:0] FP_SEVEN = 32'h40E00000;  // 7.0
localparam logic [31:0] FP_EIGHT = 32'h41000000;  // 8.0
localparam logic [31:0] FP_NEG_ONE = 32'hBF800000;  // -1.0
localparam logic [31:0] FP_NEG_THREE = 32'hC0400000;  // -3.0
localparam logic [31:0] FP_HALF = 32'h3F000000;  // 0.5

//
// FP register file access macro
//
`define FP_REG(i) uut.cpu.stage_id.g_fp_regfile.fp_regfile.regs[i]

//
// FP CSR access macro
//
`define FP_CSR_FFLAGS uut.cpu.stage_ex.g_fp_ext.fp_csr.fflags
`define FP_CSR_FRM uut.cpu.stage_ex.g_fp_ext.fp_csr.frm_reg

//
// Initialize FP regfile to 0 in simulation
// (Removed: was causing issues with Verilator)
//
// always_ff @(posedge clk) begin
//   if (!rst_n) begin
//     for (int i = 0; i < 32; i++) begin
//       `FP_REG(i) <= '0;
//     end
//   end
// end

// ============================================================================
// Basic Load/Store Tests
// ============================================================================

//
// Test: FLW - load float from memory
//
// Memory layout: IMEM at 0x0000-0x0FFF, DMEM at 0x1000-0x1FFF
// DMEM word 0 is at address 0x1000
//
task automatic test_flw_basic;
  // Store test value in data memory (word 0)
  `DMEM_WR(0, FP_THREE);

  // x1 = 0x1000 (DMEM base address)
  LUI(x1, 32'h00001000);

  // f1 = mem[x1]
  FLW(f1, x1, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(1), FP_THREE);
endtask

//
// Test: FSW - store float to memory
//
task automatic test_fsw_basic;
  // Initialize f1 via FMV.W.X
  LUI(x1, 32'h3F800000);  // 1.0 in IEEE 754 (upper 20 bits: 0x3F800)
  FMV_W_X(f1, x1);

  // x2 = 0x1000 (DMEM base address)
  LUI(x2, 32'h00001000);

  // mem[x2] = f1
  FSW(f1, x2, 0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`DMEM_RD(0), 32'h3F800000);
endtask

//
// Test: FLW with offset
//
task automatic test_flw_offset;
  // Store values at different offsets
  `DMEM_WR(0, FP_ONE);
  `DMEM_WR(1, FP_TWO);
  `DMEM_WR(2, FP_THREE);

  // x1 = 0x1000 (DMEM base address)
  LUI(x1, 32'h00001000);

  // Load with different offsets
  FLW(f1, x1, 0);  // f1 = 1.0
  FLW(f2, x1, 4);  // f2 = 2.0
  FLW(f3, x1, 8);  // f3 = 3.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(1), FP_ONE);
  `CHECK_EQ(`FP_REG(2), FP_TWO);
  `CHECK_EQ(`FP_REG(3), FP_THREE);
endtask

// ============================================================================
// Basic Arithmetic Tests
// ============================================================================

//
// Test: FADD.S - 1.0 + 2.0 = 3.0
//
task automatic test_fadd_basic;
  // Load operands from memory
  `DMEM_WR(0, FP_ONE);
  `DMEM_WR(1, FP_TWO);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 1.0
  FLW(f2, x1, 4);  // f2 = 2.0

  FADD_S(f3, f1, f2, RNE);  // f3 = 3.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(3), FP_THREE);
endtask

//
// Test: FSUB.S - 5.0 - 2.0 = 3.0
//
task automatic test_fsub_basic;
  `DMEM_WR(0, FP_FIVE);
  `DMEM_WR(1, FP_TWO);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);
  FLW(f2, x1, 4);

  FSUB_S(f3, f1, f2, RNE);  // f3 = 3.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(3), FP_THREE);
endtask

//
// Test: FMUL.S - 2.0 * 3.0 = 6.0
//
task automatic test_fmul_basic;
  `DMEM_WR(0, FP_TWO);
  `DMEM_WR(1, FP_THREE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);
  FLW(f2, x1, 4);

  FMUL_S(f3, f1, f2, RNE);  // f3 = 6.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(3), FP_SIX);
endtask

//
// Test: FDIV.S - 6.0 / 2.0 = 3.0 (multi-cycle)
//
task automatic test_fdiv_basic;
  `DMEM_WR(0, FP_SIX);
  `DMEM_WR(1, FP_TWO);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);
  FLW(f2, x1, 4);

  FDIV_S(f3, f1, f2, RNE);  // f3 = 3.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 1000);
  `CHECK_EQ(`FP_REG(3), FP_THREE);
endtask

//
// Test: FSQRT.S - sqrt(4.0) = 2.0 (multi-cycle)
//
task automatic test_fsqrt_basic;
  `DMEM_WR(0, FP_FOUR);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);

  FSQRT_S(f2, f1, RNE);  // f2 = 2.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk, 1000);
  `CHECK_EQ(`FP_REG(2), FP_TWO);
endtask

// ============================================================================
// FMA Tests
// ============================================================================

//
// Test: FMADD.S - (2.0 * 3.0) + 1.0 = 7.0
//
task automatic test_fmadd_basic;
  `DMEM_WR(0, FP_TWO);
  `DMEM_WR(1, FP_THREE);
  `DMEM_WR(2, FP_ONE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 2.0
  FLW(f2, x1, 4);  // f2 = 3.0
  FLW(f3, x1, 8);  // f3 = 1.0

  FMADD_S(f4, f1, f2, f3, RNE);  // f4 = 2*3+1 = 7.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(4), FP_SEVEN);
endtask

//
// Test: FMSUB.S - (2.0 * 3.0) - 1.0 = 5.0
//
task automatic test_fmsub_basic;
  `DMEM_WR(0, FP_TWO);
  `DMEM_WR(1, FP_THREE);
  `DMEM_WR(2, FP_ONE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);
  FLW(f2, x1, 4);
  FLW(f3, x1, 8);

  FMSUB_S(f4, f1, f2, f3, RNE);  // f4 = 2*3-1 = 5.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(4), FP_FIVE);
endtask

// ============================================================================
// Comparison Tests
// ============================================================================

//
// Test: FEQ.S - equality comparison
//
task automatic test_feq_basic;
  `DMEM_WR(0, FP_THREE);
  `DMEM_WR(1, FP_THREE);
  `DMEM_WR(2, FP_FIVE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 3.0
  FLW(f2, x1, 4);  // f2 = 3.0
  FLW(f3, x1, 8);  // f3 = 5.0

  FEQ_S(x2, f1, f2);  // x2 = 1 (equal)
  FEQ_S(x3, f1, f3);  // x3 = 0 (not equal)
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
endtask

//
// Test: FLT.S - less than comparison
//
task automatic test_flt_basic;
  `DMEM_WR(0, FP_THREE);
  `DMEM_WR(1, FP_FIVE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 3.0
  FLW(f2, x1, 4);  // f2 = 5.0

  FLT_S(x2, f1, f2);  // x2 = 1 (3.0 < 5.0)
  FLT_S(x3, f2, f1);  // x3 = 0 (5.0 not < 3.0)
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd0);
endtask

//
// Test: FMIN.S/FMAX.S
//
task automatic test_fminmax_basic;
  `DMEM_WR(0, FP_THREE);
  `DMEM_WR(1, FP_FIVE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 3.0
  FLW(f2, x1, 4);  // f2 = 5.0

  FMIN_S(f3, f1, f2);  // f3 = 3.0
  FMAX_S(f4, f1, f2);  // f4 = 5.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(3), FP_THREE);
  `CHECK_EQ(`FP_REG(4), FP_FIVE);
endtask

// ============================================================================
// Move/Convert Tests
// ============================================================================

//
// Test: FMV.W.X - move integer to float
//
task automatic test_fmv_w_x_basic;
  LUI(x1, 32'h40400000);  // 3.0 in IEEE 754 (upper 20 bits: 0x40400)
  FMV_W_X(f1, x1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(1), FP_THREE);
endtask

//
// Test: FMV.X.W - move float to integer
//
task automatic test_fmv_x_w_basic;
  `DMEM_WR(0, FP_THREE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);

  FMV_X_W(x2, f1);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], FP_THREE);
endtask

//
// Test: FCVT.W.S - float to signed int
//
task automatic test_fcvt_w_s_basic;
  `DMEM_WR(0, FP_THREE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 3.0

  FCVT_W_S(x2, f1, RNE);  // x2 = 3
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd3);
endtask

//
// Test: FCVT.S.W - signed int to float
//
task automatic test_fcvt_s_w_basic;
  ADDI(x1, x0, 5);  // x1 = 5
  FCVT_S_W(f1, x1, RNE);  // f1 = 5.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(1), FP_FIVE);
endtask

// ============================================================================
// Sign Manipulation Tests
// ============================================================================

//
// Test: FSGNJ.S - copy sign
//
task automatic test_fsgnj_basic;
  `DMEM_WR(0, FP_THREE);
  `DMEM_WR(1, FP_NEG_ONE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 3.0
  FLW(f2, x1, 4);  // f2 = -1.0

  FSGNJ_S(f3, f1, f2);  // f3 = -3.0 (sign of f2)
  FSGNJN_S(f4, f1, f2);  // f4 = +3.0 (negated sign of f2)
  FSGNJX_S(f5, f1, f2);  // f5 = -3.0 (XOR of signs)
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(3), FP_NEG_THREE);
  `CHECK_EQ(`FP_REG(4), FP_THREE);
  `CHECK_EQ(`FP_REG(5), FP_NEG_THREE);
endtask

// ============================================================================
// Hazard/Forwarding Tests
// ============================================================================

//
// Test: RAW hazard - use FP result immediately
//
task automatic test_fp_raw_hazard;
  `DMEM_WR(0, FP_TWO);
  `DMEM_WR(1, FP_THREE);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 2.0
  FLW(f2, x1, 4);  // f2 = 3.0

  FADD_S(f3, f1, f2, RNE);  // f3 = 5.0
  FADD_S(f4, f3, f1, RNE);  // f4 = 7.0 (uses f3 immediately)
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(3), FP_FIVE);
  `CHECK_EQ(`FP_REG(4), FP_SEVEN);
endtask

//
// Test: Chained FP operations
//
task automatic test_fp_chain;
  `DMEM_WR(0, FP_TWO);

  LUI(x1, 32'h00001000);
  FLW(f1, x1, 0);  // f1 = 2.0

  FADD_S(f2, f1, f1, RNE);  // f2 = 4.0
  FADD_S(f3, f2, f2, RNE);  // f3 = 8.0
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(2), FP_FOUR);
  `CHECK_EQ(`FP_REG(3), FP_EIGHT);
endtask

//
// Test: FLW followed by immediate use (load-use hazard)
//
task automatic test_fp_load_use;
  `DMEM_WR(0, FP_TWO);
  `DMEM_WR(1, FP_THREE);

  LUI(x1, 32'h00001000);

  FLW(f1, x1, 0);  // f1 = 2.0
  FLW(f2, x1, 4);  // f2 = 3.0
  FADD_S(f3, f1, f2, RNE);  // f3 = 5.0 (uses loaded values)
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(`FP_REG(3), FP_FIVE);
endtask

//
// Test: Mixed int/FP operations
//
task automatic test_fp_mixed_int_fp;
  `DMEM_WR(0, FP_THREE);

  // Integer operations
  ADDI(x1, x0, 5);
  ADDI(x2, x0, 3);
  ADD(x3, x1, x2);  // x3 = 8

  // FP load and compute
  LUI(x4, 32'h00001000);
  FLW(f1, x4, 0);  // f1 = 3.0
  FADD_S(f2, f1, f1, RNE);  // f2 = 6.0

  // Convert and verify
  FCVT_W_S(x5, f2, RNE);  // x5 = 6
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'd8);
  `CHECK_EQ(`FP_REG(2), FP_SIX);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[5], 32'd6);
endtask

// ============================================================================
// CSR Tests
// ============================================================================

//
// Test: Read/write frm CSR
//
task automatic test_fp_csr_frm;
  // Set rounding mode to RTZ (1)
  ADDI(x1, x0, 1);
  CSRRW(x0, CSR_FRM, x1);

  // Read it back
  CSRRS(x2, CSR_FRM, x0);

  // Set to RDN (2)
  ADDI(x3, x0, 2);
  CSRRW(x0, CSR_FRM, x3);
  CSRRS(x4, CSR_FRM, x0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd1);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd2);
endtask

//
// Test: Read/write fflags CSR
//
task automatic test_fp_csr_fflags;
  // Set some flags (NX=1, OF=4 -> 5)
  ADDI(x1, x0, 5);
  CSRRW(x0, CSR_FFLAGS, x1);

  // Read back
  CSRRS(x2, CSR_FFLAGS, x0);

  // Clear some flags via CSRRC
  ADDI(x3, x0, 1);  // Clear NX
  CSRRC(x0, CSR_FFLAGS, x3);
  CSRRS(x4, CSR_FFLAGS, x0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'd5);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'd4);
endtask

//
// Test: fcsr combined access (frm + fflags)
//
task automatic test_fp_csr_fcsr;
  // Write fcsr = 0xAB (frm=5, fflags=0x0B)
  ADDI(x1, x0, 32'hAB);
  CSRRW(x0, CSR_FCSR, x1);

  // Read fcsr
  CSRRS(x2, CSR_FCSR, x0);

  // Read fflags separately
  CSRRS(x3, CSR_FFLAGS, x0);

  // Read frm separately
  CSRRS(x4, CSR_FRM, x0);
  EBREAK();

  load_program();

  `CHECK_WAIT_FOR_EBREAK(clk);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[2], 32'hAB);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[3], 32'h0B);
  `CHECK_EQ(uut.cpu.stage_id.regfile.regs[4], 32'h05);
endtask

