`include "svc_unit.sv"

// TODO: the CHECK_TRUE(0) is kinda janky, but the check macros don't work with
// strings, and even using result == expected in CHECK_TRUE had weirdness.

module svc_rv_dasm_tbi;
  logic  [31:0] MEM    [0:1023];
  logic  [31:0] inst;
  string        result;

  `include "svc_rv_asm.svh"
  `include "svc_rv_dasm.svh"

  //
  // Test R-type instructions
  //
  task automatic test_r_type;
    inst   = 32'h003100b3;
    result = dasm_inst(inst);
    if (result != "   add  x1,  x2,  x3") begin
      $display("FAIL: expected '   add  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h403100b3;
    result = dasm_inst(inst);
    if (result != "   sub  x1,  x2,  x3") begin
      $display("FAIL: expected '   sub  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h003110b3;
    result = dasm_inst(inst);
    if (result != "   sll  x1,  x2,  x3") begin
      $display("FAIL: expected '   sll  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h003120b3;
    result = dasm_inst(inst);
    if (result != "   slt  x1,  x2,  x3") begin
      $display("FAIL: expected '   slt  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h003130b3;
    result = dasm_inst(inst);
    if (result != "  sltu  x1,  x2,  x3") begin
      $display("FAIL: expected '  sltu  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h003140b3;
    result = dasm_inst(inst);
    if (result != "   xor  x1,  x2,  x3") begin
      $display("FAIL: expected '   xor  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h003150b3;
    result = dasm_inst(inst);
    if (result != "   srl  x1,  x2,  x3") begin
      $display("FAIL: expected '   srl  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h403150b3;
    result = dasm_inst(inst);
    if (result != "   sra  x1,  x2,  x3") begin
      $display("FAIL: expected '   sra  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h003160b3;
    result = dasm_inst(inst);
    if (result != "    or  x1,  x2,  x3") begin
      $display("FAIL: expected '    or  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h003170b3;
    result = dasm_inst(inst);
    if (result != "   and  x1,  x2,  x3") begin
      $display("FAIL: expected '   and  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test M-extension multiply instructions
  //
  task automatic test_m_ext;
    inst   = 32'h023100b3;
    result = dasm_inst(inst);
    if (result != "   mul  x1,  x2,  x3") begin
      $display("FAIL: expected '   mul  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h023110b3;
    result = dasm_inst(inst);
    if (result != "  mulh  x1,  x2,  x3") begin
      $display("FAIL: expected '  mulh  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h023120b3;
    result = dasm_inst(inst);
    if (result != "mulhsu  x1,  x2,  x3") begin
      $display("FAIL: expected 'mulhsu  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h023130b3;
    result = dasm_inst(inst);
    if (result != " mulhu  x1,  x2,  x3") begin
      $display("FAIL: expected ' mulhu  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test M-extension division/remainder instructions
  //
  task automatic test_m_ext_div;
    inst   = 32'h023140b3;
    result = dasm_inst(inst);
    if (result != "   div  x1,  x2,  x3") begin
      $display("FAIL: expected '   div  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h023150b3;
    result = dasm_inst(inst);
    if (result != "  divu  x1,  x2,  x3") begin
      $display("FAIL: expected '  divu  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h023160b3;
    result = dasm_inst(inst);
    if (result != "   rem  x1,  x2,  x3") begin
      $display("FAIL: expected '   rem  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h023170b3;
    result = dasm_inst(inst);
    if (result != "  remu  x1,  x2,  x3") begin
      $display("FAIL: expected '  remu  x1,  x2,  x3', got '%s'", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test I-type ALU instructions
  //
  task automatic test_i_type_alu;
    inst   = 32'h00a10093;
    result = dasm_inst(inst);
    if (result != "  addi  x1,  x2, 10") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'hfff10093;
    result = dasm_inst(inst);
    if (result != "  addi  x1,  x2, -1") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a12093;
    result = dasm_inst(inst);
    if (result != "  slti  x1,  x2, 10") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a13093;
    result = dasm_inst(inst);
    if (result != " sltiu  x1,  x2, 10") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a14093;
    result = dasm_inst(inst);
    if (result != "  xori  x1,  x2, 10") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a16093;
    result = dasm_inst(inst);
    if (result != "   ori  x1,  x2, 10") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a17093;
    result = dasm_inst(inst);
    if (result != "  andi  x1,  x2, 10") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test shift immediate instructions
  //
  task automatic test_shift_imm;
    inst   = 32'h00511093;
    result = dasm_inst(inst);
    if (result != "  slli  x1,  x2, 5") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00515093;
    result = dasm_inst(inst);
    if (result != "  srli  x1,  x2, 5") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h40515093;
    result = dasm_inst(inst);
    if (result != "  srai  x1,  x2, 5") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test load instructions
  //
  task automatic test_loads;
    inst   = 32'h00a10083;
    result = dasm_inst(inst);
    if (result != "    lb  x1, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a11083;
    result = dasm_inst(inst);
    if (result != "    lh  x1, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a12083;
    result = dasm_inst(inst);
    if (result != "    lw  x1, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a14083;
    result = dasm_inst(inst);
    if (result != "   lbu  x1, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a15083;
    result = dasm_inst(inst);
    if (result != "   lhu  x1, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'hff810083;
    result = dasm_inst(inst);
    if (result != "    lb  x1, -8(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test store instructions
  //
  task automatic test_stores;
    inst   = 32'h00310523;
    result = dasm_inst(inst);
    if (result != "    sb  x3, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00311523;
    result = dasm_inst(inst);
    if (result != "    sh  x3, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00312523;
    result = dasm_inst(inst);
    if (result != "    sw  x3, 10(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'hfe312c23;
    result = dasm_inst(inst);
    if (result != "    sw  x3, -8(x2)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test branch instructions
  //
  task automatic test_branches;
    inst   = 32'h00310463;
    result = dasm_inst(inst);
    if (result != "   beq  x2,  x3, 8") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00311463;
    result = dasm_inst(inst);
    if (result != "   bne  x2,  x3, 8") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00314463;
    result = dasm_inst(inst);
    if (result != "   blt  x2,  x3, 8") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00315463;
    result = dasm_inst(inst);
    if (result != "   bge  x2,  x3, 8") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00316463;
    result = dasm_inst(inst);
    if (result != "  bltu  x2,  x3, 8") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00317463;
    result = dasm_inst(inst);
    if (result != "  bgeu  x2,  x3, 8") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'hfe311ee3;
    result = dasm_inst(inst);
    if (result != "   bne  x2,  x3, -4") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test U-type instructions
  //
  task automatic test_u_type;
    inst   = 32'h123450b7;
    result = dasm_inst(inst);
    if (result != "   lui  x1, 0x12345") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h12345097;
    result = dasm_inst(inst);
    if (result != " auipc  x1, 0x12345") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test J-type instructions
  //
  task automatic test_j_type;
    inst   = 32'h008000ef;
    result = dasm_inst(inst);
    if (result != "   jal  x1, 8") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'hff5ff0ef;
    result = dasm_inst(inst);
    if (result != "   jal  x1, -12") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h000100e7;
    result = dasm_inst(inst);
    if (result != "  jalr  x1,  x2, 0") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00a100e7;
    result = dasm_inst(inst);
    if (result != "  jalr  x1,  x2, 10") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test system instructions
  //
  task automatic test_system;
    inst   = 32'h00000073;
    result = dasm_inst(inst);
    if (result != "ecall") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h00100073;
    result = dasm_inst(inst);
    if (result != "ebreak") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h0000000f;
    result = dasm_inst(inst);
    if (result != "fence") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    inst   = 32'h0000100f;
    result = dasm_inst(inst);
    if (result != "fence.i") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test CSR instructions
  //
  task automatic test_csr;
    asm_pc = 0;
    CSRRS(x1, 12'hC00, x2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != " csrrs  x1,    cycle,  x2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRS(x1, 12'hC80, x2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != " csrrs  x1,   cycleh,  x2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRS(x1, 12'hC02, x2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != " csrrs  x1,  instret,  x2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRS(x1, 12'hC82, x2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != " csrrs  x1, instreth,  x2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRS(x1, 12'h300, x2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != " csrrs  x1,    0x300,  x2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRW(x1, 12'hC00, x2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != " csrrw  x1,    cycle,  x2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRC(x1, 12'hC00, x2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != " csrrc  x1,    cycle,  x2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRWI(x1, 12'hC00, 1);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "csrrwi  x1,    cycle,   1") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRSI(x1, 12'hC00, 1);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "csrrsi  x1,    cycle,   1") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    CSRRCI(x1, 12'hC00, 2);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "csrrci  x1,    cycle,   2") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test with assembler round-trip
  //
  task automatic test_roundtrip;
    asm_pc = 0;
    ADD(x1, x2, x3);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "   add  x1,  x2,  x3") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    ADDI(x5, x6, 42);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "  addi  x5,  x6, 42") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    LW(x10, x11, 100);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "    lw x10, 100(x11)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    SW(x20, x21, 200);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "    sw x20, 200(x21)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    BEQ(x1, x2, 16);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "   beq  x1,  x2, 16") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    JAL(x1, 100);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "   jal  x1, 100") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end

    asm_pc = 0;
    LUI(x15, 32'h12345000);
    inst   = MEM[0];
    result = dasm_inst(inst);
    if (result != "   lui x15, 0x12345") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  //
  // Test unknown instruction
  //
  task automatic test_unknown;
    inst   = 32'hdeadbe7e;
    result = dasm_inst(inst);
    if (result != "unknown (0xdeadbe7e)") begin
      $display("FAIL: got %s", result);
      `CHECK_TRUE(0);
    end
  endtask

  `TEST_SUITE_BEGIN(svc_rv_dasm_tbi);
  `TEST_CASE(test_r_type);
  `TEST_CASE(test_m_ext);
  `TEST_CASE(test_m_ext_div);
  `TEST_CASE(test_i_type_alu);
  `TEST_CASE(test_shift_imm);
  `TEST_CASE(test_loads);
  `TEST_CASE(test_stores);
  `TEST_CASE(test_branches);
  `TEST_CASE(test_u_type);
  `TEST_CASE(test_j_type);
  `TEST_CASE(test_system);
  `TEST_CASE(test_csr);
  `TEST_CASE(test_roundtrip);
  `TEST_CASE(test_unknown);
  `TEST_SUITE_END();
endmodule
