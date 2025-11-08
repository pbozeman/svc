`ifndef SVC_RV_DASM_SVH
`define SVC_RV_DASM_SVH

//
// RISC-V RV32I Disassembler
//
// Provides a function to disassemble RISC-V machine code instructions
// into human-readable assembly.
//
// Usage in testbench or simulation:
//   `include "svc_rv_dasm.svh"
//   logic [31:0] inst;
//   $display("%s", dasm_inst(inst));
//
// verilator lint_off UNUSEDSIGNAL

//
// Register name lookup
//
function automatic string reg_name(input logic [4:0] reg_num);
  return $sformatf("x%0d", reg_num);
endfunction

//
// CSR name lookup
//
function automatic string csr_name(input logic [11:0] csr_addr);
  case (csr_addr)
    12'hC00: return "cycle";
    12'hC80: return "cycleh";
    12'hC02: return "instret";
    12'hC82: return "instreth";
    default: return $sformatf("0x%03x", csr_addr);
  endcase
endfunction

//
// Main disassembly function
//
function automatic string dasm_inst(input logic [31:0] instr);
  logic [6:0] opcode;
  logic [4:0] rd, rs1, rs2;
  logic [2:0] funct3;
  logic [6:0] funct7;
  logic signed [31:0] imm_i, imm_s, imm_b, imm_u, imm_j;
  logic [11:0] csr;
  logic [ 4:0] shamt;

  opcode = instr[6:0];
  rd     = instr[11:7];
  funct3 = instr[14:12];
  rs1    = instr[19:15];
  rs2    = instr[24:20];
  funct7 = instr[31:25];

  imm_i  = {{20{instr[31]}}, instr[31:20]};
  imm_s  = {{20{instr[31]}}, instr[31:25], instr[11:7]};
  imm_b  = {{19{instr[31]}}, instr[31], instr[7], instr[30:25], instr[11:8], 1'b0};
  imm_u  = {instr[31:12], 12'b0};
  imm_j  = {{11{instr[31]}}, instr[31], instr[19:12], instr[20], instr[30:21], 1'b0};
  csr    = instr[31:20];
  shamt  = instr[24:20];

  case (opcode)
    7'b0110011: begin
      case (funct3)
        3'b000: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "add", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0100000) begin
            return $sformatf("%6s %3s, %3s, %3s", "sub", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "mul", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        3'b001: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "sll", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "mulh", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        3'b010: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "slt", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "mulhsu", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        3'b011: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "sltu", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "mulhu", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        3'b100: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "xor", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "div", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        3'b101: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "srl", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0100000) begin
            return $sformatf("%6s %3s, %3s, %3s", "sra", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "divu", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        3'b110: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "or", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "rem", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        3'b111: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %3s", "and", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end else if (funct7 == 7'b0000001) begin
            return $sformatf("%6s %3s, %3s, %3s", "remu", reg_name(rd), reg_name(rs1),
                             reg_name(rs2));
          end
        end
        default: ;
      endcase
    end

    7'b0010011: begin
      case (funct3)
        3'b000:
        return $sformatf(
            "%6s %3s, %3s, %0d", "addi", reg_name(rd), reg_name(rs1), imm_i
        );
        3'b010:
        return $sformatf(
            "%6s %3s, %3s, %0d", "slti", reg_name(rd), reg_name(rs1), imm_i
        );
        3'b011:
        return $sformatf(
            "%6s %3s, %3s, %0d", "sltiu", reg_name(rd), reg_name(rs1), imm_i
        );
        3'b100:
        return $sformatf(
            "%6s %3s, %3s, %0d", "xori", reg_name(rd), reg_name(rs1), imm_i
        );
        3'b110:
        return $sformatf("%6s %3s, %3s, %0d", "ori", reg_name(rd), reg_name(rs1), imm_i);
        3'b111:
        return $sformatf(
            "%6s %3s, %3s, %0d", "andi", reg_name(rd), reg_name(rs1), imm_i
        );
        3'b001: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %0d", "slli", reg_name(rd), reg_name(rs1),
                             shamt);
          end
        end
        3'b101: begin
          if (funct7 == 7'b0000000) begin
            return $sformatf("%6s %3s, %3s, %0d", "srli", reg_name(rd), reg_name(rs1),
                             shamt);
          end else if (funct7 == 7'b0100000) begin
            return $sformatf("%6s %3s, %3s, %0d", "srai", reg_name(rd), reg_name(rs1),
                             shamt);
          end
        end
        default: ;
      endcase
    end

    7'b0000011: begin
      case (funct3)
        3'b000:
        return $sformatf("%6s %3s, %0d(%s)", "lb", reg_name(rd), imm_i, reg_name(rs1));
        3'b001:
        return $sformatf("%6s %3s, %0d(%s)", "lh", reg_name(rd), imm_i, reg_name(rs1));
        3'b010:
        return $sformatf("%6s %3s, %0d(%s)", "lw", reg_name(rd), imm_i, reg_name(rs1));
        3'b100:
        return $sformatf("%6s %3s, %0d(%s)", "lbu", reg_name(rd), imm_i, reg_name(rs1));
        3'b101:
        return $sformatf("%6s %3s, %0d(%s)", "lhu", reg_name(rd), imm_i, reg_name(rs1));
        default: ;
      endcase
    end

    7'b0100011: begin
      case (funct3)
        3'b000:
        return $sformatf("%6s %3s, %0d(%s)", "sb", reg_name(rs2), imm_s, reg_name(rs1));
        3'b001:
        return $sformatf("%6s %3s, %0d(%s)", "sh", reg_name(rs2), imm_s, reg_name(rs1));
        3'b010:
        return $sformatf("%6s %3s, %0d(%s)", "sw", reg_name(rs2), imm_s, reg_name(rs1));
        default: ;
      endcase
    end

    7'b1100011: begin
      case (funct3)
        3'b000:
        return $sformatf(
            "%6s %3s, %3s, %0d", "beq", reg_name(rs1), reg_name(rs2), imm_b
        );
        3'b001:
        return $sformatf(
            "%6s %3s, %3s, %0d", "bne", reg_name(rs1), reg_name(rs2), imm_b
        );
        3'b100:
        return $sformatf(
            "%6s %3s, %3s, %0d", "blt", reg_name(rs1), reg_name(rs2), imm_b
        );
        3'b101:
        return $sformatf(
            "%6s %3s, %3s, %0d", "bge", reg_name(rs1), reg_name(rs2), imm_b
        );
        3'b110:
        return $sformatf(
            "%6s %3s, %3s, %0d", "bltu", reg_name(rs1), reg_name(rs2), imm_b
        );
        3'b111:
        return $sformatf(
            "%6s %3s, %3s, %0d", "bgeu", reg_name(rs1), reg_name(rs2), imm_b
        );
        default: ;
      endcase
    end

    7'b0110111: return $sformatf("%6s %3s, 0x%05x", "lui", reg_name(rd), instr[31:12]);

    7'b0010111: return $sformatf("%6s %3s, 0x%05x", "auipc", reg_name(rd), instr[31:12]);

    7'b1101111: return $sformatf("%6s %3s, %0d", "jal", reg_name(rd), imm_j);

    7'b1100111: begin
      if (funct3 == 3'b000) begin
        return
            $sformatf("%6s %3s, %3s, %0d", "jalr", reg_name(rd), reg_name(rs1), imm_i);
      end
    end

    7'b0001111: begin
      case (funct3)
        3'b000: return "fence";
        3'b001: return "fence.i";
        default: ;
      endcase
    end

    7'b1110011: begin
      case (funct3)
        3'b000: begin
          if (instr[31:20] == 12'h000) return "ecall";
          if (instr[31:20] == 12'h001) return "ebreak";
        end
        3'b001:
        return $sformatf(
            "%6s %3s, %8s, %3s", "csrrw", reg_name(rd), csr_name(csr), reg_name(rs1)
        );
        3'b010:
        return $sformatf(
            "%6s %3s, %8s, %3s", "csrrs", reg_name(rd), csr_name(csr), reg_name(rs1)
        );
        3'b011:
        return $sformatf(
            "%6s %3s, %8s, %3s", "csrrc", reg_name(rd), csr_name(csr), reg_name(rs1)
        );
        3'b101:
        return $sformatf(
            "%6s %3s, %8s, %3d", "csrrwi", reg_name(rd), csr_name(csr), rs1
        );
        3'b110:
        return $sformatf(
            "%6s %3s, %8s, %3d", "csrrsi", reg_name(rd), csr_name(csr), rs1
        );
        3'b111:
        return $sformatf(
            "%6s %3s, %8s, %3d", "csrrci", reg_name(rd), csr_name(csr), rs1
        );
        default: ;
      endcase
    end
    default: ;
  endcase

  return $sformatf("unknown (0x%08x)", instr);
endfunction

// verilator lint_on UNUSEDSIGNAL

`endif
