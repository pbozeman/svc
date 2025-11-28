`ifndef SVC_RV_FMT_LD_SV
`define SVC_RV_FMT_LD_SV

`include "svc.sv"

//
// RISC-V Load Format
//
// Handles data extraction and sign/zero extension for load operations.
// Supports LB, LH, LW (signed) and LBU, LHU (unsigned).
//
module svc_rv_fmt_ld #(
    parameter int XLEN
) (
    //
    // Load operation inputs
    //
    input logic [XLEN-1:0] data_in,
    input logic [     1:0] addr,
    input logic [     2:0] funct3,

`ifdef RISCV_FORMAL
    output logic [3:0] f_rstrb,
`endif

    //
    // Load result output
    //
    output logic [XLEN-1:0] data_out

);
  `include "svc_rv_defs.svh"

  //
  // Extract byte and halfword slices from memory data
  //
  logic [ 7:0] byte0;
  logic [ 7:0] byte1;
  logic [ 7:0] byte2;
  logic [ 7:0] byte3;
  logic [15:0] half0;
  logic [15:0] half1;
  logic        addr_half;

  assign byte0     = data_in[7:0];
  assign byte1     = data_in[15:8];
  assign byte2     = data_in[23:16];
  assign byte3     = data_in[31:24];
  assign half0     = data_in[15:0];
  assign half1     = data_in[31:16];
  assign addr_half = addr[1];

  //
  // Select byte based on address
  //
  logic [7:0] selected_byte;

  always_comb begin
    case (addr)
      2'b00:   selected_byte = byte0;
      2'b01:   selected_byte = byte1;
      2'b10:   selected_byte = byte2;
      2'b11:   selected_byte = byte3;
      default: selected_byte = byte0;
    endcase
  end

  //
  // Select halfword based on address
  //
  logic [15:0] selected_half;

  always_comb begin
    case (addr_half)
      1'b0:    selected_half = half0;
      1'b1:    selected_half = half1;
      default: selected_half = half0;
    endcase
  end

  //
  // Extract sign bits
  //
  logic byte_sign;
  logic half_sign;

  assign byte_sign = selected_byte[7];
  assign half_sign = selected_half[15];

  //
  // Apply sign/zero extension based on funct3
  //
  always_comb begin
    case (funct3)
      FUNCT3_LB:  data_out = {{24{byte_sign}}, selected_byte};
      FUNCT3_LH:  data_out = {{16{half_sign}}, selected_half};
      FUNCT3_LW:  data_out = data_in;
      FUNCT3_LBU: data_out = {24'b0, selected_byte};
      FUNCT3_LHU: data_out = {16'b0, selected_half};
      default:    data_out = data_in;
    endcase
  end

`ifdef RISCV_FORMAL
  logic [3:0] f_byte_mask;
  logic [3:0] f_half_mask;

  always_comb begin
    f_byte_mask = {addr == 2'b11, addr == 2'b10, addr == 2'b01, addr == 2'b00};
    f_half_mask = addr_half ? 4'b1100 : 4'b0011;

    case (funct3)
      FUNCT3_LB, FUNCT3_LBU: f_rstrb = f_byte_mask;
      FUNCT3_LH, FUNCT3_LHU: f_rstrb = f_half_mask;
      FUNCT3_LW:             f_rstrb = 4'b1111;
      default:               f_rstrb = 4'b0000;
    endcase
  end

`endif

endmodule

`endif
