`ifndef SVC_RV_FMT_ST_SV
`define SVC_RV_FMT_ST_SV

`include "svc.sv"

//
// RISC-V Store Format
//
// Handles data positioning and write strobe generation for store operations.
// Supports SB (store byte), SH (store halfword), and SW (store word).
//
module svc_rv_fmt_st #(
    parameter int XLEN
) (
    //
    // Store operation inputs
    //
    input logic [XLEN-1:0] data_in,
    input logic [     1:0] addr,
    input logic [     2:0] funct3,

    //
    // Memory interface outputs
    //
    output logic [  XLEN-1:0] data_out,
    output logic [XLEN/8-1:0] wstrb
);
  `include "svc_rv_defs.svh"

  logic [ 7:0] byte_data;
  logic [15:0] half_data;
  logic        addr_half;

  assign byte_data = data_in[7:0];
  assign half_data = data_in[15:0];
  assign addr_half = addr[1];

  //
  // Position write data based on operation size
  //
  always_comb begin
    case (funct3)
      FUNCT3_SB: data_out = {4{byte_data}};
      FUNCT3_SH: data_out = {2{half_data}};
      default:   data_out = data_in;
    endcase
  end

  //
  // Generate write strobes based on address and operation size
  //
  always_comb begin
    case (funct3)
      FUNCT3_SB: begin
        case (addr)
          2'b00:   wstrb = 4'b0001;
          2'b01:   wstrb = 4'b0010;
          2'b10:   wstrb = 4'b0100;
          2'b11:   wstrb = 4'b1000;
          default: wstrb = 4'b0001;
        endcase
      end

      FUNCT3_SH: begin
        case (addr_half)
          1'b0:    wstrb = 4'b0011;
          1'b1:    wstrb = 4'b1100;
          default: wstrb = 4'b0011;
        endcase
      end

      default: begin
        wstrb = 4'b1111;
      end
    endcase
  end

endmodule

`endif
