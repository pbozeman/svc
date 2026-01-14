`ifndef SVC_RV_FP_CSR_SV
`define SVC_RV_FP_CSR_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V Floating-Point CSR Module
//
// Implements RV32F CSRs:
// - fflags (0x001): FP exception flags [4:0] = {NV, DZ, OF, UF, NX}
// - frm    (0x002): FP rounding mode [2:0]
// - fcsr   (0x003): Combined [7:5] = frm, [4:0] = fflags
//
// Features:
// - Full CSR read/write support (CSRRW/S/C and immediate variants)
// - Sticky exception flag accumulation (set via OR, cleared only by write)
// - Dynamic rounding mode output for FPU
//
module svc_rv_fp_csr (
    input logic clk,
    input logic rst_n,

    //
    // CSR interface
    //
    input  logic [11:0] csr_addr,
    input  logic [ 2:0] csr_op,     // funct3: CSRRW/S/C/WI/SI/CI
    input  logic [31:0] csr_wdata,  // Write data (rs1 or zimm)
    input  logic        csr_en,     // CSR operation enable
    output logic [31:0] csr_rdata,
    output logic        csr_valid,  // Address matches FP CSR

    //
    // Dynamic rounding mode output (to FPU)
    //
    output logic [2:0] frm,

    //
    // Exception flag accumulation (from FPU)
    //
    input logic       fflags_set_en,
    input logic [4:0] fflags_set      // {NV, DZ, OF, UF, NX}
);

  `include "svc_rv_defs.svh"

  //
  // CSR registers
  //
  logic [4:0] fflags;
  logic [2:0] frm_reg;

  assign frm = frm_reg;

  //
  // Address decode
  //
  logic addr_fflags;
  logic addr_frm;
  logic addr_fcsr;

  assign addr_fflags = (csr_addr == CSR_FFLAGS);
  assign addr_frm    = (csr_addr == CSR_FRM);
  assign addr_fcsr   = (csr_addr == CSR_FCSR);
  assign csr_valid   = addr_fflags || addr_frm || addr_fcsr;

  //
  // CSR read mux
  //
  always_comb begin
    csr_rdata = 32'h0;
    if (addr_fflags) begin
      csr_rdata = {27'h0, fflags};
    end else if (addr_frm) begin
      csr_rdata = {29'h0, frm_reg};
    end else if (addr_fcsr) begin
      csr_rdata = {24'h0, frm_reg, fflags};
    end
  end

  //
  // CSR operation decode
  //
  logic is_csrrw, is_csrrs, is_csrrc;
  logic is_csrrwi, is_csrrsi, is_csrrci;
  logic is_write_op;
  logic is_set_op;
  logic is_clear_op;

  assign is_csrrw    = (csr_op == FUNCT3_CSRRW);
  assign is_csrrs    = (csr_op == FUNCT3_CSRRS);
  assign is_csrrc    = (csr_op == FUNCT3_CSRRC);
  assign is_csrrwi   = (csr_op == FUNCT3_CSRRWI);
  assign is_csrrsi   = (csr_op == FUNCT3_CSRRSI);
  assign is_csrrci   = (csr_op == FUNCT3_CSRRCI);

  assign is_write_op = is_csrrw || is_csrrwi;
  assign is_set_op   = is_csrrs || is_csrrsi;
  assign is_clear_op = is_csrrc || is_csrrci;

  //
  // Write enable and data computation
  //
  logic       fflags_we;
  logic       frm_we;
  logic [4:0] fflags_next;
  logic [2:0] frm_next;

  always_comb begin
    fflags_we   = 1'b0;
    frm_we      = 1'b0;
    fflags_next = fflags;
    frm_next    = frm_reg;

    if (csr_en && csr_valid) begin
      if (addr_fflags) begin
        fflags_we = 1'b1;
        if (is_write_op) begin
          fflags_next = csr_wdata[4:0];
        end else if (is_set_op) begin
          fflags_next = fflags | csr_wdata[4:0];
        end else if (is_clear_op) begin
          fflags_next = fflags & ~csr_wdata[4:0];
        end
      end else if (addr_frm) begin
        frm_we = 1'b1;
        if (is_write_op) begin
          frm_next = csr_wdata[2:0];
        end else if (is_set_op) begin
          frm_next = frm_reg | csr_wdata[2:0];
        end else if (is_clear_op) begin
          frm_next = frm_reg & ~csr_wdata[2:0];
        end
      end else if (addr_fcsr) begin
        fflags_we = 1'b1;
        frm_we    = 1'b1;
        if (is_write_op) begin
          fflags_next = csr_wdata[4:0];
          frm_next    = csr_wdata[7:5];
        end else if (is_set_op) begin
          fflags_next = fflags | csr_wdata[4:0];
          frm_next    = frm_reg | csr_wdata[7:5];
        end else if (is_clear_op) begin
          fflags_next = fflags & ~csr_wdata[4:0];
          frm_next    = frm_reg & ~csr_wdata[7:5];
        end
      end
    end

    //
    // Accumulate FPU exception flags (sticky - OR with new flags)
    // This happens regardless of CSR operations
    //
    if (fflags_set_en) begin
      fflags_next = fflags_next | fflags_set;
    end
  end

  //
  // Register updates
  //
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      fflags  <= 5'h0;
      frm_reg <= 3'h0;
    end else begin
      if (fflags_we || fflags_set_en) begin
        fflags <= fflags_next;
      end
      if (frm_we) begin
        frm_reg <= frm_next;
      end
    end
  end

  // Only bits [7:0] are used (fflags[4:0] and frm[2:0])
  `SVC_UNUSED(csr_wdata[31:8]);

endmodule

`endif
