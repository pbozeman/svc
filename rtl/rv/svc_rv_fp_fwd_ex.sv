`ifndef SVC_RV_FP_FWD_EX_SV
`define SVC_RV_FP_FWD_EX_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V FP EX stage data forwarding unit
//
// Provides MEM→EX bypass for back-to-back FP operations. Similar to the
// integer forwarding unit but handles three source registers (fp_rs1, fp_rs2,
// fp_rs3) for FMA instructions.
//
// Forwarding paths:
// - MEM→EX: Forwards FP results for back-to-back ops (Producer in MEM,
//           Consumer in EX). Reads from the nearby EX/MEM register.
// - WB→ID: Handled by FP regfile internal forwarding (FWD_REGFILE parameter)
//
// Cannot forward from MEM stage:
// - FP load results on BRAM (data not ready until WB)
// - (FP load results on SRAM ARE ready in MEM and can be forwarded)
//
// Multi-cycle FP ops (FDIV/FSQRT):
// - No forwarding to MC ops - they use pipeline register values directly
// - Hazard unit stalls if there's a dependency until value is in regfile
//
module svc_rv_fp_fwd_ex #(
    parameter int XLEN,
    parameter int FWD_FP,
    parameter int MEM_TYPE
) (
    //
    // EX stage inputs (consumers)
    //
    input logic [     4:0] fp_rs1_ex,
    input logic [     4:0] fp_rs2_ex,
    input logic [     4:0] fp_rs3_ex,
    input logic [XLEN-1:0] fp_rs1_data_ex,
    input logic [XLEN-1:0] fp_rs2_data_ex,
    input logic [XLEN-1:0] fp_rs3_data_ex,

    //
    // Multi-cycle FP operation indicator
    //
    // When is_fp_mc_ex=1, disable forwarding. The pipeline register
    // holds stable frs*_data_ex values during MC execution.
    //
    input logic is_fp_mc_ex,

    //
    // MEM stage inputs
    //
    input logic [     4:0] fp_rd_mem,
    input logic            fp_reg_write_mem,
    input logic            is_fp_load_mem,
    input logic [XLEN-1:0] fp_result_mem,
    input logic [XLEN-1:0] ld_data_mem,       // Shared with integer loads

    //
    // Forwarded outputs
    //
    output logic [XLEN-1:0] fwd_fp_rs1_ex,
    output logic [XLEN-1:0] fwd_fp_rs2_ex,
    output logic [XLEN-1:0] fwd_fp_rs3_ex
);

  `include "svc_rv_defs.svh"

  if (FWD_FP != 0) begin : g_forwarding
    //
    // MEM→EX result forwarding (non-load FP results)
    //
    // Forward FP results from MEM stage. Do NOT forward FP loads on BRAM
    // (data not available until WB).
    //
    // Disable forwarding entirely for multi-cycle FP ops (is_fp_mc_ex).
    //
    logic mem_to_ex_fwd_a;
    logic mem_to_ex_fwd_b;
    logic mem_to_ex_fwd_c;

    always_comb begin
      mem_to_ex_fwd_a = 1'b0;
      mem_to_ex_fwd_b = 1'b0;
      mem_to_ex_fwd_c = 1'b0;

      if (!is_fp_mc_ex && fp_reg_write_mem && !is_fp_load_mem) begin
        mem_to_ex_fwd_a = (fp_rd_mem == fp_rs1_ex);
        mem_to_ex_fwd_b = (fp_rd_mem == fp_rs2_ex);
        mem_to_ex_fwd_c = (fp_rd_mem == fp_rs3_ex);
      end
    end

    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_sram_load_fwd
      //
      // SRAM: FP load data is ready in MEM stage, can forward
      //
      logic mem_to_ex_fwd_load_a;
      logic mem_to_ex_fwd_load_b;
      logic mem_to_ex_fwd_load_c;

      always_comb begin
        mem_to_ex_fwd_load_a = 1'b0;
        mem_to_ex_fwd_load_b = 1'b0;
        mem_to_ex_fwd_load_c = 1'b0;

        if (!is_fp_mc_ex && fp_reg_write_mem && is_fp_load_mem) begin
          mem_to_ex_fwd_load_a = (fp_rd_mem == fp_rs1_ex);
          mem_to_ex_fwd_load_b = (fp_rd_mem == fp_rs2_ex);
          mem_to_ex_fwd_load_c = (fp_rd_mem == fp_rs3_ex);
        end
      end

      //
      // Forwarding muxes with priority:
      // MEM load > MEM result > regfile
      //
      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_a: fwd_fp_rs1_ex = ld_data_mem;
          mem_to_ex_fwd_a:      fwd_fp_rs1_ex = fp_result_mem;
          default:              fwd_fp_rs1_ex = fp_rs1_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_b: fwd_fp_rs2_ex = ld_data_mem;
          mem_to_ex_fwd_b:      fwd_fp_rs2_ex = fp_result_mem;
          default:              fwd_fp_rs2_ex = fp_rs2_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_c: fwd_fp_rs3_ex = ld_data_mem;
          mem_to_ex_fwd_c:      fwd_fp_rs3_ex = fp_result_mem;
          default:              fwd_fp_rs3_ex = fp_rs3_data_ex;
        endcase
      end

    end else begin : g_bram_no_load_fwd
      //
      // BRAM: FP load data not ready in MEM stage, cannot forward
      //
      // Forwarding muxes with priority:
      // MEM result > regfile
      //
      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_a: fwd_fp_rs1_ex = fp_result_mem;
          default:         fwd_fp_rs1_ex = fp_rs1_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_b: fwd_fp_rs2_ex = fp_result_mem;
          default:         fwd_fp_rs2_ex = fp_rs2_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_c: fwd_fp_rs3_ex = fp_result_mem;
          default:         fwd_fp_rs3_ex = fp_rs3_data_ex;
        endcase
      end

      `SVC_UNUSED({ld_data_mem});
    end

  end else begin : g_no_forwarding
    //
    // No forwarding, just pass through
    //
    assign fwd_fp_rs1_ex = fp_rs1_data_ex;
    assign fwd_fp_rs2_ex = fp_rs2_data_ex;
    assign fwd_fp_rs3_ex = fp_rs3_data_ex;

    // verilog_format: off
    `SVC_UNUSED({fp_rs1_ex, fp_rs2_ex, fp_rs3_ex, fp_rd_mem, fp_reg_write_mem,
                 is_fp_load_mem, fp_result_mem, ld_data_mem,
                 is_fp_mc_ex, MEM_TYPE});
    // verilog_format: on
  end

endmodule

`endif
