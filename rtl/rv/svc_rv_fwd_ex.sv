`ifndef SVC_RV_FWD_EX_SV
`define SVC_RV_FWD_EX_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V EX stage data forwarding unit
//
// Provides MEM→EX bypass for back-to-back ALU operations (cheap forwarding
// from nearby EX/MEM pipeline register).
//
// NOTE: WB→EX forwarding was removed to improve timing. The WB
// forwarding path is long (from WB stage back to EX mux) and increases EX
// stage combinational depth. Instead, WB→ID forwarding happens earlier in
// the ID stage (see svc_rv_fwd_id), before the ID→EX pipeline register.
// This moves the expensive WB forwarding mux off the EX critical path.
//
// Forwarding paths:
// - MEM→EX: Forwards ALU results for back-to-back ops (Producer in MEM,
//           Consumer in EX). This is "cheap" - just reading from the nearby
//           EX/MEM register.
// - (WB→EX removed): Now handled by WB→ID in svc_rv_fwd_id. For loads on
//           BRAM, the hazard unit stalls until load reaches WB, then WB→ID
//           forwards the result.
//
// Cannot forward from MEM stage:
// - Load results on BRAM (data not ready until WB)
// - CSR results (data not ready until WB)
// - (Load results on SRAM ARE ready in MEM and can be forwarded)
//
// Multi-cycle ops (div/rem):
// - No forwarding to MC ops - use pipeline register values directly
// - Hazard unit stalls if there's a dependency until value is in regfile
// - Pipeline register holds stable rs1_data_ex/rs2_data_ex during MC execution
// - This removes FSM state from the forwarding critical path
//
// TODO: Consider making WB→EX configurable for timing-relaxed designs.
module svc_rv_fwd_ex #(
    parameter int XLEN,
    parameter int FWD,
    parameter int MEM_TYPE
) (
    //
    // EX stage inputs (consumers)
    //
    input logic [     4:0] rs1_ex,
    input logic [     4:0] rs2_ex,
    input logic [XLEN-1:0] rs1_data_ex,
    input logic [XLEN-1:0] rs2_data_ex,

    //
    // Multi-cycle operation indicator (registered, from decode)
    //
    // When is_mc_ex=1, disable forwarding entirely. The pipeline register
    // holds stable rs1_data_ex/rs2_data_ex values during MC execution.
    // Hazard unit handles stalls for any dependencies.
    //
    input logic is_mc_ex,

    //
    // MEM stage inputs
    //
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic [     2:0] res_src_mem,
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] ld_data_mem,

    //
    // Forwarded outputs
    //
    output logic [XLEN-1:0] fwd_rs1_ex,
    output logic [XLEN-1:0] fwd_rs2_ex
);

  `include "svc_rv_defs.svh"

  if (FWD != 0) begin : g_forwarding
    //
    // Decode result source to determine forwarding eligibility
    //
    logic is_ld_mem;
    logic is_csr_mem;
    logic is_m_result_mem;

    assign is_ld_mem       = (res_src_mem == RES_MEM);
    assign is_csr_mem      = (res_src_mem == RES_CSR);
    assign is_m_result_mem = (res_src_mem == RES_M);

    //
    // MEM→EX result forwarding (common to both SRAM and BRAM)
    //
    // Forward results from MEM stage (ALU, etc). Do NOT forward: loads, CSRs,
    // or M extension results (2-stage multiply). M extension results are
    // treated like BRAM loads - not available until WB.
    //
    // Disable forwarding entirely for multi-cycle ops (is_mc_ex) - they use
    // stable pipeline register values directly.
    //
    logic mem_to_ex_fwd_a;
    logic mem_to_ex_fwd_b;

    always_comb begin
      mem_to_ex_fwd_a = 1'b0;
      mem_to_ex_fwd_b = 1'b0;

      if (!is_mc_ex && reg_write_mem && rd_mem != 5'd0 && !is_ld_mem &&
          !is_csr_mem && !is_m_result_mem) begin
        mem_to_ex_fwd_a = (rd_mem == rs1_ex);
        mem_to_ex_fwd_b = (rd_mem == rs2_ex);
      end
    end

    if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_sram_load_fwd
      //
      // SRAM: Load data is ready in MEM stage, can forward
      //
      logic mem_to_ex_fwd_load_a;
      logic mem_to_ex_fwd_load_b;

      //
      // MEM→EX load forwarding (SRAM only)
      //
      always_comb begin
        mem_to_ex_fwd_load_a = 1'b0;
        mem_to_ex_fwd_load_b = 1'b0;

        if (!is_mc_ex && reg_write_mem && rd_mem != 5'd0 && is_ld_mem) begin
          mem_to_ex_fwd_load_a = (rd_mem == rs1_ex);
          mem_to_ex_fwd_load_b = (rd_mem == rs2_ex);
        end
      end

      //
      // Forwarding muxes with priority:
      // MEM load > MEM result > regfile
      //
      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_a: fwd_rs1_ex = ld_data_mem;
          mem_to_ex_fwd_a:      fwd_rs1_ex = result_mem;
          default:              fwd_rs1_ex = rs1_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_b: fwd_rs2_ex = ld_data_mem;
          mem_to_ex_fwd_b:      fwd_rs2_ex = result_mem;
          default:              fwd_rs2_ex = rs2_data_ex;
        endcase
      end

    end else begin : g_bram_no_load_fwd
      //
      // BRAM: Load data not ready in MEM stage, cannot forward
      //
      // Forwarding muxes with priority:
      // MEM result > regfile
      //
      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_a: fwd_rs1_ex = result_mem;
          default:         fwd_rs1_ex = rs1_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_b: fwd_rs2_ex = result_mem;
          default:         fwd_rs2_ex = rs2_data_ex;
        endcase
      end

      `SVC_UNUSED({ld_data_mem});
    end

  end else begin : g_no_forwarding
    //
    // No forwarding, just pass through
    //
    assign fwd_rs1_ex = rs1_data_ex;
    assign fwd_rs2_ex = rs2_data_ex;

    // verilog_format: off
    `SVC_UNUSED({rs1_ex, rs2_ex, rd_mem, reg_write_mem,
                 res_src_mem, result_mem, ld_data_mem, is_mc_ex, MEM_TYPE});
    // verilog_format: on
  end

endmodule

`endif
