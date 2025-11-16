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
// TIMING NOTE: WB→EX forwarding was removed to improve timing. The WB
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
// TODO: Consider making WB→EX configurable for timing-relaxed designs.
//
module svc_rv_fwd_ex #(
    parameter int XLEN     = 32,
    parameter int FWD      = 0,
    parameter int MEM_TYPE = 0
) (
    //
    // EX stage inputs (consumers)
    //
    input logic [     4:0] rs1_ex,
    input logic [     4:0] rs2_ex,
    input logic [XLEN-1:0] rs1_data_ex,
    input logic [XLEN-1:0] rs2_data_ex,

    //
    // MEM stage inputs (producer)
    //
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic [     2:0] res_src_mem,
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] load_data_mem,

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
    logic is_load_mem;
    logic is_csr_mem;

    assign is_load_mem = (res_src_mem == RES_MEM);
    assign is_csr_mem  = (res_src_mem == RES_CSR);

    //
    // MEM→EX result forwarding (common to both SRAM and BRAM)
    //
    // Forward results from MEM stage (ALU, Zmmul, etc - not loads or CSRs)
    //
    logic mem_to_ex_fwd_a;
    logic mem_to_ex_fwd_b;

    always_comb begin
      mem_to_ex_fwd_a = 1'b0;
      mem_to_ex_fwd_b = 1'b0;

      if (reg_write_mem && rd_mem != 5'd0 && !is_load_mem && !is_csr_mem) begin
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

        if (reg_write_mem && rd_mem != 5'd0 && is_load_mem) begin
          mem_to_ex_fwd_load_a = (rd_mem == rs1_ex);
          mem_to_ex_fwd_load_b = (rd_mem == rs2_ex);
        end
      end

      //
      // Forwarding muxes with priority: MEM load > MEM result > regfile
      //
      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_a: fwd_rs1_ex = load_data_mem;
          mem_to_ex_fwd_a:      fwd_rs1_ex = result_mem;
          default:              fwd_rs1_ex = rs1_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_b: fwd_rs2_ex = load_data_mem;
          mem_to_ex_fwd_b:      fwd_rs2_ex = result_mem;
          default:              fwd_rs2_ex = rs2_data_ex;
        endcase
      end

    end else begin : g_bram_no_load_fwd
      //
      // BRAM: Load data not ready in MEM stage, cannot forward
      //
      // Forwarding muxes with priority: MEM result > regfile
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

      `SVC_UNUSED({load_data_mem});
    end

  end else begin : g_no_forwarding
    //
    // No forwarding, just pass through
    //
    assign fwd_rs1_ex = rs1_data_ex;
    assign fwd_rs2_ex = rs2_data_ex;

    // verilog_format: off
    `SVC_UNUSED({rs1_ex, rs2_ex, rd_mem, reg_write_mem, res_src_mem,
                 result_mem, load_data_mem, MEM_TYPE});
    // verilog_format: on
  end

endmodule

`endif
