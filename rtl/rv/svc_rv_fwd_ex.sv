`ifndef SVC_RV_FWD_EX_SV
`define SVC_RV_FWD_EX_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V data forwarding unit
//
// Forwards ALU results from later pipeline stages back to EX stage to resolve
// data hazards without stalling.
//
// Two types of forwarding:
// - EX hazard (MEM→EX): Forward from MEM stage when it has the needed value
// - MEM hazard (WB→EX): Forward from WB stage when MEM doesn't have it
//
// Priority: MEM > WB > regfile (MEM is more recent)
//
// Cannot forward:
// - Load results in MEM stage for BRAM (data not ready until WB)
// - CSR results in MEM stage (data not ready until WB)
// - Load results for SRAM are available in MEM stage and CAN be forwarded
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
    // WB stage inputs (producer)
    //
    input logic [     4:0] rd_wb,
    input logic            reg_write_wb,
    input logic [XLEN-1:0] rd_data_wb,

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

    //
    // WB→EX forwarding (common to both SRAM and BRAM)
    //
    // Forward from WB stage when MEM doesn't have the value
    // Handles load results after stall, CSR reads, and older hazards
    //
    logic wb_to_ex_fwd_a;
    logic wb_to_ex_fwd_b;

    always_comb begin
      wb_to_ex_fwd_a = 1'b0;
      wb_to_ex_fwd_b = 1'b0;

      if (reg_write_wb && rd_wb != 5'd0) begin
        wb_to_ex_fwd_a = (rd_wb == rs1_ex);
        wb_to_ex_fwd_b = (rd_wb == rs2_ex);
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
      // Forwarding muxes with priority: MEM load > MEM result > WB > regfile
      //
      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_a: fwd_rs1_ex = load_data_mem;
          mem_to_ex_fwd_a:      fwd_rs1_ex = result_mem;
          wb_to_ex_fwd_a:       fwd_rs1_ex = rd_data_wb;
          default:              fwd_rs1_ex = rs1_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_load_b: fwd_rs2_ex = load_data_mem;
          mem_to_ex_fwd_b:      fwd_rs2_ex = result_mem;
          wb_to_ex_fwd_b:       fwd_rs2_ex = rd_data_wb;
          default:              fwd_rs2_ex = rs2_data_ex;
        endcase
      end

    end else begin : g_bram_no_load_fwd
      //
      // BRAM: Load data not ready in MEM stage, cannot forward
      //
      // Forwarding muxes with priority: MEM result > WB > regfile
      //
      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_a: fwd_rs1_ex = result_mem;
          wb_to_ex_fwd_a:  fwd_rs1_ex = rd_data_wb;
          default:         fwd_rs1_ex = rs1_data_ex;
        endcase
      end

      always_comb begin
        case (1'b1)
          mem_to_ex_fwd_b: fwd_rs2_ex = result_mem;
          wb_to_ex_fwd_b:  fwd_rs2_ex = rd_data_wb;
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
                 result_mem, load_data_mem, rd_wb, reg_write_wb, rd_data_wb,
                 MEM_TYPE});
    // verilog_format: on
  end

endmodule

`endif
