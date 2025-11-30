`ifndef SVC_RV_FWD_ID_SV
`define SVC_RV_FWD_ID_SV

`include "svc.sv"
`include "svc_unused.sv"

//
// RISC-V ID stage data forwarding unit
//
// Forwards results from later pipeline stages (MEM, WB) back to ID stage
// to resolve data hazards without stalling.
//
module svc_rv_fwd_id #(
    parameter int XLEN,
    parameter int MEM_TYPE
) (
    input logic clk,

    //
    // ID stage register indices and data
    //
    input logic [     4:0] rs1_id,
    input logic [     4:0] rs2_id,
    input logic [XLEN-1:0] rs1_data_id,
    input logic [XLEN-1:0] rs2_data_id,

    //
    // MEM stage forwarding source
    //
    input logic [     4:0] rd_mem,
    input logic            reg_write_mem,
    input logic [     2:0] res_src_mem,
    input logic [XLEN-1:0] result_mem,
    input logic [XLEN-1:0] load_data_mem,

    //
    // WB stage forwarding source
    //
    input logic [     4:0] rd_wb,
    input logic            reg_write_wb,
    input logic [XLEN-1:0] rd_data_wb,

    //
    // Forwarded outputs
    //
    output logic [XLEN-1:0] fwd_rs1_id,
    output logic [XLEN-1:0] fwd_rs2_id
);

  `include "svc_rv_defs.svh"

  //
  // Decode result source to determine forwarding eligibility
  //
  logic is_load_mem;
  logic is_csr_mem;
  logic is_m_result_mem;

  assign is_load_mem     = (res_src_mem == RES_MEM);
  assign is_csr_mem      = (res_src_mem == RES_CSR);
  assign is_m_result_mem = (res_src_mem == RES_M);

  //
  // MEM→ID result forwarding (common to both SRAM and BRAM)
  //
  // Forward results from MEM stage (ALU, etc).
  // Do NOT forward: loads, CSRs, or M extension results (2-stage multiply).
  // M extension results are treated like BRAM loads - not available until WB.
  //
  logic mem_to_id_fwd_a;
  logic mem_to_id_fwd_b;

  always_comb begin
    mem_to_id_fwd_a = 1'b0;
    mem_to_id_fwd_b = 1'b0;

    if (reg_write_mem && rd_mem != 5'd0 && !is_load_mem && !is_csr_mem &&
        !is_m_result_mem) begin
      mem_to_id_fwd_a = (rd_mem == rs1_id);
      mem_to_id_fwd_b = (rd_mem == rs2_id);
    end
  end

  //
  // WB→ID forwarding
  //
  logic wb_fwd_rs1;
  logic wb_fwd_rs2;

  always_comb begin
    wb_fwd_rs1 = 1'b0;
    wb_fwd_rs2 = 1'b0;

    if (reg_write_wb && rd_wb != 5'd0) begin
      wb_fwd_rs1 = (rd_wb == rs1_id);
      wb_fwd_rs2 = (rd_wb == rs2_id);
    end
  end

  if (MEM_TYPE == MEM_TYPE_SRAM) begin : g_sram_load_fwd
    //
    // SRAM: Load data is ready in MEM stage, can forward
    //
    logic mem_to_id_fwd_load_a;
    logic mem_to_id_fwd_load_b;

    //
    // MEM→ID load forwarding (SRAM only)
    //
    always_comb begin
      mem_to_id_fwd_load_a = 1'b0;
      mem_to_id_fwd_load_b = 1'b0;

      if (reg_write_mem && rd_mem != 5'd0 && is_load_mem) begin
        mem_to_id_fwd_load_a = (rd_mem == rs1_id);
        mem_to_id_fwd_load_b = (rd_mem == rs2_id);
      end
    end

    //
    // Forwarding muxes with priority: MEM load > MEM result > WB > regfile
    //
    always_comb begin
      case (1'b1)
        mem_to_id_fwd_load_a: fwd_rs1_id = load_data_mem;
        mem_to_id_fwd_a:      fwd_rs1_id = result_mem;
        wb_fwd_rs1:           fwd_rs1_id = rd_data_wb;
        default:              fwd_rs1_id = rs1_data_id;
      endcase
    end

    always_comb begin
      case (1'b1)
        mem_to_id_fwd_load_b: fwd_rs2_id = load_data_mem;
        mem_to_id_fwd_b:      fwd_rs2_id = result_mem;
        wb_fwd_rs2:           fwd_rs2_id = rd_data_wb;
        default:              fwd_rs2_id = rs2_data_id;
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
        mem_to_id_fwd_a: fwd_rs1_id = result_mem;
        wb_fwd_rs1:      fwd_rs1_id = rd_data_wb;
        default:         fwd_rs1_id = rs1_data_id;
      endcase
    end

    always_comb begin
      case (1'b1)
        mem_to_id_fwd_b: fwd_rs2_id = result_mem;
        wb_fwd_rs2:      fwd_rs2_id = rd_data_wb;
        default:         fwd_rs2_id = rs2_data_id;
      endcase
    end

    `SVC_UNUSED({load_data_mem});
  end

  `SVC_UNUSED({clk, XLEN});

endmodule

`endif
