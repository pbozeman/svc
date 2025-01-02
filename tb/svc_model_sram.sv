`ifndef SVC_MODEL_SRAM_SV
`define SVC_MODEL_SRAM_SV

`include "svc.sv"

module svc_model_sram #(
    parameter UNITIALIZED_READS_OK = 0,
    parameter SRAM_ADDR_WIDTH      = 8,
    parameter SRAM_DATA_WIDTH      = 16,
    parameter SRAM_STRB_WIDTH      = (SRAM_DATA_WIDTH / 8),
    parameter SRAM_META_WIDTH      = 4
) (
    input logic clk,
    input logic rst_n,

    input  logic                       sram_cmd_valid,
    output logic                       sram_cmd_ready,
    input  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    input  logic [SRAM_META_WIDTH-1:0] sram_cmd_meta,
    input  logic                       sram_cmd_last,
    input  logic                       sram_cmd_wr_en,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    input  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,
    output logic                       sram_rd_resp_valid,
    input  logic                       sram_rd_resp_ready,
    output logic [SRAM_DATA_WIDTH-1:0] sram_rd_resp_data,
    output logic [SRAM_META_WIDTH-1:0] sram_rd_resp_meta,
    output logic                       sram_rd_resp_last
);
  // Memory array to store data
  logic [SRAM_DATA_WIDTH-1:0] mem               [(1 << SRAM_ADDR_WIDTH)-1:0];

  // Read response pipeline control
  logic                       read_pending;
  logic [SRAM_DATA_WIDTH-1:0] pending_read_data;
  logic [SRAM_META_WIDTH-1:0] pending_meta;
  logic                       pending_last;

  // Ready to accept new commands when not processing a read
  assign sram_cmd_ready = !read_pending || (read_pending && sram_rd_resp_ready);

  // Read response handling
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      sram_rd_resp_valid <= '0;
      read_pending       <= '0;
      pending_read_data  <= '0;

      // Initialize memory to X
      for (int i = 0; i < (1 << SRAM_ADDR_WIDTH); i++) begin
        mem[i] <= 'x;
      end
    end else begin
      if (sram_cmd_valid && sram_cmd_ready && !sram_cmd_wr_en) begin
        if (mem[sram_cmd_addr] === 'x && UNITIALIZED_READS_OK) begin
          pending_read_data = SRAM_DATA_WIDTH'(sram_cmd_addr);
        end else begin
          pending_read_data <= mem[sram_cmd_addr];
        end
        read_pending       <= 1'b1;
        sram_rd_resp_valid <= 1'b1;
      end else begin
        if (sram_rd_resp_valid && sram_rd_resp_ready) begin
          sram_rd_resp_valid <= 1'b0;
          read_pending       <= 1'b0;
        end
      end
    end
  end

  // Write handling - process writes byte by byte based on write strobe
  always_ff @(posedge clk) begin
    if (sram_cmd_valid && sram_cmd_ready && sram_cmd_wr_en) begin
      for (int i = 0; i < SRAM_STRB_WIDTH; i++) begin
        if (sram_cmd_wr_strb[i]) begin
          mem[sram_cmd_addr][i*8+:8] <= sram_cmd_wr_data[i*8+:8];
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (sram_cmd_valid && sram_cmd_ready) begin
      pending_meta <= sram_cmd_meta;
      pending_last <= sram_cmd_last;
    end
  end

  // Drive read response data
  assign sram_rd_resp_data = pending_read_data;
  assign sram_rd_resp_meta = pending_meta;
  assign sram_rd_resp_last = pending_last;
endmodule

`endif
