`ifndef SVC_MODEL_SRAM_IF_SV
`define SVC_MODEL_SRAM_IF_SV

`include "svc.sv"
`include "svc_sync_fifo.sv"

module svc_model_sram_if #(
    parameter UNITIALIZED_READS_OK = 0,
    parameter SRAM_ADDR_WIDTH      = 4,
    parameter SRAM_DATA_WIDTH      = 16,
    parameter SRAM_STRB_WIDTH      = (SRAM_DATA_WIDTH / 8)
) (
    input logic clk,
    input logic rst_n,

    input  logic                       sram_cmd_valid,
    output logic                       sram_cmd_ready,
    input  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    input  logic                       sram_cmd_wr_en,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    input  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,
    output logic                       sram_resp_valid,
    input  logic                       sram_resp_ready,
    output logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data
);
  localparam FIFO_DATA_WIDTH = SRAM_DATA_WIDTH;

  // Memory array to store data
  logic [SRAM_DATA_WIDTH-1:0] mem              [(1 << SRAM_ADDR_WIDTH)-1:0];

  // result fifo
  logic                       fifo_w_inc;
  logic [FIFO_DATA_WIDTH-1:0] fifo_w_data;
  logic                       fifo_w_half_full;

  logic                       fifo_r_inc;
  logic                       fifo_r_empty;
  logic [FIFO_DATA_WIDTH-1:0] fifo_r_data;

  svc_sync_fifo #(
      .ADDR_WIDTH(2),
      .DATA_WIDTH(FIFO_DATA_WIDTH)
  ) svc_sync_fifo_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (fifo_w_inc),
      .w_data     (fifo_w_data),
      .w_full     (),
      .w_half_full(fifo_w_half_full),
      .r_inc      (fifo_r_inc),
      .r_empty    (fifo_r_empty),
      .r_data     (fifo_r_data)
  );

  assign fifo_w_inc = sram_cmd_valid && sram_cmd_ready && !sram_cmd_wr_en;
  assign fifo_w_data = mem[sram_cmd_addr];
  assign fifo_r_inc = sram_resp_valid && sram_resp_ready;

  assign sram_cmd_ready = !fifo_w_half_full;

  assign sram_resp_valid = !fifo_r_empty;
  assign sram_resp_rd_data = fifo_r_data;

  // Read response handling
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      // Initialize memory to X or addr
      for (int i = 0; i < (1 << SRAM_ADDR_WIDTH); i++) begin
        if (UNITIALIZED_READS_OK) begin
          mem[i] <= SRAM_DATA_WIDTH'(i);
        end else begin
          mem[i] <= 'x;
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

endmodule

`endif
