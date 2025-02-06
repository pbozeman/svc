`ifndef SVC_FB_PIX_SV
`define SVC_FB_PIX_SV

`include "svc.sv"
`include "svc_unused.sv"

// Sends a frame buffer as a pixel stream
module svc_fb_pix #(
    parameter H_WIDTH        = 12,
    parameter V_WIDTH        = 12,
    parameter COLOR_WIDTH    = 4,
    parameter AXI_ADDR_WIDTH = 12,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    output logic                   m_pix_valid,
    output logic [COLOR_WIDTH-1:0] m_pix_red,
    output logic [COLOR_WIDTH-1:0] m_pix_grn,
    output logic [COLOR_WIDTH-1:0] m_pix_blu,
    input  logic                   m_pix_ready,

    input logic [H_WIDTH-1:0] h_visible,
    input logic [V_WIDTH-1:0] v_visible,

    output logic                      m_axi_arvalid,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic [               1:0] m_axi_rresp,
    input  logic                      m_axi_rlast,
    output logic                      m_axi_rready
);
  // Note: if there is some future weird resolution that isn't divisible by
  // 128, this module will need to be updated.
  localparam BURST_LEN = 128;
  localparam BURST_SHIFT = $clog2(BURST_LEN);

  localparam WORD_SIZE = AXI_DATA_WIDTH / 8;
  localparam WORD_SHIFT = $clog2(WORD_SIZE);

  localparam BW = H_WIDTH + V_WIDTH - $clog2(BURST_LEN);
  localparam AW = AXI_ADDR_WIDTH;

  localparam PIXEL_WIDTH = COLOR_WIDTH * 3;

  logic [BW-1:0] burst_total;
  logic [AW-1:0] burst_bytes;

  logic [BW-1:0] burst_cnt;
  logic [BW-1:0] burst_cnt_next;

  logic [AW-1:0] burst_addr;
  logic [AW-1:0] burst_addr_next;

  logic          m_axi_arvalid_next;
  logic [AW-1:0] m_axi_araddr_next;

  // if this becomes an issue for timing, pass it in with x_visible since all
  // the values are actually known ahead of time, even if the set we use is
  // dynamic
  assign burst_total = ((h_visible * v_visible) >> BURST_SHIFT);
  assign burst_bytes = BURST_LEN << WORD_SHIFT;

  // fixed ar values
  assign m_axi_arid = 0;
  assign m_axi_arsize = `SVC_MAX_AXSIZE(AXI_DATA_WIDTH);
  assign m_axi_arburst = 2'b01;
  assign m_axi_arlen = BURST_LEN - 1;

  // directly connect the r channel signals to the pixel stream
  assign m_pix_valid = m_axi_rvalid;
  assign {m_pix_red, m_pix_grn, m_pix_blu} = m_axi_rdata[PIXEL_WIDTH-1:0];
  assign m_axi_rready = m_pix_ready;

  // pipeline the AR setup. Don't wait for rlast before starting the next one.
  always_comb begin
    m_axi_arvalid_next = m_axi_arvalid && !m_axi_arready;
    m_axi_araddr_next  = m_axi_araddr;

    burst_cnt_next     = burst_cnt;
    burst_addr_next    = burst_addr;

    if (!m_axi_arvalid || m_axi_arready) begin
      m_axi_arvalid_next = 1'b1;
      m_axi_araddr_next  = burst_addr;

      if (burst_cnt != burst_total) begin
        burst_cnt_next  = burst_cnt + 1;
        burst_addr_next = burst_addr + burst_bytes;
      end else begin
        burst_addr_next = 0;
        burst_cnt_next  = 0;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      burst_cnt     <= 0;
      burst_addr    <= 0;

      m_axi_arvalid <= 1'b0;
    end else begin
      burst_cnt     <= burst_cnt_next;
      burst_addr    <= burst_addr_next;

      m_axi_arvalid <= m_axi_arvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    m_axi_araddr <= m_axi_araddr_next;
  end

  `SVC_UNUSED({m_axi_rid, m_axi_rresp, m_axi_rdata, m_axi_rlast,
               h_visible[BURST_SHIFT-1:0]});

endmodule
`endif
