`ifndef SVC_FB_PIX_SV
`define SVC_FB_PIX_SV

`include "svc.sv"
`include "svc_sync_fifo.sv"
`include "svc_unused.sv"

// Sends a frame buffer as a pixel stream
//
// TODO: add x/y to the stream, or eol/eof like in axi video streams. This is
// because if there is ever a dropped pixel, the consumer of the pixel stream
// has no idea how many pixels were dropped and will resync to the wrong spot.
// In the pattern gen demo, this results in the color bars shifting out of
// phase with the display.

module svc_fb_pix #(
    parameter H_WIDTH         = 12,
    parameter V_WIDTH         = 12,
    parameter COLOR_WIDTH     = 4,
    parameter AXI_ADDR_WIDTH  = 16,
    parameter AXI_DATA_WIDTH  = 16,
    parameter AXI_ID_WIDTH    = 4,
    parameter FIFO_ADDR_WIDTH = 3
) (
    input logic clk,
    input logic rst_n,

    output logic                      m_pix_valid,
    output logic [   COLOR_WIDTH-1:0] m_pix_red,
    output logic [   COLOR_WIDTH-1:0] m_pix_grn,
    output logic [   COLOR_WIDTH-1:0] m_pix_blu,
    output logic [       H_WIDTH-1:0] m_pix_x,
    output logic [       V_WIDTH-1:0] m_pix_y,
    output logic [AXI_ADDR_WIDTH-1:0] m_pix_addr,
    input  logic                      m_pix_ready,

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
  localparam AW = AXI_ADDR_WIDTH;
  localparam HW = H_WIDTH;
  localparam VW = V_WIDTH;
  localparam PIXEL_WIDTH = COLOR_WIDTH * 3;

  logic [HW-1:0] x;
  logic [HW-1:0] x_next;

  logic [VW-1:0] y;
  logic [VW-1:0] y_next;

  logic          m_axi_arvalid_next;
  logic [AW-1:0] m_axi_araddr_next;

  logic          fifo_ready;

  // fixed ar values
  assign m_axi_arid                        = 0;
  assign m_axi_arsize                      = `SVC_MAX_AXSIZE(AXI_DATA_WIDTH);
  assign m_axi_arburst                     = 2'b01;
  assign m_axi_arlen                       = 0;

  // directly connect the r channel signals to the pixel stream
  assign m_pix_valid                       = m_axi_rvalid;
  assign m_axi_rready                      = m_pix_ready;
  assign {m_pix_red, m_pix_grn, m_pix_blu} = m_axi_rdata[PIXEL_WIDTH-1:0];

  always_comb begin
    m_axi_arvalid_next = m_axi_arvalid && !m_axi_arready;

    if (!m_axi_arvalid || m_axi_arready) begin
      if (fifo_ready) begin
        m_axi_arvalid_next = 1'b1;
      end
    end
  end

  always_comb begin
    x_next            = x;
    y_next            = y;
    m_axi_araddr_next = m_axi_araddr;

    if (m_axi_arvalid && m_axi_arready) begin
      m_axi_araddr_next = m_axi_araddr + (1 << m_axi_arsize);

      if (x < h_visible - 1) begin
        x_next = x + 1;
      end else begin
        x_next = 0;

        if (y < v_visible - 1) begin
          y_next = y + 1;
        end else begin
          y_next            = 0;
          m_axi_araddr_next = 0;
        end
      end
    end
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      x             <= 0;
      y             <= 0;
      m_axi_arvalid <= 1'b0;
      m_axi_araddr  <= 0;
    end else begin
      x             <= x_next;
      y             <= y_next;
      m_axi_arvalid <= m_axi_arvalid_next;
      m_axi_araddr  <= m_axi_araddr_next;
    end
  end

  logic fifo_w_half_full;
  assign fifo_ready = !fifo_w_half_full;

  svc_sync_fifo #(
      .DATA_WIDTH(HW + VW + AW),
      .ADDR_WIDTH(FIFO_ADDR_WIDTH)
  ) svc_sync_fifo_i (
      .clk        (clk),
      .rst_n      (rst_n),
      .w_inc      (m_axi_arvalid && m_axi_arready),
      .w_data     ({x, y, m_axi_araddr}),
      .w_full     (),
      .w_half_full(fifo_w_half_full),
      .r_inc      (m_pix_valid && m_pix_ready),
      .r_empty    (),
      .r_data     ({m_pix_x, m_pix_y, m_pix_addr})
  );

  `SVC_UNUSED({m_axi_rid, m_axi_rresp, m_axi_rdata, m_axi_rlast});

`ifdef FORMAL
`ifdef ZIPCPU_PRIVATE
`ifdef FORMAL_SVC_FB_PIX
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  logic f_past_valid = 0;
  always @(posedge clk) begin
    f_past_valid <= 1;
  end

  always @(posedge clk) begin
    if (!f_past_valid) begin
      assume (rst_n == 0);
    end
  end

  // m_valid stability
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      // m_pix_valid should remain stable when m_pix_ready is low
      if ($past(m_pix_valid && !m_pix_ready)) begin
        `ASSERT(as_m_pix_valid_stable, m_pix_valid);
      end
    end
  end

  logic [3:0] stall_cnt;
  always @(posedge clk) begin
    if (!rst_n) begin
      stall_cnt <= 0;
    end else begin
      if (m_pix_valid) begin
        if (m_pix_ready) begin
          stall_cnt <= 0;
        end else begin
          stall_cnt <= stall_cnt + 1;
        end
      end
    end
  end

`ifdef FORMAL_SVC_FB_PIX
  // We don't to make such an assertion for our callers
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      assume (stall_cnt < 2);
    end
  end
`endif

  // data stability assertions
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n)) begin
      // output signals should be stable until accepted
      if ($past(m_pix_valid && !m_pix_ready) && !m_pix_ready) begin
        `ASSERT(as_stable_m_pix_red, $stable(m_pix_red));
        `ASSERT(as_stable_m_pix_grn, $stable(m_pix_grn));
        `ASSERT(as_stable_m_pix_blu, $stable(m_pix_blu));
        `ASSERT(as_stable_m_pix_x, $stable(m_pix_x));
        `ASSERT(as_stable_m_pix_y, $stable(m_pix_y));
        `ASSERT(as_stable_m_pix_addr, $stable(m_pix_addr));
      end
    end
  end

  // verilator lint_off: PINMISSING
  faxi_master #(
      .C_AXI_ID_WIDTH  (AXI_ID_WIDTH),
      .C_AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .F_OPT_INITIAL   (1'b0),
      .OPT_EXCLUSIVE   (1'b0),
      .OPT_NARROW_BURST(1'b0),
      .F_LGDEPTH       (9),
      .F_AXI_MAXSTALL  (3),
      .F_AXI_MAXRSTALL (2),
      .F_AXI_MAXDELAY  (3)
  ) faxi_manager_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),
      .i_axi_awvalid(1'b0),
      .i_axi_awready(1'b0),
      .i_axi_awid   (0),
      .i_axi_awaddr (0),
      .i_axi_awlen  (0),
      .i_axi_awsize (0),
      .i_axi_awburst(0),
      .i_axi_awlock (0),
      .i_axi_awcache(0),
      .i_axi_awprot (0),
      .i_axi_awqos  (0),
      .i_axi_wvalid (0),
      .i_axi_wready (0),
      .i_axi_wdata  (0),
      .i_axi_wstrb  (0),
      .i_axi_wlast  (0),
      .i_axi_bvalid (1'b0),
      .i_axi_bready (1'b0),
      .i_axi_bid    (0),
      .i_axi_bresp  (2'b00),

      .i_axi_arvalid(m_axi_arvalid),
      .i_axi_arready(m_axi_arready),
      .i_axi_arid   (m_axi_arid),
      .i_axi_araddr (m_axi_araddr),
      .i_axi_arlen  (m_axi_arlen),
      .i_axi_arsize (m_axi_arsize),
      .i_axi_arburst(m_axi_arburst),
      .i_axi_arlock (0),
      .i_axi_arcache(0),
      .i_axi_arprot (0),
      .i_axi_arqos  (0),
      .i_axi_rvalid (m_axi_rvalid),
      .i_axi_rready (m_axi_rready),
      .i_axi_rdata  (m_axi_rdata),
      .i_axi_rid    (m_axi_rid),
      .i_axi_rlast  (m_axi_rlast),
      .i_axi_rresp  (m_axi_rresp)
  );
  // verilator lint_on: PINMISSING
`endif

  `undef ASSERT
  `undef ASSUME
  `undef COVER
`endif

endmodule
`endif
