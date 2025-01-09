`ifndef SVC_AXI_AXIL_RD_SV
`define SVC_AXI_AXIL_RD_SV

`include "svc.sv"

// AXI to AXI-Lite adapter for reads. Buses must be the same size.

module svc_axi_axil_rd #(
    parameter AXI_ADDR_WIDTH = 4,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_arvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [               7:0] s_axi_arlen,
    input  logic [               2:0] s_axi_arsize,
    input  logic [               1:0] s_axi_arburst,
    output logic                      s_axi_arready,
    output logic                      s_axi_rvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic                      s_axi_rlast,
    input  logic                      s_axi_rready,

    //
    // AXI-Lite manager interface
    output logic                      m_axil_arvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axil_araddr,
    input  logic                      m_axil_arready,
    input  logic                      m_axil_rvalid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axil_rdata,
    input  logic [               1:0] m_axil_rresp,
    output logic                      m_axil_rready
);
  typedef enum {
    STATE_IDLE,
    STATE_BURST
  } state_t;

  state_t                      state;
  state_t                      state_next;

  logic                        s_axi_arready_next;
  logic                        s_axi_rlast_next;

  logic                        m_axil_arvalid_next;
  logic   [AXI_ADDR_WIDTH-1:0] m_axil_araddr_next;

  logic   [AXI_ADDR_WIDTH-1:0] r_addr;
  logic   [AXI_ADDR_WIDTH-1:0] r_addr_next;

  logic   [  AXI_ID_WIDTH-1:0] r_id;
  logic   [  AXI_ID_WIDTH-1:0] r_id_next;

  logic   [               7:0] r_len;
  logic   [               7:0] r_len_next;

  logic   [               2:0] r_size;
  logic   [               2:0] r_size_next;

  logic   [               1:0] r_burst;
  logic   [               1:0] r_burst_next;

  assign s_axi_rvalid  = m_axil_rvalid;
  assign s_axi_rdata   = m_axil_rdata;
  assign s_axi_rid     = r_id;
  assign s_axi_rresp   = m_axil_rresp;

  assign m_axil_rready = s_axi_rready;

  always_comb begin
    state_next          = state;

    r_addr_next         = r_addr;
    r_id_next           = r_id;
    r_len_next          = r_len;
    r_size_next         = r_size;
    r_burst_next        = r_burst;

    s_axi_arready_next  = 1'b0;
    s_axi_rlast_next    = s_axi_rlast;

    m_axil_arvalid_next = m_axil_arvalid && !m_axil_arready;
    m_axil_araddr_next  = m_axil_araddr;

    case (state)
      STATE_IDLE: begin
        s_axi_arready_next = 1'b1;

        if (s_axi_arvalid && s_axi_arready) begin
          state_next          = STATE_BURST;
          s_axi_arready_next  = 1'b0;

          r_addr_next         = s_axi_araddr;
          r_id_next           = s_axi_arid;
          r_len_next          = s_axi_arlen;
          r_size_next         = s_axi_arsize;
          r_burst_next        = s_axi_arburst;

          m_axil_arvalid_next = 1'b1;
          m_axil_araddr_next  = s_axi_araddr;

          s_axi_rlast_next    = r_len_next == 0;
        end
      end

      STATE_BURST: begin
        if (m_axil_rready && m_axil_rvalid) begin
          r_addr_next      = r_addr + (1 << r_size);
          r_len_next       = r_len - 1;
          s_axi_rlast_next = r_len_next == 0;
          if (r_len == 0) begin
            m_axil_arvalid_next = 1'b0;
            s_axi_arready_next  = 1'b1;
            state_next          = STATE_IDLE;
          end else begin
            // start new AXI lite read
            m_axil_arvalid_next = 1'b1;
            m_axil_araddr_next  = r_addr_next;
          end
        end
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      state          <= STATE_IDLE;
      s_axi_arready  <= 1'b0;
      m_axil_arvalid <= 1'b0;
    end else begin
      state          <= state_next;

      r_addr         <= r_addr_next;
      r_id           <= r_id_next;
      r_len          <= r_len_next;
      r_size         <= r_size_next;
      r_burst        <= r_burst_next;

      s_axi_arready  <= s_axi_arready_next;
      s_axi_rlast    <= s_axi_rlast_next;

      m_axil_arvalid <= m_axil_arvalid_next;
      m_axil_araddr  <= m_axil_araddr_next;
    end
  end

endmodule
`endif
