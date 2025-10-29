`ifndef SVC_AXI_TGEN_RD_SV
`define SVC_AXI_TGEN_RD_SV

`include "svc.sv"
`include "svc_unused.sv"

module svc_axi_tgen_rd #(
    parameter AXI_ADDR_WIDTH = 20,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4
) (
    input logic clk,
    input logic rst_n,

    input  logic start,
    output logic busy,

    input logic [AXI_ADDR_WIDTH-1:0] base_addr,
    input logic [  AXI_ID_WIDTH-1:0] burst_id,
    input logic [               7:0] burst_beats,
    input logic [AXI_ADDR_WIDTH-1:0] burst_stride,
    input logic [               2:0] burst_arsize,
    input logic [              15:0] burst_num,

    output logic                      m_axi_arvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_arid,
    output logic [               7:0] m_axi_arlen,
    output logic [               2:0] m_axi_arsize,
    output logic [               1:0] m_axi_arburst,
    input  logic                      m_axi_arready,
    input  logic                      m_axi_rvalid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axi_rdata,
    input  logic                      m_axi_rlast,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_rid,
    input  logic [               1:0] m_axi_rresp,
    output logic                      m_axi_rready
);
  localparam AW = AXI_ADDR_WIDTH;

  typedef enum {
    STATE_IDLE,
    STATE_BURST_INIT,
    STATE_BURST,
    STATE_DONE
  } state_t;

  state_t          state;
  state_t          state_next;

  logic            busy_next;

  logic            m_axi_arvalid_next;
  logic   [AW-1:0] m_axi_araddr_next;
  logic   [   7:0] m_axi_arlen_next;

  logic            m_axi_rready_next;

  logic   [AW-1:0] burst_addr;
  logic   [AW-1:0] burst_addr_next;

  logic   [  15:0] burst_cnt;
  logic   [  15:0] burst_cnt_next;

  logic   [   7:0] beat_cnt;
  logic   [   7:0] beat_cnt_next;

  assign m_axi_arsize  = burst_arsize;
  assign m_axi_arid    = burst_id;
  assign m_axi_arburst = 2'b01;

  always_comb begin
    state_next         = state;
    busy_next          = busy;

    burst_addr_next    = burst_addr;
    burst_cnt_next     = burst_cnt;
    beat_cnt_next      = beat_cnt;

    m_axi_arvalid_next = m_axi_arvalid && !m_axi_arready;
    m_axi_araddr_next  = m_axi_araddr;
    m_axi_arlen_next   = m_axi_arlen;

    m_axi_rready_next  = 1'b1;

    case (state)
      STATE_IDLE: begin
        busy_next = 1'b0;
        if (start) begin
          state_next      = STATE_BURST_INIT;
          busy_next       = 1'b1;
          burst_addr_next = base_addr;

          burst_cnt_next  = 0;
          beat_cnt_next   = 0;
        end
      end

      STATE_BURST_INIT: begin
        if (!m_axi_arvalid || m_axi_arready) begin
          state_next         = STATE_BURST;

          m_axi_arvalid_next = 1'b1;
          m_axi_araddr_next  = burst_addr;
          m_axi_arlen_next   = burst_beats - 1;
        end
      end

      STATE_BURST: begin
        if (m_axi_rvalid && m_axi_rready) begin
          beat_cnt_next = beat_cnt + 1;

          if (m_axi_rlast) begin
            burst_cnt_next = burst_cnt + 1;

            if (burst_cnt_next != burst_num) begin
              state_next      = STATE_BURST_INIT;
              beat_cnt_next   = 0;
              burst_addr_next = burst_addr + burst_stride;
            end else begin
              state_next = STATE_DONE;
            end
          end
        end
      end

      STATE_DONE: begin
        state_next = STATE_IDLE;
        busy_next  = 1'b0;
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state         <= STATE_IDLE;
      busy          <= 1'b0;

      m_axi_arvalid <= 1'b0;
      m_axi_rready  <= 1'b1;
    end else begin
      state         <= state_next;
      busy          <= busy_next;

      m_axi_arvalid <= m_axi_arvalid_next;
      m_axi_rready  <= m_axi_rready_next;
    end
  end

  always_ff @(posedge clk) begin
    burst_addr   <= burst_addr_next;
    burst_cnt    <= burst_cnt_next;
    beat_cnt     <= beat_cnt_next;

    m_axi_araddr <= m_axi_araddr_next;
    m_axi_arlen  <= m_axi_arlen_next;
  end

  `SVC_UNUSED({m_axi_rid, m_axi_rdata, m_axi_rresp});

endmodule
`endif
