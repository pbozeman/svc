`ifndef SVC_AXI_TGEN_WR_SV
`define SVC_AXI_TGEN_WR_SV

`include "svc.sv"
`include "svc_unused.sv"

// AXI traffic generator for writes

module svc_axi_tgen_wr #(
    parameter AXI_ADDR_WIDTH = 20,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8
) (
    input logic clk,
    input logic rst_n,

    input  logic start,
    output logic busy,

    input logic [AXI_ADDR_WIDTH-1:0] base_addr,
    input logic [  AXI_ID_WIDTH-1:0] burst_id,
    input logic [               7:0] burst_beats,
    input logic [AXI_ADDR_WIDTH-1:0] burst_stride,
    input logic [               2:0] burst_awsize,
    input logic [              15:0] burst_num,

    output logic                      m_axi_awvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr,
    output logic [  AXI_ID_WIDTH-1:0] m_axi_awid,
    output logic [               7:0] m_axi_awlen,
    output logic [               2:0] m_axi_awsize,
    output logic [               1:0] m_axi_awburst,
    input  logic                      m_axi_awready,
    output logic                      m_axi_wvalid,
    output logic [AXI_DATA_WIDTH-1:0] m_axi_wdata,
    output logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb,
    output logic                      m_axi_wlast,
    input  logic                      m_axi_wready,
    input  logic                      m_axi_bvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m_axi_bid,
    input  logic [               1:0] m_axi_bresp,
    output logic                      m_axi_bready
);
  localparam AW = AXI_ADDR_WIDTH;
  localparam DW = AXI_DATA_WIDTH;

  typedef enum {
    STATE_IDLE,
    STATE_BURST_INIT,
    STATE_BURST,
    STATE_DONE
  } state_t;

  state_t          state;
  state_t          state_next;

  logic            busy_next;

  logic            m_axi_awvalid_next;
  logic   [AW-1:0] m_axi_awaddr_next;
  logic   [   7:0] m_axi_awlen_next;

  logic            m_axi_wvalid_next;
  logic   [DW-1:0] m_axi_wdata_next;
  logic            m_axi_wlast_next;

  logic   [AW-1:0] burst_addr;
  logic   [AW-1:0] burst_addr_next;

  logic   [  15:0] burst_cnt;
  logic   [  15:0] burst_cnt_next;

  logic   [   7:0] beat_cnt;
  logic   [   7:0] beat_cnt_next;

  assign m_axi_awsize  = burst_awsize;
  assign m_axi_awid    = burst_id;
  assign m_axi_awburst = 2'b01;

  // cap wstrb based on awsize since it might not be full
  assign m_axi_wstrb   = ((1 << (1 << burst_awsize)) - 1) & AXI_STRB_WIDTH'('1);

  assign m_axi_bready  = 1'b1;

  always_comb begin
    state_next         = state;
    busy_next          = busy;

    burst_addr_next    = burst_addr;
    burst_cnt_next     = burst_cnt;
    beat_cnt_next      = beat_cnt;

    m_axi_awvalid_next = m_axi_awvalid && !m_axi_awready;
    m_axi_awaddr_next  = m_axi_awaddr;
    m_axi_awlen_next   = m_axi_awlen;

    m_axi_wvalid_next  = m_axi_wvalid && !m_axi_wready;
    m_axi_wdata_next   = m_axi_wdata;
    m_axi_wlast_next   = m_axi_wlast;

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
        if (!m_axi_awvalid || m_axi_awready) begin
          state_next         = STATE_BURST;

          m_axi_awvalid_next = 1'b1;
          m_axi_awaddr_next  = burst_addr;
          m_axi_awlen_next   = burst_beats - 1;

          burst_cnt_next     = burst_cnt + 1;

          if (!m_axi_wvalid || m_axi_wready) begin
            beat_cnt_next     = beat_cnt + 1;
            m_axi_wvalid_next = 1'b1;

            // TODO: put something useful in the data so we can optionally
            // verify it later
            m_axi_wdata_next  = 0;
            m_axi_wlast_next  = beat_cnt_next == burst_beats;
          end
        end
      end

      STATE_BURST: begin
        if (m_axi_wvalid && m_axi_wready) begin
          if (beat_cnt != burst_beats) begin
            beat_cnt_next     = beat_cnt + 1;
            m_axi_wvalid_next = 1'b1;

            // TODO: see above
            m_axi_wdata_next  = 0;
            m_axi_wlast_next  = beat_cnt_next == burst_beats;
          end else begin
            if (burst_cnt != burst_num) begin
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

      m_axi_awvalid <= 1'b0;
      m_axi_wvalid  <= 1'b0;
    end else begin
      state         <= state_next;
      busy          <= busy_next;

      m_axi_awvalid <= m_axi_awvalid_next;
      m_axi_wvalid  <= m_axi_wvalid_next;
    end
  end

  always_ff @(posedge clk) begin
    burst_addr   <= burst_addr_next;
    burst_cnt    <= burst_cnt_next;
    beat_cnt     <= beat_cnt_next;

    m_axi_awaddr <= m_axi_awaddr_next;
    m_axi_awlen  <= m_axi_awlen_next;
    m_axi_wdata  <= m_axi_wdata_next;
    m_axi_wlast  <= m_axi_wlast_next;
  end

  `SVC_UNUSED({m_axi_bvalid, m_axi_bid, m_axi_bresp});

endmodule
`endif
