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

`ifdef FORMAL
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE

  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  faxi_slave #(
      .C_AXI_ID_WIDTH    (AXI_ID_WIDTH),
      .C_AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
      .C_AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
      .F_AXI_MAXSTALL    (0),
      .F_AXI_MAXRSTALL   (3),
      .F_OPT_INITIAL     (0),
      .OPT_EXCLUSIVE     (0),
      .F_AXI_MAXDELAY    (0),
      .F_OPT_ASSUME_RESET(1)
  ) faxi_subordinate_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      // Write address
      .i_axi_awready(),
      .i_axi_awid   (),
      .i_axi_awaddr (),
      .i_axi_awlen  (),
      .i_axi_awsize (),
      .i_axi_awburst(),
      .i_axi_awlock (0),
      .i_axi_awcache(0),
      .i_axi_awprot (0),
      .i_axi_awqos  (0),
      .i_axi_awvalid(0),

      // Write data
      .i_axi_wready(),
      .i_axi_wdata (),
      .i_axi_wstrb (),
      .i_axi_wlast (),
      .i_axi_wvalid(0),

      // Write return response
      .i_axi_bid   (),
      .i_axi_bresp (),
      .i_axi_bvalid(0),
      .i_axi_bready(),

      // Read address
      .i_axi_arready(s_axi_arready),
      .i_axi_arid   (s_axi_arid),
      .i_axi_araddr (s_axi_araddr),
      .i_axi_arlen  (s_axi_arlen),
      .i_axi_arsize (s_axi_arsize),
      .i_axi_arburst(s_axi_arburst),
      .i_axi_arlock (0),
      .i_axi_arcache(0),
      .i_axi_arprot (0),
      .i_axi_arqos  (0),
      .i_axi_arvalid(s_axi_arvalid),

      // Read response
      .i_axi_rid   (s_axi_rid),
      .i_axi_rresp (s_axi_rresp),
      .i_axi_rvalid(s_axi_rvalid),
      .i_axi_rdata (s_axi_rdata),
      .i_axi_rlast (s_axi_rlast),
      .i_axi_rready(s_axi_rready),

      .f_axi_awr_nbursts   (),
      .f_axi_wr_pending    (),
      .f_axi_rd_nbursts    (),
      .f_axi_rd_outstanding(),

      // Write burst properties
      .f_axi_wr_checkid  (),
      .f_axi_wr_ckvalid  (),
      .f_axi_wrid_nbursts(),
      .f_axi_wr_addr     (),
      .f_axi_wr_incr     (),
      .f_axi_wr_burst    (),
      .f_axi_wr_size     (),
      .f_axi_wr_len      (),
      .f_axi_wr_lockd    (),

      // Read properties
      .f_axi_rd_checkid(),
      .f_axi_rd_ckvalid(),
      .f_axi_rd_cklen  (),
      .f_axi_rd_ckaddr (),
      .f_axi_rd_ckincr (),
      .f_axi_rd_ckburst(),
      .f_axi_rd_cksize (),
      .f_axi_rd_ckarlen(),
      .f_axi_rd_cklockd(),

      .f_axi_rdid_nbursts          (),
      .f_axi_rdid_outstanding      (),
      .f_axi_rdid_ckign_nbursts    (),
      .f_axi_rdid_ckign_outstanding(),

      // Exclusive access handling
      .f_axi_ex_state              (),
      .f_axi_ex_checklock          (),
      .f_axi_rdid_bursts_to_lock   (),
      .f_axi_wrid_bursts_to_exwrite(),

      .f_axi_exreq_addr  (),
      .f_axi_exreq_len   (),
      .f_axi_exreq_burst (),
      .f_axi_exreq_size  (),
      .f_axi_exreq_return(),

      .i_active_lock (0),
      .i_exlock_addr (),
      .i_exlock_len  (),
      .i_exlock_burst(),
      .i_exlock_size ()

  );

  faxil_master #(
      .C_AXI_DATA_WIDTH  (AXI_DATA_WIDTH),
      .C_AXI_ADDR_WIDTH  (AXI_ADDR_WIDTH),
      .F_AXI_MAXWAIT     (5),
      .F_AXI_MAXDELAY    (4),
      .F_AXI_MAXRSTALL   (0),
      .F_OPT_READ_ONLY   (1),
      .F_OPT_INITIAL     (0),
      .F_OPT_ASSUME_RESET(1)
  ) faxil_manager_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      // Write address channel
      .i_axi_awvalid(0),
      .i_axi_awready(),
      .i_axi_awaddr (),
      .i_axi_awprot (),

      // Write data
      .i_axi_wready(),
      .i_axi_wdata (),
      .i_axi_wstrb (),
      .i_axi_wvalid(0),

      // Write response
      .i_axi_bresp (),
      .i_axi_bvalid(0),
      .i_axi_bready(),

      // Read address
      .i_axi_arvalid(m_axil_arvalid),
      .i_axi_arready(m_axil_arready),
      .i_axi_araddr (m_axil_araddr),
      .i_axi_arprot (0),

      // Read data return
      .i_axi_rvalid(m_axil_rvalid),
      .i_axi_rready(m_axil_rready),
      .i_axi_rdata (m_axil_rdata),
      .i_axi_rresp (m_axil_rresp),

      // Formal check variables
      .f_axi_rd_outstanding (),
      .f_axi_wr_outstanding (),
      .f_axi_awr_outstanding()
  );

  // TODO: this can likely be reduced to 1 with a skidbuffer on the input
  // to the adpater and then driving the axil side in the same clock as
  // the axi addr inputs.
  localparam F_FIRST_BEAT_LATENCY = 2;

  // TODO: fix the beat latency and then do N of these checks in a row.
  // Do this before the first beat latency, as the first beat latency is
  // acceptable for my use cases, but this is not.
  localparam F_BEAT_LATENCY = 2;
  always @(posedge clk) begin
    if ((f_past_valid) && (rst_n)) begin
      c_beat_per_clk :
      cover ((s_axi_rready && s_axi_rvalid) && $past(
          s_axi_rready && s_axi_rvalid, F_BEAT_LATENCY
      ) && $past(
          (s_axi_arvalid && s_axi_arready && s_axi_arlen == 3),
          F_FIRST_BEAT_LATENCY + F_BEAT_LATENCY
      ));
    end
  end

`endif
`endif

endmodule
`endif
