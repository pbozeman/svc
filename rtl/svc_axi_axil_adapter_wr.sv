`ifndef SVC_AXI_AXIL_ADAPTER_WR_SV
`define SVC_AXI_AXIL_ADAPTER_WR_SV

`include "svc.sv"
`include "svc_axi_axil_reflect_wr.sv"
`include "svc_axi_burst_iter_ax.sv"

// AXI to AXI-Lite adapter for writes. Buses must be the same size.

module svc_axi_axil_adapter_wr #(
    parameter AXI_ADDR_WIDTH           = 8,
    parameter AXI_DATA_WIDTH           = 16,
    parameter AXI_STRB_WIDTH           = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH             = 4,
    parameter OUTSTANDING_WRITES_WIDTH = 1
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI subordinate interface
    //
    input  logic                      s_axi_awvalid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [               7:0] s_axi_awlen,
    input  logic [               2:0] s_axi_awsize,
    input  logic [               1:0] s_axi_awburst,
    output logic                      s_axi_awready,
    input  logic                      s_axi_wvalid,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                      s_axi_wlast,
    output logic                      s_axi_wready,
    output logic                      s_axi_bvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [               1:0] s_axi_bresp,
    input  logic                      s_axi_bready,

    //
    // AXI-Lite manager interface
    //
    output logic [AXI_ADDR_WIDTH-1:0] m_axil_awaddr,
    output logic                      m_axil_awvalid,
    input  logic                      m_axil_awready,
    output logic [AXI_DATA_WIDTH-1:0] m_axil_wdata,
    output logic [AXI_STRB_WIDTH-1:0] m_axil_wstrb,
    output logic                      m_axil_wvalid,
    input  logic                      m_axil_wready,
    input  logic [               1:0] m_axil_bresp,
    input  logic                      m_axil_bvalid,
    output logic                      m_axil_bready
);

  logic                      m_axi_awvalid;
  logic [AXI_ADDR_WIDTH-1:0] m_axi_awaddr;
  logic [  AXI_ID_WIDTH-1:0] m_axi_awid;
  logic [               7:0] m_axi_awlen;
  logic [               2:0] m_axi_awsize;
  logic [               1:0] m_axi_awburst;
  logic                      m_axi_awlast;
  logic                      m_axi_awready;

  logic                      m_axi_wvalid;
  logic [AXI_DATA_WIDTH-1:0] m_axi_wdata;
  logic [AXI_STRB_WIDTH-1:0] m_axi_wstrb;
  logic                      m_axi_wlast;
  logic                      m_axi_wready;
  logic                      m_axi_bvalid;
  logic [  AXI_ID_WIDTH-1:0] m_axi_bid;
  logic [               1:0] m_axi_bresp;
  logic                      m_axi_buser;
  logic                      m_axi_bready;

  svc_axi_burst_iter_ax #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_burst_iter_ar_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_valid(s_axi_awvalid),
      .s_addr (s_axi_awaddr),
      .s_id   (s_axi_awid),
      .s_len  (s_axi_awlen),
      .s_size (s_axi_awsize),
      .s_burst(s_axi_awburst),
      .s_ready(s_axi_awready),

      .m_valid(m_axi_awvalid),
      .m_addr (m_axi_awaddr),
      .m_id   (m_axi_awid),
      .m_len  (m_axi_awlen),
      .m_size (m_axi_awsize),
      .m_burst(m_axi_awburst),
      .m_last (m_axi_awlast),
      .m_ready(m_axi_awready)
  );

  // the rest of the signals pass through
  assign m_axi_wvalid = s_axi_wvalid;
  assign m_axi_wdata  = s_axi_wdata;
  assign m_axi_wstrb  = s_axi_wstrb;
  assign m_axi_wlast  = s_axi_wlast;
  assign s_axi_wready = m_axi_wready;

  assign s_axi_bid    = m_axi_bid;
  assign s_axi_bresp  = m_axi_bresp;
  assign m_axi_bready = s_axi_bready;

  svc_axi_axil_reflect_wr #(
      .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH            (AXI_ID_WIDTH),
      .AXI_USER_WIDTH          (1),
      .OUTSTANDING_WRITES_WIDTH(OUTSTANDING_WRITES_WIDTH)
  ) svc_axi_axil_reflect_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_awuser (m_axi_awlast),
      .s_axi_awready(m_axi_awready),
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wlast  (m_axi_wlast),
      .s_axi_wready (m_axi_wready),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bid    (m_axi_bid),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_buser  (m_axi_buser),
      .s_axi_bready (m_axi_bready),

      .m_axil_awaddr (m_axil_awaddr),
      .m_axil_awvalid(m_axil_awvalid),
      .m_axil_awready(m_axil_awready),
      .m_axil_wdata  (m_axil_wdata),
      .m_axil_wstrb  (m_axil_wstrb),
      .m_axil_wvalid (m_axil_wvalid),
      .m_axil_wready (m_axil_wready),
      .m_axil_bresp  (m_axil_bresp),
      .m_axil_bvalid (m_axil_bvalid),
      .m_axil_bready (m_axil_bready)
  );

  assign s_axi_bvalid = m_axi_bvalid && m_axi_buser;

`ifdef FORMAL
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE
`ifdef FORMAL_SVC_AXI_AXIL_ADAPTER_WR
  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  logic [8:0] f_axi_wr_pending;
  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);

    // FIXME: this over constrains the state space as this can actually happen
    // in real usage, but is necessary for faxi_slave.v. See faxi_slave.v:664
    if (f_axi_wr_pending > 0) begin
      assume (!s_axi_awready);
    end
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
      .i_axi_awready(s_axi_awready),
      .i_axi_awid   (s_axi_awid),
      .i_axi_awaddr (s_axi_awaddr),
      .i_axi_awlen  (s_axi_awlen),
      .i_axi_awsize (s_axi_awsize),
      .i_axi_awburst(s_axi_awburst),
      .i_axi_awlock (0),
      .i_axi_awcache(0),
      .i_axi_awprot (0),
      .i_axi_awqos  (0),
      .i_axi_awvalid(s_axi_awvalid),

      // Write data
      .i_axi_wready(s_axi_wready),
      .i_axi_wdata (s_axi_wdata),
      .i_axi_wstrb (s_axi_wstrb),
      .i_axi_wlast (s_axi_wlast),
      .i_axi_wvalid(s_axi_wvalid),

      // Write return response
      .i_axi_bid   (s_axi_bid),
      .i_axi_bresp (s_axi_bresp),
      .i_axi_bvalid(s_axi_bvalid),
      .i_axi_bready(s_axi_bready),

      // Read address
      .i_axi_arready(),
      .i_axi_arid   (),
      .i_axi_araddr (),
      .i_axi_arlen  (),
      .i_axi_arsize (),
      .i_axi_arburst(),
      .i_axi_arlock (0),
      .i_axi_arcache(0),
      .i_axi_arprot (0),
      .i_axi_arqos  (0),
      .i_axi_arvalid(0),

      // Read response
      .i_axi_rid   (),
      .i_axi_rresp (),
      .i_axi_rvalid(0),
      .i_axi_rdata (),
      .i_axi_rlast (),
      .i_axi_rready(),

      .f_axi_awr_nbursts   (),
      .f_axi_wr_pending    (f_axi_wr_pending),
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
      .F_OPT_WRITE_ONLY  (1),
      .F_OPT_INITIAL     (0),
      .F_OPT_ASSUME_RESET(1)
  ) faxil_manager_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      // Write address channel
      .i_axi_awvalid(m_axil_awvalid),
      .i_axi_awready(m_axil_awready),
      .i_axi_awaddr (m_axil_awaddr),
      .i_axi_awprot (0),

      // Write data
      .i_axi_wready(m_axil_wready),
      .i_axi_wdata (m_axil_wdata),
      .i_axi_wstrb (m_axil_wstrb),
      .i_axi_wvalid(m_axil_wvalid),

      // Write response
      .i_axi_bresp (m_axil_bresp),
      .i_axi_bvalid(m_axil_bvalid),
      .i_axi_bready(m_axil_bready),

      // Read address
      .i_axi_arvalid(0),
      .i_axi_arready(),
      .i_axi_araddr (),
      .i_axi_arprot (0),

      // Read data return
      .i_axi_rvalid(0),
      .i_axi_rready(),
      .i_axi_rdata (),
      .i_axi_rresp (),

      // Formal check variables
      .f_axi_rd_outstanding (),
      .f_axi_wr_outstanding (),
      .f_axi_awr_outstanding()
  );
`endif

  // TODO: perf coverage statement like the in the _rd version

`else  // ZIPCPU_PRIVATE
  // verilator lint_off: UNUSEDSIGNAL
  logic f_unused = |{s_axi_awlen, s_axi_awsize, s_axi_awburst};
  // verilator lint_on: UNUSEDSIGNAL
`endif
`endif

endmodule
`endif
