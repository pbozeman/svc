`ifndef SVC_AXI_BURST_ADAPTER_SV
`define SVC_AXI_BURST_ADAPTER_SV

`include "svc.sv"
`include "svc_axi_burst_adapter_rd.sv"
`include "svc_axi_burst_adapter_wr.sv"

// AXI to AXI burst adapter where n beat bursts are split into 1 beat bursts.
//
// This is useful as an adapter step prior to feeding a bursting master into
// an arbiter, preventing starvation of others masters while the burst is
// onging.

module svc_axi_burst_adapter #(
    parameter AXI_ADDR_WIDTH       = 8,
    parameter AXI_DATA_WIDTH       = 16,
    parameter AXI_STRB_WIDTH       = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH         = 4,
    parameter OUTSTANDING_IO_WIDTH = 1
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
    // AXI manager interface
    //
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
    output logic                      m_axi_bready,

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
  svc_axi_burst_adapter_wr #(
      .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
      .AXI_STRB_WIDTH          (AXI_STRB_WIDTH),
      .AXI_ID_WIDTH            (AXI_ID_WIDTH),
      .OUTSTANDING_WRITES_WIDTH(OUTSTANDING_IO_WIDTH)
  ) svc_axi_burst_adapter_wr_i (
      .clk          (clk),
      .rst_n        (rst_n),
      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awready(s_axi_awready),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wready (s_axi_wready),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bid    (s_axi_bid),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_bready (s_axi_bready),
      .m_axi_awvalid(m_axi_awvalid),
      .m_axi_awaddr (m_axi_awaddr),
      .m_axi_awid   (m_axi_awid),
      .m_axi_awlen  (m_axi_awlen),
      .m_axi_awsize (m_axi_awsize),
      .m_axi_awburst(m_axi_awburst),
      .m_axi_awready(m_axi_awready),
      .m_axi_wvalid (m_axi_wvalid),
      .m_axi_wdata  (m_axi_wdata),
      .m_axi_wstrb  (m_axi_wstrb),
      .m_axi_wlast  (m_axi_wlast),
      .m_axi_wready (m_axi_wready),
      .m_axi_bvalid (m_axi_bvalid),
      .m_axi_bid    (m_axi_bid),
      .m_axi_bresp  (m_axi_bresp),
      .m_axi_bready (m_axi_bready)
  );

  svc_axi_burst_adapter_rd #(
      .AXI_ADDR_WIDTH         (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH         (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH           (AXI_ID_WIDTH),
      .OUTSTANDING_READS_WIDTH(OUTSTANDING_IO_WIDTH)
  ) svc_axi_burst_adapter_rd_i (
      .clk          (clk),
      .rst_n        (rst_n),
      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arid   (s_axi_arid),
      .s_axi_araddr (s_axi_araddr),
      .s_axi_arlen  (s_axi_arlen),
      .s_axi_arsize (s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_arready(s_axi_arready),
      .s_axi_rvalid (s_axi_rvalid),
      .s_axi_rid    (s_axi_rid),
      .s_axi_rdata  (s_axi_rdata),
      .s_axi_rresp  (s_axi_rresp),
      .s_axi_rlast  (s_axi_rlast),
      .s_axi_rready (s_axi_rready),
      .m_axi_arvalid(m_axi_arvalid),
      .m_axi_arid   (m_axi_arid),
      .m_axi_araddr (m_axi_araddr),
      .m_axi_arlen  (m_axi_arlen),
      .m_axi_arsize (m_axi_arsize),
      .m_axi_arburst(m_axi_arburst),
      .m_axi_arready(m_axi_arready),
      .m_axi_rvalid (m_axi_rvalid),
      .m_axi_rid    (m_axi_rid),
      .m_axi_rdata  (m_axi_rdata),
      .m_axi_rresp  (m_axi_rresp),
      .m_axi_rlast  (m_axi_rlast),
      .m_axi_rready (m_axi_rready)
  );

`ifdef FORMAL
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
  //
`ifdef ZIPCPU_PRIVATE
`ifdef FORMAL_SVC_AXI_BURST_ADAPTER
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  logic [8:0] f_axi_wr_pending;

  always @(*) begin
    // FIXME: this over constrains the state space as this can actually happen
    // in real usage, but is necessary for faxi_slave.v. See faxi_slave.v:664
    if (f_axi_wr_pending > 0) begin
      assume (!s_axi_awready);
    end
  end

  //
  // assumptions
  //
  always_ff @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
    end
  end

  // TODO: add some coverage checks, including:
  // * latency
  // * throughput

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

  // For formal verification we just back the module with a axi_memory.
  // It would be nice to use zipcpu's formal faxi_m, but it imposes too many
  // restrictions on what a manager is allowed to do, i.e. AW can't be
  // pipelined during an active write burst, AW must come before W, and if
  // they come in the same cycle, the write len must be 0. All of
  // that is just to restrictive and not representative of how the svc modules
  // work. assume'ing them into compliance would be formally verifying
  // something very different than what actually happens during synthesis.
`ifndef VERILATOR
  svc_axi_mem #(
      .AXI_ADDR_WIDTH(AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH(AXI_DATA_WIDTH),
      .AXI_ID_WIDTH  (AXI_ID_WIDTH)
  ) svc_axi_mem_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(m_axi_awvalid),
      .s_axi_awid   (m_axi_awid),
      .s_axi_awaddr (m_axi_awaddr),
      .s_axi_awlen  (m_axi_awlen),
      .s_axi_awsize (m_axi_awsize),
      .s_axi_awburst(m_axi_awburst),
      .s_axi_awready(m_axi_awready),
      .s_axi_wvalid (m_axi_wvalid),
      .s_axi_wdata  (m_axi_wdata),
      .s_axi_wstrb  (m_axi_wstrb),
      .s_axi_wlast  (m_axi_wlast),
      .s_axi_wready (m_axi_wready),
      .s_axi_bvalid (m_axi_bvalid),
      .s_axi_bid    (m_axi_bid),
      .s_axi_bresp  (m_axi_bresp),
      .s_axi_bready (m_axi_bready),

      .s_axi_arvalid(m_axi_arvalid),
      .s_axi_arid   (m_axi_arid),
      .s_axi_araddr (m_axi_araddr),
      .s_axi_arlen  (m_axi_arlen),
      .s_axi_arsize (m_axi_arsize),
      .s_axi_arburst(m_axi_arburst),
      .s_axi_arready(m_axi_arready),
      .s_axi_rvalid (m_axi_rvalid),
      .s_axi_rid    (m_axi_rid),
      .s_axi_rdata  (m_axi_rdata),
      .s_axi_rresp  (m_axi_rresp),
      .s_axi_rlast  (m_axi_rlast),
      .s_axi_rready (m_axi_rready)
  );
`endif

  // TODO: coverage statement for throughput
`endif
`endif

endmodule
`endif
