`ifndef SVC_AXI_AXIL_REFLECT_SV
`define SVC_AXI_AXIL_REFLECT_SV

`include "svc.sv"
`include "svc_axi_axil_reflect_rd.sv"
`include "svc_axi_axil_reflect_wr.sv"

//
// Takes an AXI to AXI-Lite write stream with single beat bursts and
// reflects the IDs from the original AW and AR request B/R returns.
//
module svc_axi_axil_reflect #(
    parameter AXI_ADDR_WIDTH       = 2,
    parameter AXI_DATA_WIDTH       = 16,
    parameter AXI_STRB_WIDTH       = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH         = 4,
    parameter AXI_USER_WIDTH       = 1,
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
    input  logic [AXI_USER_WIDTH-1:0] s_axi_awuser,
    output logic                      s_axi_awready,
    input  logic                      s_axi_wvalid,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                      s_axi_wlast,
    output logic                      s_axi_wready,
    output logic                      s_axi_bvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [               1:0] s_axi_bresp,
    output logic [AXI_USER_WIDTH-1:0] s_axi_buser,
    input  logic                      s_axi_bready,

    input  logic                      s_axi_arvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [               7:0] s_axi_arlen,
    input  logic [               2:0] s_axi_arsize,
    input  logic [               1:0] s_axi_arburst,
    input  logic [AXI_USER_WIDTH-1:0] s_axi_aruser,
    output logic                      s_axi_arready,
    output logic                      s_axi_rvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic [AXI_USER_WIDTH-1:0] s_axi_ruser,
    output logic                      s_axi_rlast,
    input  logic                      s_axi_rready,

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
    output logic                      m_axil_bready,

    output logic                      m_axil_arvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axil_araddr,
    input  logic                      m_axil_arready,
    input  logic                      m_axil_rvalid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axil_rdata,
    input  logic [               1:0] m_axil_rresp,
    output logic                      m_axil_rready
);

  svc_axi_axil_reflect_wr #(
      .AXI_ADDR_WIDTH          (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH          (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH            (AXI_ID_WIDTH),
      .AXI_USER_WIDTH          (AXI_USER_WIDTH),
      .OUTSTANDING_WRITES_WIDTH(OUTSTANDING_IO_WIDTH)
  ) svc_axi_axil_reflect_wr_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_awvalid(s_axi_awvalid),
      .s_axi_awaddr (s_axi_awaddr),
      .s_axi_awid   (s_axi_awid),
      .s_axi_awlen  (s_axi_awlen),
      .s_axi_awsize (s_axi_awsize),
      .s_axi_awburst(s_axi_awburst),
      .s_axi_awuser (s_axi_awuser),
      .s_axi_awready(s_axi_awready),
      .s_axi_wvalid (s_axi_wvalid),
      .s_axi_wdata  (s_axi_wdata),
      .s_axi_wstrb  (s_axi_wstrb),
      .s_axi_wlast  (s_axi_wlast),
      .s_axi_wready (s_axi_wready),
      .s_axi_bvalid (s_axi_bvalid),
      .s_axi_bid    (s_axi_bid),
      .s_axi_bresp  (s_axi_bresp),
      .s_axi_buser  (s_axi_buser),
      .s_axi_bready (s_axi_bready),

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

  svc_axi_axil_reflect_rd #(
      .AXI_ADDR_WIDTH         (AXI_ADDR_WIDTH),
      .AXI_DATA_WIDTH         (AXI_DATA_WIDTH),
      .AXI_ID_WIDTH           (AXI_ID_WIDTH),
      .AXI_USER_WIDTH         (AXI_USER_WIDTH),
      .OUTSTANDING_READS_WIDTH(OUTSTANDING_IO_WIDTH)
  ) svc_axi_axil_reflect_rd_i (
      .clk  (clk),
      .rst_n(rst_n),

      .s_axi_arvalid(s_axi_arvalid),
      .s_axi_arid   (s_axi_arid),
      .s_axi_araddr (s_axi_araddr),
      .s_axi_arlen  (s_axi_arlen),
      .s_axi_arsize (s_axi_arsize),
      .s_axi_arburst(s_axi_arburst),
      .s_axi_aruser (s_axi_aruser),
      .s_axi_arready(s_axi_arready),
      .s_axi_rvalid (s_axi_rvalid),
      .s_axi_rid    (s_axi_rid),
      .s_axi_rdata  (s_axi_rdata),
      .s_axi_rresp  (s_axi_rresp),
      .s_axi_ruser  (s_axi_ruser),
      .s_axi_rlast  (s_axi_rlast),
      .s_axi_rready (s_axi_rready),

      .m_axil_arvalid(m_axil_arvalid),
      .m_axil_araddr (m_axil_araddr),
      .m_axil_arready(m_axil_arready),
      .m_axil_rvalid (m_axil_rvalid),
      .m_axil_rdata  (m_axil_rdata),
      .m_axil_rresp  (m_axil_rresp),
      .m_axil_rready (m_axil_rready)
  );

`ifdef FORMAL
  //
  // zipcpu faxi verification
  //
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE

`ifdef FORMAL_SVC_AXI_AXIL_REFLECT
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  localparam logic [2:0] F_MAX_AXSIZE = 3'($clog2(AXI_DATA_WIDTH) - 3);

  logic f_past_valid = 1'b0;
  always @(posedge clk) begin
    f_past_valid <= 1'b1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  //
  // assumptions
  //
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      `ASSUME(am_wr_one_beat, s_axi_awlen == 0);
      `ASSUME(am_wr_max_size, s_axi_awsize <= F_MAX_AXSIZE);
      `ASSUME(am_wr_burst_in_place, s_axi_awburst == 0);

      `ASSUME(am_rd_one_beat, s_axi_arlen == 0);
      `ASSUME(am_rd_max_size, s_axi_arsize <= F_MAX_AXSIZE);
      `ASSUME(am_rd_burst_in_place, s_axi_arburst == 0);
    end
  end

  //
  // basic assertions
  //
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
    end
  end

`ifdef FORMAL_SVC_AXI_AXIL_REFLECT
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

  // TODO: perf coverage statements
`endif

`endif
`endif

endmodule
`endif
