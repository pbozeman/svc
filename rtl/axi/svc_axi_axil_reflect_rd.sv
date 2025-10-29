`ifndef SVC_AXI_AXIL_REFLECT_RD_SV
`define SVC_AXI_AXIL_REFLECT_RD_SV

`include "svc.sv"
`include "svc_sync_fifo_n.sv"
`include "svc_sync_fifo_n1.sv"
`include "svc_unused.sv"

// Takes an AXI to AXI-Lite read stream with single beat bursts and
// reflects the IDs from the original AR request to the R returns.
module svc_axi_axil_reflect_rd #(
    parameter AXI_ADDR_WIDTH          = 8,
    parameter AXI_DATA_WIDTH          = 16,
    parameter AXI_ID_WIDTH            = 4,
    parameter AXI_USER_WIDTH          = 1,
    parameter OUTSTANDING_READS_WIDTH = 1
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
    output logic                      m_axil_arvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axil_araddr,
    input  logic                      m_axil_arready,
    input  logic                      m_axil_rvalid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axil_rdata,
    input  logic [               1:0] m_axil_rresp,
    output logic                      m_axil_rready
);
  logic ar_valid;
  logic ar_ready;

  logic id_ready;
  logic id_valid;

  svc_sync_fifo_n1 #(
      .DATA_WIDTH(AXI_ADDR_WIDTH)
  ) svc_sync_fifo_n1_ar_i (
      .clk  (clk),
      .rst_n(rst_n),

      .w_inc   (s_axi_arvalid && s_axi_arready),
      .w_data  (s_axi_araddr),
      .w_full_n(ar_ready),

      .r_inc    (m_axil_arvalid && m_axil_arready),
      .r_data   (m_axil_araddr),
      .r_empty_n(ar_valid)
  );

  svc_sync_fifo_n #(
      .ADDR_WIDTH(OUTSTANDING_READS_WIDTH),
      .DATA_WIDTH(AXI_ID_WIDTH + AXI_USER_WIDTH)
  ) svc_sync_fifo_n_id_i (
      .clk  (clk),
      .rst_n(rst_n),

      .w_inc    (s_axi_arvalid && s_axi_arready),
      .w_data   ({s_axi_arid, s_axi_aruser}),
      .w_full_n (id_ready),
      .r_inc    (s_axi_rvalid && s_axi_rready),
      .r_data   ({s_axi_rid, s_axi_ruser}),
      .r_empty_n(id_valid)
  );

  // this is cheating a bit. This is supposed to be a non-combinatorial signal
  // per the axi spec, but, both of these signals are registered, so
  // this is a minor transgression and vastly simplifies the logic.
  assign s_axi_arready  = ar_ready && id_ready;

  assign m_axil_arvalid = ar_valid;

  assign s_axi_rvalid   = m_axil_rvalid;
  assign s_axi_rdata    = m_axil_rdata;
  assign s_axi_rresp    = m_axil_rresp;
  assign s_axi_rlast    = 1'b1;

  assign m_axil_rready  = s_axi_rready;

  `SVC_UNUSED({s_axi_arlen, s_axi_arsize, s_axi_arburst, id_valid});

`ifdef FORMAL
  //
  // zipcpu faxi verification
  //
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE

`ifdef FORMAL_SVC_AXI_AXIL_REFLECT_RD
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif
  localparam logic [2:0] F_MAX_ARSIZE = 3'($clog2(AXI_DATA_WIDTH) - 3);

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
      if (s_axi_arvalid) begin
        `ASSUME(am_one_beat, s_axi_arlen == 0);
        `ASSUME(am_max_size, s_axi_arsize <= F_MAX_ARSIZE);
        `ASSUME(am_burst_in_place, s_axi_arburst == 0);
      end
    end
  end

  //
  // basic assertions
  //
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (s_axi_arvalid && s_axi_arready) begin
        assert (id_ready);
      end

      if (m_axil_rvalid) begin
        assert (id_valid);
      end
    end
  end

`ifdef FORMAL_SVC_AXI_AXIL_REFLECT_RD
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
`endif
`endif
`endif

endmodule
`endif
