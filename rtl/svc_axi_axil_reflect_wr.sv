`ifndef SVC_AXI_AXIL_REFLECT_WR_SV
`define SVC_AXI_AXIL_REFLECT_WR_SV

`include "svc.sv"
`include "svc_skidbuf.sv"
`include "svc_sync_fifo_zl.sv"
`include "svc_unused.sv"

// Takes an AXI to AXI-Lite write stream with single beat bursts and
// reflects the IDs from the original AW request to the B returns.
//
module svc_axi_axil_reflect_wr #(
    parameter AXI_ADDR_WIDTH           = 8,
    parameter AXI_DATA_WIDTH           = 16,
    parameter AXI_STRB_WIDTH           = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH             = 4,
    parameter AXI_USER_WIDTH           = 1,
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
  logic sb_aw_valid;
  logic sb_aw_ready;

  logic sb_w_valid;
  logic sb_w_ready;

  logic id_valid;
  logic id_ready;

  svc_skidbuf #(
      .DATA_WIDTH(AXI_ADDR_WIDTH)
  ) svc_skidbuf_aw_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axi_awvalid && s_axi_awready),
      .i_data (s_axi_awaddr),
      .o_ready(sb_aw_ready),

      .i_ready(m_axil_awvalid && m_axil_awready),
      .o_data (m_axil_awaddr),
      .o_valid(sb_aw_valid)
  );

  svc_skidbuf #(
      .DATA_WIDTH(AXI_DATA_WIDTH + AXI_STRB_WIDTH)
  ) svc_skidbuf_w_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axi_wvalid && s_axi_wready),
      .i_data ({s_axi_wstrb, s_axi_wdata}),
      .o_ready(sb_w_ready),

      .i_ready(m_axil_wvalid && m_axil_wready),
      .o_data ({m_axil_wstrb, m_axil_wdata}),
      .o_valid(sb_w_valid)
  );

  svc_sync_fifo_zl #(
      .ADDR_WIDTH(OUTSTANDING_WRITES_WIDTH),
      .DATA_WIDTH(AXI_ID_WIDTH + AXI_USER_WIDTH)
  ) svc_sync_fifo_zl_id_i (
      .clk  (clk),
      .rst_n(rst_n),

      .w_inc    (s_axi_awvalid && s_axi_awready),
      .w_data   ({s_axi_awid, s_axi_awuser}),
      .w_full_n (id_ready),
      .r_inc    (s_axi_bvalid && s_axi_bready),
      .r_data   ({s_axi_bid, s_axi_buser}),
      .r_empty_n(id_valid)
  );

  assign s_axi_awready  = sb_aw_ready && id_ready;
  assign s_axi_wready   = sb_w_ready && id_ready;

  assign m_axil_awvalid = sb_aw_valid;
  assign m_axil_wvalid  = sb_w_valid;

  assign s_axi_bvalid   = m_axil_bvalid;
  assign s_axi_bresp    = m_axil_bresp;
  assign m_axil_bready  = s_axi_bready;

  // verilog_format: off
  `SVC_UNUSED({s_axi_awlen, s_axi_awsize, s_axi_awburst, s_axi_wlast,
               id_valid});
  // verilog_format: on

`ifdef FORMAL
  //
  // zipcpu faxi verification
  //
  // This uses faxi_* files in tb/formal/private.
  // See tb/formal/private/README.md
`ifdef ZIPCPU_PRIVATE

`ifdef FORMAL_SVC_AXI_AXIL_REFLECT_WR
  `define ASSERT(lable, a) lable: assert(a)
  `define ASSUME(lable, a) lable: assume(a)
  `define COVER(lable, a) lable: cover(a)
`else
  `define ASSERT(lable, a) lable: assume(a)
  `define ASSUME(lable, a) lable: assert(a)
  `define COVER(lable, a)
`endif

  localparam logic [2:0] F_MAX_AWSIZE = 3'($clog2(AXI_DATA_WIDTH) - 3);

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
      if (s_axi_awvalid) begin
        `ASSUME(am_one_beat, s_axi_awlen == 0);
        `ASSUME(am_max_size, s_axi_awsize <= F_MAX_AWSIZE);
        `ASSUME(am_burst_in_place, s_axi_awburst == 0);
      end
    end
  end

  //
  // basic assertions
  //
  always @(posedge clk) begin
    if (f_past_valid && $past(rst_n) && rst_n) begin
      if (m_axil_bvalid) begin
        `ASSERT(as_id_valid, id_valid);
      end
    end
  end

`ifdef FORMAL_SVC_AXI_AXIL_REFLECT_WR
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
`endif
`endif

endmodule
`endif
