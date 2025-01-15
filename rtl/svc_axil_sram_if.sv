`ifndef SVC_AXIL_SRAM_IF_SV
`define SVC_AXIL_SRAM_IF_SV

`include "svc.sv"
`include "svc_skidbuf.sv"
`include "svc_unused.sv"

// This is a wrapper to convert byte based AXI-Lite to an SRAM interface.
// It arbitrates between reads and writes, as the SRAM can only
// do 1 at a time. It also converts the addresses to be word rather than byte
// based. rresp and bresp are always marked as success.
module svc_axil_sram_if #(
    parameter AXIL_ADDR_WIDTH = 8,
    parameter AXIL_DATA_WIDTH = 16,
    parameter AXIL_STRB_WIDTH = (AXIL_DATA_WIDTH / 8),
    parameter LSB             = $clog2(AXIL_DATA_WIDTH) - 3,
    parameter SRAM_ADDR_WIDTH = AXIL_ADDR_WIDTH - LSB,
    parameter SRAM_DATA_WIDTH = AXIL_DATA_WIDTH,
    parameter SRAM_STRB_WIDTH = AXIL_STRB_WIDTH
) (
    input logic clk,
    input logic rst_n,

    //
    // AXI-Lite subordinate interface
    //
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic [                1:0] s_axil_bresp,
    output logic                       s_axil_bvalid,
    input  logic                       s_axil_bready,

    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    output logic                       s_axil_rvalid,
    input  logic                       s_axil_rready,

    //
    // SRAM interface
    //
    output logic                       sram_cmd_valid,
    input  logic                       sram_cmd_ready,
    output logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr,
    output logic                       sram_cmd_wr_en,
    output logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data,
    output logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb,
    input  logic                       sram_resp_rd_valid,
    output logic                       sram_resp_rd_ready,
    input  logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data
);
  localparam SB_W_DATA_WIDTH = SRAM_DATA_WIDTH + SRAM_STRB_WIDTH;

  // ar skidbuf
  logic                       sb_ar_valid;
  logic                       sb_ar_ready;
  logic [SRAM_ADDR_WIDTH-1:0] sb_ar_addr;

  // r skidbuf
  logic                       sb_r_ready;

  //
  // aw skidbuf
  //
  logic                       sb_aw_valid;
  logic                       sb_aw_ready;
  logic [SRAM_ADDR_WIDTH-1:0] sb_aw_addr;

  //
  // w skidbuf
  //
  logic                       sb_w_valid;
  logic                       sb_w_ready;
  logic [SRAM_DATA_WIDTH-1:0] sb_w_data;
  logic [SRAM_STRB_WIDTH-1:0] sb_w_strb;

  //
  //
  // arbiter signals
  //
  logic                       pri_rd;
  logic                       pri_rd_next;

  logic                       rd_ok;
  logic                       rd_start;

  logic                       wr_ok;
  logic                       wr_start;

  // SRAM outputs
  logic                       sram_cmd_valid_next;
  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr_next;
  logic                       sram_cmd_wr_en_next;
  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data_next;
  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb_next;

  //
  // ar channel
  //
  assign s_axil_arready = sb_ar_ready && sb_r_ready;

  svc_skidbuf #(
      .DATA_WIDTH(SRAM_ADDR_WIDTH)
  ) svc_skidbuf_ar_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_arvalid && s_axil_arready),
      .i_data (s_axil_araddr[AXIL_ADDR_WIDTH-1:LSB]),
      .o_ready(sb_ar_ready),

      .i_ready(rd_start),
      .o_data (sb_ar_addr),
      .o_valid(sb_ar_valid)
  );

  //
  // r channel
  //
  assign s_axil_rresp = 2'b00;

  svc_skidbuf #(
      .DATA_WIDTH(SRAM_DATA_WIDTH)
  ) svc_skidbuf_r_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(sram_resp_rd_valid && sram_resp_rd_ready),
      .i_data (sram_resp_rd_data),
      .o_ready(sb_r_ready),

      .i_ready(s_axil_rvalid && s_axil_rready),
      .o_data (s_axil_rdata),
      .o_valid(s_axil_rvalid)
  );

  //
  // aw channel
  //
  assign s_axil_awready = sb_aw_ready;

  svc_skidbuf #(
      .DATA_WIDTH(SRAM_ADDR_WIDTH)
  ) svc_skidbuf_aw_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_awvalid && s_axil_awready),
      .i_data (s_axil_awaddr[AXIL_ADDR_WIDTH-1:LSB]),
      .o_ready(sb_aw_ready),

      .i_ready(wr_start),
      .o_data (sb_aw_addr),
      .o_valid(sb_aw_valid)
  );

  //
  // w channel
  //
  assign s_axil_wready = sb_w_ready && (!s_axil_bvalid || s_axil_bready);

  svc_skidbuf #(
      .DATA_WIDTH(SB_W_DATA_WIDTH)
  ) svc_skidbuf_w_i (
      .clk  (clk),
      .rst_n(rst_n),

      .i_valid(s_axil_wvalid && s_axil_wready),
      .i_data ({s_axil_wstrb, s_axil_wdata}),
      .o_ready(sb_w_ready),

      .i_ready(wr_start),
      .o_data ({sb_w_strb, sb_w_data}),
      .o_valid(sb_w_valid)
  );

  //
  // b channel
  //
  // a max of 2 is equivalent to the skidbufs
  logic [1:0] bcnt;
  logic [1:0] bcnt_next;
  assign s_axil_bresp = 2'b00;

  always_comb begin
    case ({
      (sram_cmd_valid && sram_cmd_ready && sram_cmd_wr_en),
      (s_axil_bvalid && s_axil_bready)
    })
      2'b01: begin
        bcnt_next = bcnt - 1;
      end

      2'b10: begin
        bcnt_next = bcnt + 1;
      end

      2'b00, 2'b11: begin
        bcnt_next = bcnt;
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      bcnt          <= 0;
      s_axil_bvalid <= 1'b0;
    end else begin
      bcnt          <= bcnt_next;
      s_axil_bvalid <= bcnt_next > 0;
    end
  end

  //
  // arbiter
  //
  assign rd_ok = sb_ar_valid && sb_r_ready;
  assign wr_ok = sb_aw_valid && sb_w_valid && bcnt < 2'b10;

  // pull the common rd/wr arb logic out so that rd/wr signals
  // don't have to be duplicated 2x each.
  always_comb begin
    wr_start = 1'b0;
    rd_start = 1'b0;

    if (!sram_cmd_valid || sram_cmd_ready) begin
      if (pri_rd) begin
        if (rd_ok) begin
          rd_start = 1'b1;
        end else if (wr_ok) begin
          wr_start = 1'b1;
        end
      end else begin
        if (wr_ok) begin
          wr_start = 1'b1;
        end else if (rd_ok) begin
          rd_start = 1'b1;
        end
      end
    end
  end

  always_comb begin
    sram_cmd_valid_next   = sram_cmd_valid && !sram_cmd_ready;
    sram_cmd_addr_next    = sram_cmd_addr;
    sram_cmd_wr_en_next   = sram_cmd_wr_en;
    sram_cmd_wr_data_next = sram_cmd_wr_data;
    sram_cmd_wr_strb_next = sram_cmd_wr_strb;
    pri_rd_next           = pri_rd;

    if (!sram_cmd_valid || sram_cmd_ready) begin
      if (rd_start) begin
        sram_cmd_valid_next = 1'b1;
        sram_cmd_addr_next  = sb_ar_addr;
        sram_cmd_wr_en_next = 1'b0;
        pri_rd_next         = 1'b0;
      end else if (wr_start) begin
        sram_cmd_valid_next   = 1'b1;
        sram_cmd_addr_next    = sb_aw_addr;
        sram_cmd_wr_data_next = sb_w_data;
        sram_cmd_wr_strb_next = sb_w_strb;
        sram_cmd_wr_en_next   = 1'b1;
        pri_rd_next           = 1'b1;
      end
    end
  end

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      sram_cmd_valid <= 1'b0;
      pri_rd         <= 1'b0;
    end else begin
      pri_rd           <= pri_rd_next;
      sram_cmd_valid   <= sram_cmd_valid_next;
      sram_cmd_addr    <= sram_cmd_addr_next;
      sram_cmd_wr_en   <= sram_cmd_wr_en_next;
      sram_cmd_wr_data <= sram_cmd_wr_data_next;
      sram_cmd_wr_strb <= sram_cmd_wr_strb_next;
    end
  end

  assign sram_resp_rd_ready = sb_r_ready;

  `SVC_UNUSED({s_axil_awaddr[3:0], s_axil_araddr[3:0]});

`ifdef FORMAL
`ifdef FORMAL_SVC_AXIL_SRAM_IF
  // the number of bits necessary to count the maximum number
  // of items in flight.
  localparam F_LGDEPTH = 4;

  // the svc modules don't init all values pre-reset
  localparam F_OPT_INITIAL = 0;

  // Since the sram can not run read and write at the same time,
  // the stall must be less than the delay, or else a stall on one channel can
  // cause max delay to be hit on the other, which would be the expected
  // behavior. (12 was the default for both, so give a small amount of
  // of breathing room)
  localparam F_AXI_MAXRSTALL = 8;
  localparam F_AXI_MAXDELAY = 12;

  // verilator lint_off: UNUSEDSIGNAL
  // Remove the lint_off when these get used for induction. See the comment at
  // the end of the formal section.
  wire  [F_LGDEPTH-1:0] f_axil_rd_outstanding;
  wire  [F_LGDEPTH-1:0] f_axil_wr_outstanding;
  wire  [F_LGDEPTH-1:0] f_axil_awr_outstanding;
  // verilator lint_on: UNUSEDSIGNAL

  logic                 f_past_valid;

  initial f_past_valid = 0;
  always @(posedge clk) begin
    f_past_valid <= 1;
  end

  always @(*) begin
    // assume reset at the start, and then, we don't reset randomly
    assume (rst_n == f_past_valid);
  end

  // NOTE: this is a protocol check only. We are not checking what IO is going
  // to/from the right place.
  faxil_slave #(
      .C_AXI_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .C_AXI_DATA_WIDTH(AXIL_DATA_WIDTH),
      .F_LGDEPTH       (F_LGDEPTH),
      .F_OPT_INITIAL   (F_OPT_INITIAL),
      .F_AXI_MAXRSTALL (F_AXI_MAXRSTALL),
      .F_AXI_MAXDELAY  (F_AXI_MAXDELAY)
  ) faxil_i (
      .i_clk        (clk),
      .i_axi_reset_n(rst_n),

      .i_axi_awready(s_axil_awready),
      .i_axi_awaddr (s_axil_awaddr),
      .i_axi_awvalid(s_axil_awvalid),
      .i_axi_awprot ('0),

      .i_axi_wready(s_axil_wready),
      .i_axi_wdata (s_axil_wdata),
      .i_axi_wstrb (s_axil_wstrb),
      .i_axi_wvalid(s_axil_wvalid),

      .i_axi_bready(s_axil_bready),
      .i_axi_bvalid(s_axil_bvalid),
      .i_axi_bresp (s_axil_bresp),

      .i_axi_araddr (s_axil_araddr),
      .i_axi_arvalid(s_axil_arvalid),
      .i_axi_arready(s_axil_arready),
      .i_axi_arprot ('0),

      .i_axi_rvalid(s_axil_rvalid),
      .i_axi_rready(s_axil_rready),
      .i_axi_rdata (s_axil_rdata),
      .i_axi_rresp (s_axil_rresp),

      .f_axi_rd_outstanding (f_axil_rd_outstanding),
      .f_axi_wr_outstanding (f_axil_wr_outstanding),
      .f_axi_awr_outstanding(f_axil_awr_outstanding)
  );

`ifndef VERILATOR
  svc_model_sram_if #(
      .SRAM_ADDR_WIDTH(SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH(SRAM_DATA_WIDTH),
      .READ_ONLY_ZERO (1)
  ) svc_model_sram_if_i (
      .clk  (clk),
      .rst_n(rst_n),

      .sram_cmd_valid   (sram_cmd_valid),
      .sram_cmd_ready   (sram_cmd_ready),
      .sram_cmd_addr    (sram_cmd_addr),
      .sram_cmd_wr_en   (sram_cmd_wr_en),
      .sram_cmd_wr_data (sram_cmd_wr_data),
      .sram_cmd_wr_strb (sram_cmd_wr_strb),
      .sram_resp_valid  (sram_resp_rd_valid),
      .sram_resp_ready  (sram_resp_rd_ready),
      .sram_resp_rd_data(sram_resp_rd_data)
  );
`endif

  // ensure we can do 6 io ops in a row, 1 every clock cycle.
  // Why 6? Because the module used to be implemented with fifos with a depth
  // of 4, but now we might as well leave this at 6.
  //
  // ensure we can get 6 write responses in a row, 1 every clock cycle
  always @(posedge clk) begin
    if ((f_past_valid) && (rst_n)) begin
      c_write_per_clk :
      cover ((s_axil_bvalid && s_axil_bready) && ($past(
          (s_axil_bvalid && s_axil_bready), 1
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 2
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 3
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 4
      )) && ($past(
          (s_axil_bvalid && s_axil_bready), 5
      )));
    end
  end

  // ensure we can do 6 read responses in a row, 1 every clock cycle
  always @(posedge clk) begin
    if ((f_past_valid) && (rst_n)) begin
      c_read_per_clk :
      cover ((s_axil_rvalid && s_axil_rready) && ($past(
          (s_axil_rvalid && s_axil_rready), 1
      )) && ($past(
          (s_axil_rvalid && s_axil_rready), 2
      )) && ($past(
          (s_axil_rvalid && s_axil_rready), 3
      )) && ($past(
          (s_axil_rvalid && s_axil_rready), 4
      )) && ($past(
          (s_axil_rvalid && s_axil_rready), 5
      )));
    end
  end

  // Look into properties to use induction and an unbounded check
  //
  // This is going to be a bit of a pain as it is going to require counting
  // all the entries in the fifos.
  //
  // see
  //   https://zipcpu.com/blog/2020/03/08/easyaxil.html
  // and
  //   https://github.com/ZipCPU/wb2axip/blob/master/rtl/demoaxi.v
`else
  // verilator lint_off: UNUSEDSIGNAL
  logic unused = |{s_axil_awaddr[3:0], s_axil_araddr[3:0]};
  // verilator lint_on: UNUSEDSIGNAL
`endif
`endif

endmodule

`endif
