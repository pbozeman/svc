`include "svc_unit.sv"

`include "svc_axi_tgen_csr.sv"

// This is not an exhaustive test as the csr is just a wrapper around
// svc_axil_regfile. Let's just make sure the mappings are there and
// it synthesizes.

// verilator lint_off: UNUSEDSIGNAL
module svc_axi_tgen_csr_tb;
  localparam AXI_ADDR_WIDTH = 20;
  localparam AXI_ID_WIDTH = 4;
  localparam AXIL_ADDR_WIDTH = 32;
  localparam AXIL_DATA_WIDTH = 32;
  localparam AXIL_STRB_WIDTH = AXIL_DATA_WIDTH / 8;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr;
  logic                       s_axil_awvalid;
  logic                       s_axil_awready;
  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata;
  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb;
  logic                       s_axil_wvalid;
  logic                       s_axil_wready;
  logic                       s_axil_bvalid;
  logic [                1:0] s_axil_bresp;
  logic                       s_axil_bready;
  logic                       s_axil_arvalid;
  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr;
  logic                       s_axil_arready;
  logic                       s_axil_rvalid;
  logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata;
  logic [                1:0] s_axil_rresp;
  logic                       s_axil_rready;

  logic [ AXI_ADDR_WIDTH-1:0] base_addr;
  logic [   AXI_ID_WIDTH-1:0] burst_id;
  logic [                7:0] burst_beats;
  logic [ AXI_ADDR_WIDTH-1:0] burst_stride;
  logic [                2:0] burst_axsize;
  logic [               15:0] burst_num;

  svc_axi_tgen_csr #(
      .AXI_ADDR_WIDTH (AXI_ADDR_WIDTH),
      .AXI_ID_WIDTH   (AXI_ID_WIDTH),
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
      .AXIL_STRB_WIDTH(AXIL_STRB_WIDTH)
  ) uut (
      .clk           (clk),
      .rst_n         (rst_n),
      .base_addr     (base_addr),
      .burst_id      (burst_id),
      .burst_beats   (burst_beats),
      .burst_stride  (burst_stride),
      .burst_axsize  (burst_axsize),
      .burst_num     (burst_num),
      .s_axil_awaddr (s_axil_awaddr),
      .s_axil_awvalid(s_axil_awvalid),
      .s_axil_awready(s_axil_awready),
      .s_axil_wdata  (s_axil_wdata),
      .s_axil_wstrb  (s_axil_wstrb),
      .s_axil_wvalid (s_axil_wvalid),
      .s_axil_wready (s_axil_wready),
      .s_axil_bvalid (s_axil_bvalid),
      .s_axil_bresp  (s_axil_bresp),
      .s_axil_bready (s_axil_bready),
      .s_axil_arvalid(s_axil_arvalid),
      .s_axil_araddr (s_axil_araddr),
      .s_axil_arready(s_axil_arready),
      .s_axil_rvalid (s_axil_rvalid),
      .s_axil_rdata  (s_axil_rdata),
      .s_axil_rresp  (s_axil_rresp),
      .s_axil_rready (s_axil_rready)
  );

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      s_axil_awaddr  <= '0;
      s_axil_awvalid <= 1'b0;
      s_axil_wdata   <= '0;
      s_axil_wstrb   <= '0;
      s_axil_wvalid  <= 1'b0;
      s_axil_bready  <= 1'b0;
      s_axil_arvalid <= 1'b0;
      s_axil_araddr  <= '0;
      s_axil_rready  <= 1'b0;
    end
  end

  task automatic test_reset();
    `CHECK_EQ(base_addr, 20'h0);
    `CHECK_EQ(burst_id, 4'h0);
    `CHECK_EQ(burst_beats, 8'h40);
    `CHECK_EQ(burst_stride, 20'h200);
    `CHECK_EQ(burst_axsize, 3'h2);
    `CHECK_EQ(burst_num, 16'h10);
  endtask

  `TEST_SUITE_BEGIN(svc_axi_tgen_csr_tb);
  `TEST_CASE(test_reset);
  `TEST_SUITE_END();
endmodule
