`ifndef SVC_AXI_PERF_TGEN_SV
`define SVC_AXI_PERF_TGEN_SV

`include "svc.sv"
`include "svc_axil_regfile.sv"
`include "svc_unused.sv"

module svc_axi_tgen_csr #(
    parameter AXI_ADDR_WIDTH  = 20,
    parameter AXI_ID_WIDTH    = 4,
    parameter AXIL_ADDR_WIDTH = 32,
    parameter AXIL_DATA_WIDTH = 32,
    parameter AXIL_STRB_WIDTH = AXIL_DATA_WIDTH / 8
) (
    input logic clk,
    input logic rst_n,

    output logic [AXI_ADDR_WIDTH-1:0] base_addr,
    output logic [  AXI_ID_WIDTH-1:0] burst_id,
    output logic [               7:0] burst_beats,
    output logic [AXI_ADDR_WIDTH-1:0] burst_stride,
    output logic [               2:0] burst_axsize,
    output logic [              15:0] burst_num,

    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_awaddr,
    input  logic                       s_axil_awvalid,
    output logic                       s_axil_awready,
    input  logic [AXIL_DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [AXIL_STRB_WIDTH-1:0] s_axil_wstrb,
    input  logic                       s_axil_wvalid,
    output logic                       s_axil_wready,
    output logic                       s_axil_bvalid,
    output logic [                1:0] s_axil_bresp,
    input  logic                       s_axil_bready,

    input  logic                       s_axil_arvalid,
    input  logic [AXIL_ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                       s_axil_arready,
    output logic                       s_axil_rvalid,
    output logic [AXIL_DATA_WIDTH-1:0] s_axil_rdata,
    output logic [                1:0] s_axil_rresp,
    input  logic                       s_axil_rready
);
  localparam A_AW = AXI_ADDR_WIDTH;
  localparam A_IW = AXI_ID_WIDTH;
  localparam DW = AXIL_DATA_WIDTH;

  localparam N = 6;

  typedef enum {
    REG_BASE_ADDR    = 0,
    REG_BURST_ID     = 1,
    REG_BURST_BEATS  = 2,
    REG_BURST_STRIDE = 3,
    REG_BURST_AXSIZE = 4,
    REG_BURST_NUM    = 5
  } reg_id_t;

  localparam [N-1:0] REG_WRITE_MASK = '1;

  logic [N-1:0][AXIL_DATA_WIDTH-1:0] r_val;
  logic [N-1:0][AXIL_DATA_WIDTH-1:0] r_val_next;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      r_val[REG_BASE_ADDR]    <= DW'(0);
      r_val[REG_BURST_ID]     <= DW'(0);
      r_val[REG_BURST_BEATS]  <= DW'(64);
      r_val[REG_BURST_STRIDE] <= DW'(128 * (DW / 8));
      r_val[REG_BURST_AXSIZE] <= DW'(`SVC_MAX_AXSIZE(DW));
      r_val[REG_BURST_NUM]    <= DW'(16);
    end else begin
      r_val <= r_val_next;
    end
  end

  assign base_addr    = A_AW'(r_val[REG_BASE_ADDR]);
  assign burst_id     = A_IW'(r_val[REG_BURST_ID]);
  assign burst_beats  = 8'(r_val[REG_BURST_BEATS]);
  assign burst_stride = A_AW'(r_val[REG_BURST_STRIDE]);
  assign burst_axsize = 3'(r_val[REG_BURST_AXSIZE]);
  assign burst_num    = 16'(r_val[REG_BURST_NUM]);

  svc_axil_regfile #(
      .N              (N),
      .DATA_WIDTH     (AXIL_DATA_WIDTH),
      .AXIL_ADDR_WIDTH(AXIL_ADDR_WIDTH),
      .AXIL_DATA_WIDTH(AXIL_DATA_WIDTH),
      .AXIL_STRB_WIDTH(AXIL_STRB_WIDTH),
      .REG_WRITE_MASK (REG_WRITE_MASK)
  ) regfile (
      .clk  (clk),
      .rst_n(rst_n),

      .r_val     (r_val),
      .r_val_next(r_val_next),

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
      .s_axil_araddr (s_axil_araddr),
      .s_axil_arvalid(s_axil_arvalid),
      .s_axil_arready(s_axil_arready),
      .s_axil_rvalid (s_axil_rvalid),
      .s_axil_rdata  (s_axil_rdata),
      .s_axil_rresp  (s_axil_rresp),
      .s_axil_rready (s_axil_rready)
  );
endmodule
`endif
