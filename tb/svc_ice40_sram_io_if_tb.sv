`include "svc_unit.sv"

`include "svc_ice40_sram_io_if.sv"
`include "svc_model_sram.sv"

// verilator lint_off: UNUSEDSIGNAL
module svc_ice40_sram_io_if_tb;
  localparam SRAM_ADDR_WIDTH = 16;
  localparam SRAM_DATA_WIDTH = 8;
  localparam SRAM_STRB_WIDTH = (SRAM_DATA_WIDTH / 8);

  logic                       sram_cmd_valid;
  logic                       sram_cmd_ready;
  logic [SRAM_ADDR_WIDTH-1:0] sram_cmd_addr;
  logic                       sram_cmd_wr_en;
  logic [SRAM_DATA_WIDTH-1:0] sram_cmd_wr_data;
  logic [SRAM_STRB_WIDTH-1:0] sram_cmd_wr_strb;
  logic                       sram_resp_rd_valid;
  logic                       sram_resp_rd_ready;
  logic [SRAM_DATA_WIDTH-1:0] sram_resp_rd_data;

  logic [SRAM_ADDR_WIDTH-1:0] sram_io_addr;
  wire  [SRAM_DATA_WIDTH-1:0] sram_io_data;
  logic                       sram_io_we_n;
  logic                       sram_io_oe_n;
  logic                       sram_io_ce_n;

  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  svc_ice40_sram_io_if #(
      .SRAM_ADDR_WIDTH(SRAM_ADDR_WIDTH),
      .SRAM_DATA_WIDTH(SRAM_DATA_WIDTH)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .sram_cmd_valid    (sram_cmd_valid),
      .sram_cmd_ready    (sram_cmd_ready),
      .sram_cmd_addr     (sram_cmd_addr),
      .sram_cmd_wr_en    (sram_cmd_wr_en),
      .sram_cmd_wr_data  (sram_cmd_wr_data),
      .sram_cmd_wr_strb  (sram_cmd_wr_strb),
      .sram_resp_rd_valid(sram_resp_rd_valid),
      .sram_resp_rd_ready(sram_resp_rd_ready),
      .sram_resp_rd_data (sram_resp_rd_data),

      .sram_io_addr(sram_io_addr),
      .sram_io_data(sram_io_data),
      .sram_io_we_n(sram_io_we_n),
      .sram_io_oe_n(sram_io_oe_n),
      .sram_io_ce_n(sram_io_ce_n)
  );

  svc_model_sram #(
      .ADDR_WIDTH               (SRAM_ADDR_WIDTH),
      .DATA_WIDTH               (SRAM_DATA_WIDTH),
      .UNINITIALIZED_READS_FATAL(0)
  ) svc_model_sram_i (
      .rst_n  (rst_n),
      .we_n   (sram_io_we_n),
      .oe_n   (sram_io_oe_n),
      .ce_n   (sram_io_ce_n),
      .addr   (sram_io_addr),
      .data_io(sram_io_data)
  );

  logic auto_valid = 1'b1;

  always_ff @(posedge clk) begin
    if (~rst_n) begin
      sram_cmd_valid     <= 1'b0;
      sram_resp_rd_ready <= 1'b1;
      auto_valid         <= 1'b1;
    end else begin
      if (auto_valid) begin
        if (sram_cmd_valid && sram_cmd_ready) begin
          sram_cmd_valid <= 1'b0;
        end
      end
    end
  end

  task automatic test_initial;
    `CHECK_FALSE(sram_io_ce_n);
    `CHECK_TRUE(sram_io_oe_n);
    `CHECK_TRUE(sram_io_we_n);
  endtask

  task automatic test_io;
    sram_cmd_addr    = 16'hA000;
    sram_cmd_valid   = 1'b1;
    sram_cmd_wr_en   = 1'b1;
    sram_cmd_wr_data = 8'hD0;
    sram_cmd_wr_strb = 1'b1;
    `CHECK_TRUE(sram_cmd_valid && sram_cmd_ready);

    `TICK(clk);
    `CHECK_FALSE(sram_cmd_valid);
    sram_cmd_valid = 1'b1;
    sram_cmd_wr_en = 1'b0;
    `CHECK_FALSE(sram_resp_rd_valid);

    `TICK(clk);
    `CHECK_WAIT_FOR(clk, sram_resp_rd_valid);
    `CHECK_EQ(sram_resp_rd_data, 8'hD0);
  endtask

  task automatic test_io_sustained_write;
    time         time_start;
    logic [15:0] base_addr = 16'hA000;

    auto_valid = 1'b0;

    time_start = $time;
    for (int i = 0; i < 16; i++) begin
      sram_cmd_addr    = base_addr + SRAM_ADDR_WIDTH'(i);
      sram_cmd_valid   = 1'b1;
      sram_cmd_wr_en   = 1'b1;
      sram_cmd_wr_data = 8'hD0;
      sram_cmd_wr_strb = 1'b1;

      `CHECK_WAIT_FOR(clk, sram_cmd_valid && sram_cmd_ready);
      `TICK(clk);
    end

    // we should do an IO every 2 clocks
    `CHECK_LTE($time - time_start, 16 * 20);
  endtask

  task automatic test_io_sustained_read;
    time         time_start;
    logic [15:0] base_addr = 16'hC000;
    logic [ 7:0] expected_data = SRAM_DATA_WIDTH'(base_addr);

    auto_valid = 1'b0;

    time_start = $time;
    for (int i = 0; i < 16; i++) begin
      sram_cmd_addr  = base_addr + SRAM_ADDR_WIDTH'(i);
      sram_cmd_valid = 1'b1;
      sram_cmd_wr_en = 1'b0;

      `CHECK_WAIT_FOR(clk, sram_cmd_valid && sram_cmd_ready);
      if (sram_resp_rd_valid) begin
        `CHECK_EQ(expected_data, sram_resp_rd_data);
        expected_data = expected_data + 1;
      end
      `TICK(clk);
    end

    // we should do an IO every 2 clocks
    `CHECK_LTE($time - time_start, 16 * 20);
  endtask

  `TEST_SUITE_BEGIN(svc_ice40_sram_io_if_tb);
  `TEST_CASE(test_initial);
  `TEST_CASE(test_io);
  `TEST_CASE(test_io_sustained_write);
  `TEST_CASE(test_io_sustained_read);
  `TEST_SUITE_END();

endmodule
