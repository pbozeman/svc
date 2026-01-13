`include "svc_unit.sv"
`include "svc_unused.sv"

`include "svc_rv_dbg_bridge.sv"

module svc_rv_dbg_bridge_tbi;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // UART interface
  logic        urx_valid;
  logic [ 7:0] urx_data;
  logic        urx_ready;

  logic        utx_valid;
  logic [ 7:0] utx_data;
  logic        utx_ready;

  // Control outputs
  logic        dbg_stall;
  logic        dbg_rst_n;

  // IMEM write interface
  logic        dbg_imem_wen;
  logic [11:0] dbg_imem_waddr;
  logic [31:0] dbg_imem_wdata;
  logic [ 3:0] dbg_imem_wstrb;

  // DMEM write interface
  logic        dbg_dmem_wen;
  logic [11:0] dbg_dmem_waddr;
  logic [31:0] dbg_dmem_wdata;
  logic [ 3:0] dbg_dmem_wstrb;

  // DMEM read interface
  logic        dbg_dmem_ren;
  logic [11:0] dbg_dmem_raddr;
  logic [31:0] dbg_dmem_rdata;
  logic        dbg_dmem_rdata_valid;

  // Protocol constants
  localparam logic [7:0] CMD_MAGIC = 8'hDB;
  localparam logic [7:0] RESP_MAGIC = 8'hBD;
  localparam logic [7:0] OP_READ_CTRL = 8'h00;
  localparam logic [7:0] OP_WRITE_CTRL = 8'h01;
  localparam logic [7:0] OP_WRITE_MEM = 8'h02;
  localparam logic [7:0] OP_WRITE_BURST = 8'h03;

  svc_rv_dbg_bridge #(
      .IMEM_ADDR_WIDTH(12),
      .DMEM_ADDR_WIDTH(12),
      .IMEM_BASE_ADDR (32'h0000_0000),
      .DMEM_BASE_ADDR (32'h0001_0000)
  ) uut (
      .clk  (clk),
      .rst_n(rst_n),

      .urx_valid(urx_valid),
      .urx_data (urx_data),
      .urx_ready(urx_ready),

      .utx_valid(utx_valid),
      .utx_data (utx_data),
      .utx_ready(utx_ready),

      .dbg_stall(dbg_stall),
      .dbg_rst_n(dbg_rst_n),

      .dbg_imem_wen  (dbg_imem_wen),
      .dbg_imem_waddr(dbg_imem_waddr),
      .dbg_imem_wdata(dbg_imem_wdata),
      .dbg_imem_wstrb(dbg_imem_wstrb),

      .dbg_dmem_wen  (dbg_dmem_wen),
      .dbg_dmem_waddr(dbg_dmem_waddr),
      .dbg_dmem_wdata(dbg_dmem_wdata),
      .dbg_dmem_wstrb(dbg_dmem_wstrb),
      .dbg_dmem_busy (1'b0),

      .dbg_dmem_ren        (dbg_dmem_ren),
      .dbg_dmem_raddr      (dbg_dmem_raddr),
      .dbg_dmem_rdata      (dbg_dmem_rdata),
      .dbg_dmem_rdata_valid(dbg_dmem_rdata_valid)
  );

  // Initialize signals in reset
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      urx_valid            <= 1'b0;
      urx_data             <= 8'h00;
      utx_ready            <= 1'b0;
      dbg_dmem_rdata       <= 32'h0;
      dbg_dmem_rdata_valid <= 1'b0;
    end
  end

  // Send a byte via UART RX
  task automatic send_byte(input logic [7:0] data);
    while (!urx_ready) `TICK(clk);
    urx_valid = 1'b1;
    urx_data  = data;
    `TICK(clk);
    urx_valid = 1'b0;
    `TICK(clk);
  endtask

  // Receive a byte via UART TX
  // Sample at negedge to avoid race conditions with posedge register updates
  task automatic recv_byte(output logic [7:0] data);
    int timeout;
    timeout   = 0;
    utx_ready = 1'b1;
    // Wait for valid at negedge (stable mid-cycle)
    @(negedge clk);
    while (!utx_valid && timeout < 1000) begin
      @(negedge clk);
      timeout++;
    end
    // Capture data at negedge
    data = utx_data;
    // Wait for posedge to let bridge advance to next byte
    `TICK(clk);
  endtask

  //
  // Test: Initial state - stalled and in reset
  //
  task automatic test_initial_state;
    `CHECK_EQ(dbg_stall, 1'b1);
    `CHECK_EQ(dbg_rst_n, 1'b0);
  endtask

  //
  // Test: Read control register
  //
  task automatic test_read_ctrl;
    logic [7:0] magic, status, ctrl;

    // Send read control command
    send_byte(CMD_MAGIC);
    send_byte(OP_READ_CTRL);

    // Get response
    recv_byte(magic);
    `CHECK_EQ(magic, RESP_MAGIC);

    recv_byte(status);
    `CHECK_EQ(status, 8'h00);

    recv_byte(ctrl);
    // bit 0 = stall (1), bit 1 = reset (1)
    `CHECK_EQ(ctrl, 8'h03);
  endtask

  //
  // Test: Write control - release reset
  //
  task automatic test_write_ctrl_release_reset;
    logic [7:0] magic, status;

    // Send write control: stall=1, reset=0
    send_byte(CMD_MAGIC);
    send_byte(OP_WRITE_CTRL);
    send_byte(8'h01);

    // Get response
    recv_byte(magic);
    `CHECK_EQ(magic, RESP_MAGIC);

    recv_byte(status);
    `CHECK_EQ(status, 8'h00);

    `CHECK_EQ(dbg_stall, 1'b1);
    `CHECK_EQ(dbg_rst_n, 1'b1);
  endtask

  //
  // Test: Write control - release stall
  //
  task automatic test_write_ctrl_release_stall;
    logic [7:0] magic, status;

    // First release reset
    send_byte(CMD_MAGIC);
    send_byte(OP_WRITE_CTRL);
    send_byte(8'h01);
    recv_byte(magic);
    `CHECK_EQ(magic, RESP_MAGIC);
    recv_byte(status);
    `CHECK_EQ(status, 8'h00);

    // Then release stall
    send_byte(CMD_MAGIC);
    send_byte(OP_WRITE_CTRL);
    send_byte(8'h00);
    recv_byte(magic);
    `CHECK_EQ(magic, RESP_MAGIC);
    recv_byte(status);
    `CHECK_EQ(status, 8'h00);

    `CHECK_EQ(dbg_stall, 1'b0);
    `CHECK_EQ(dbg_rst_n, 1'b1);
  endtask

  //
  // Test: Write memory to IMEM
  //
  task automatic test_write_mem_imem;
    logic [7:0] magic, status;

    // Address 0x00000004 (IMEM), data 0xDEADBEEF
    send_byte(CMD_MAGIC);
    send_byte(OP_WRITE_MEM);
    send_byte(8'h04);  // addr[7:0]
    send_byte(8'h00);  // addr[15:8]
    send_byte(8'h00);  // addr[23:16]
    send_byte(8'h00);  // addr[31:24]
    send_byte(8'hEF);  // data[7:0]
    send_byte(8'hBE);  // data[15:8]
    send_byte(8'hAD);  // data[23:16]
    send_byte(8'hDE);  // data[31:24]

    recv_byte(magic);
    `CHECK_EQ(magic, RESP_MAGIC);

    recv_byte(status);
    `CHECK_EQ(status, 8'h00);

    // Verify IMEM write signals were asserted
    `CHECK_EQ(dbg_imem_wdata, 32'hDEADBEEF);
  endtask

  //
  // Test: Write memory to DMEM
  //
  task automatic test_write_mem_dmem;
    logic [7:0] magic, status;

    // Address 0x00010008 (DMEM), data 0xCAFEBABE
    send_byte(CMD_MAGIC);
    send_byte(OP_WRITE_MEM);
    send_byte(8'h08);  // addr[7:0]
    send_byte(8'h00);  // addr[15:8]
    send_byte(8'h01);  // addr[23:16]
    send_byte(8'h00);  // addr[31:24]
    send_byte(8'hBE);  // data[7:0]
    send_byte(8'hBA);  // data[15:8]
    send_byte(8'hFE);  // data[23:16]
    send_byte(8'hCA);  // data[31:24]

    recv_byte(magic);
    `CHECK_EQ(magic, RESP_MAGIC);

    recv_byte(status);
    `CHECK_EQ(status, 8'h00);

    // Verify DMEM write signals were asserted
    `CHECK_EQ(dbg_dmem_wdata, 32'hCAFEBABE);
  endtask

  //
  // Test: Burst write to IMEM (streamed, no per-word ACK)
  //
  task automatic test_write_burst_imem;
    logic [7:0] magic, status;

    // Address 0x00000000 (IMEM), 3 words
    send_byte(CMD_MAGIC);
    send_byte(OP_WRITE_BURST);
    send_byte(8'h00);  // addr[7:0]
    send_byte(8'h00);  // addr[15:8]
    send_byte(8'h00);  // addr[23:16]
    send_byte(8'h00);  // addr[31:24]
    send_byte(8'h03);  // count low
    send_byte(8'h00);  // count high

    // Stream all words back-to-back (no ACKs)
    // Word 0: 0x11111111
    send_byte(8'h11);
    send_byte(8'h11);
    send_byte(8'h11);
    send_byte(8'h11);

    // Word 1: 0x22222222
    send_byte(8'h22);
    send_byte(8'h22);
    send_byte(8'h22);
    send_byte(8'h22);

    // Word 2: 0x33333333
    send_byte(8'h33);
    send_byte(8'h33);
    send_byte(8'h33);
    send_byte(8'h33);

    // Final response
    recv_byte(magic);
    `CHECK_EQ(magic, RESP_MAGIC);

    recv_byte(status);
    `CHECK_EQ(status, 8'h00);
  endtask

  //
  // Test suite execution
  //
  `TEST_SUITE_BEGIN(svc_rv_dbg_bridge_tbi);
  `TEST_CASE(test_initial_state);
  `TEST_CASE(test_read_ctrl);
  `TEST_CASE(test_write_ctrl_release_reset);
  `TEST_CASE(test_write_ctrl_release_stall);
  `TEST_CASE(test_write_mem_imem);
  `TEST_CASE(test_write_mem_dmem);
  `TEST_CASE(test_write_burst_imem);
  `TEST_SUITE_END();

  `SVC_UNUSED({dbg_imem_wen, dbg_imem_waddr, dbg_imem_wstrb, dbg_dmem_wen,
               dbg_dmem_waddr, dbg_dmem_wstrb, dbg_dmem_ren, dbg_dmem_raddr});

endmodule
