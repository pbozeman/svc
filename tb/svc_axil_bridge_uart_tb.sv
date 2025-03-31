`include "svc_unit.sv"
`include "svc_axil_bridge_uart.sv"

// ✨🤖✨ tb vibe coded with claude

module svc_axil_bridge_uart_tb;
  `TEST_CLK_NS(clk, 10);
  `TEST_RST_N(clk, rst_n);

  // UART interface signals
  logic        urx_valid;
  logic [ 7:0] urx_data;
  logic        urx_ready;
  logic        utx_valid;
  logic [ 7:0] utx_data;
  logic        utx_ready;

  // AXI-Lite interface signals
  logic [31:0] m_axil_awaddr;
  logic        m_axil_awvalid;
  logic        m_axil_awready;
  logic [31:0] m_axil_wdata;
  logic [ 3:0] m_axil_wstrb;
  logic        m_axil_wvalid;
  logic        m_axil_wready;
  logic [ 1:0] m_axil_bresp;
  logic        m_axil_bvalid;
  logic        m_axil_bready;
  logic        m_axil_arvalid;
  logic [31:0] m_axil_araddr;
  logic        m_axil_arready;
  logic [31:0] m_axil_rdata;
  logic [ 1:0] m_axil_rresp;
  logic        m_axil_rvalid;
  logic        m_axil_rready;

  // Magic values for protocol
  localparam logic [15:0] CMD_MAGIC = 16'hF0B0;
  localparam logic [7:0] OP_READ = 8'h00;
  localparam logic [7:0] OP_WRITE = 8'h01;
  localparam logic [7:0] RESP_MAGIC = 8'hAB;

  // Memory array to store read responses
  logic [7:0] resp_data_bytes[0:5];
  int         resp_data_idx;
  logic       capturing_resp;

  // UUT instantiation
  svc_axil_bridge_uart uut (
      .clk  (clk),
      .rst_n(rst_n),

      .urx_valid(urx_valid),
      .urx_data (urx_data),
      .urx_ready(urx_ready),

      .utx_valid(utx_valid),
      .utx_data (utx_data),
      .utx_ready(utx_ready),

      .m_axil_awaddr (m_axil_awaddr),
      .m_axil_awvalid(m_axil_awvalid),
      .m_axil_awready(m_axil_awready),
      .m_axil_wdata  (m_axil_wdata),
      .m_axil_wstrb  (m_axil_wstrb),
      .m_axil_wvalid (m_axil_wvalid),
      .m_axil_wready (m_axil_wready),
      .m_axil_bresp  (m_axil_bresp),
      .m_axil_bvalid (m_axil_bvalid),
      .m_axil_bready (m_axil_bready),

      .m_axil_arvalid(m_axil_arvalid),
      .m_axil_araddr (m_axil_araddr),
      .m_axil_arready(m_axil_arready),
      .m_axil_rdata  (m_axil_rdata),
      .m_axil_rresp  (m_axil_rresp),
      .m_axil_rvalid (m_axil_rvalid),
      .m_axil_rready (m_axil_rready)
  );

  // Initialize signals in reset
  always_ff @(posedge clk) begin
    if (~rst_n) begin
      urx_valid      <= 1'b0;
      urx_data       <= 8'h00;
      utx_ready      <= 1'b1;

      m_axil_awready <= 1'b0;
      m_axil_wready  <= 1'b0;
      m_axil_bresp   <= 2'b00;
      m_axil_bvalid  <= 1'b0;
      m_axil_arready <= 1'b0;
      m_axil_rdata   <= 32'h00000000;
      m_axil_rresp   <= 2'b00;
      m_axil_rvalid  <= 1'b0;

      resp_data_idx  <= 0;
      capturing_resp <= 1'b0;
    end
  end

  // Response capture logic
  always_ff @(posedge clk) begin
    if (utx_valid && utx_ready) begin
      if (utx_data == RESP_MAGIC) begin
        resp_data_idx  <= 0;
        capturing_resp <= 1'b1;
      end else if (capturing_resp) begin
        resp_data_bytes[resp_data_idx] <= utx_data;
        resp_data_idx                  <= resp_data_idx + 1;
      end
    end
  end

  // Helper tasks for sending UART bytes
  task automatic send_byte(input logic [7:0] byte_data);
    urx_valid = 1'b1;
    urx_data  = byte_data;
    `CHECK_WAIT_FOR(clk, urx_ready, 10);
    `TICK(clk);
    urx_valid = 1'b0;
    `TICK(clk);
  endtask

  task automatic send_magic();
    send_byte(CMD_MAGIC[7:0]);
    send_byte(CMD_MAGIC[15:8]);
  endtask

  task automatic send_addr(input logic [31:0] addr);
    send_byte(addr[7:0]);
    send_byte(addr[15:8]);
    send_byte(addr[23:16]);
    send_byte(addr[31:24]);
  endtask

  task automatic send_data(input logic [31:0] data);
    send_byte(data[7:0]);
    send_byte(data[15:8]);
    send_byte(data[23:16]);
    send_byte(data[31:24]);
  endtask

  task automatic send_read_cmd(input logic [31:0] addr);
    send_magic();
    send_byte(OP_READ);
    send_addr(addr);
  endtask

  task automatic send_write_cmd(input logic [31:0] addr,
                                input logic [31:0] data);
    send_magic();
    send_byte(OP_WRITE);
    send_addr(addr);
    send_data(data);
  endtask

  task automatic wait_for_tx_complete();
    // Reset response capture state
    capturing_resp = 1'b0;
    resp_data_idx  = 0;

    // Wait for the first byte of response (RESP_MAGIC) to be transmitted
    `CHECK_WAIT_FOR(clk, utx_valid && utx_data == RESP_MAGIC, 50);

    // Wait for all response bytes to be transmitted
    // and for the transmitter to go idle
    `CHECK_WAIT_FOR(clk, !utx_valid, 100);
  endtask

  // Test reset behavior
  task automatic test_reset();
    `CHECK_FALSE(urx_valid);
    `CHECK_FALSE(m_axil_arvalid);
    `CHECK_FALSE(m_axil_awvalid);
    `CHECK_FALSE(m_axil_wvalid);
  endtask

  task automatic test_read_operation();
    logic [31:0] test_addr;
    logic [31:0] test_data;
    logic [ 1:0] test_resp;

    test_addr = 32'h12345678;
    test_data = 32'h87654321;
    test_resp = 2'b00;

    // Send read command
    send_read_cmd(test_addr);

    // Verify AXI read request
    `CHECK_WAIT_FOR(clk, m_axil_arvalid, 10);
    `CHECK_EQ(m_axil_araddr, test_addr);

    // Respond to read request
    m_axil_arready = 1'b1;
    `TICK(clk);
    m_axil_arready = 1'b0;

    // Wait a few cycles before sending read response
    repeat (2) `TICK(clk);

    m_axil_rdata  = test_data;
    m_axil_rresp  = test_resp;
    m_axil_rvalid = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_rready, 10);
    `TICK(clk);
    m_axil_rvalid = 1'b0;

    // Wait for and verify response
    wait_for_tx_complete();

    // Check response components
    `CHECK_EQ(resp_data_bytes[0], 8'(test_resp));
    `CHECK_EQ(resp_data_bytes[1], test_data[7:0]);
    `CHECK_EQ(resp_data_bytes[2], test_data[15:8]);
    `CHECK_EQ(resp_data_bytes[3], test_data[23:16]);
    `CHECK_EQ(resp_data_bytes[4], test_data[31:24]);
  endtask

  task automatic test_write_operation();
    logic [31:0] test_addr;
    logic [31:0] test_data;
    logic [ 1:0] test_resp;

    test_addr = 32'h87654321;
    test_data = 32'h12345678;
    test_resp = 2'b00;

    // Send write command
    send_write_cmd(test_addr, test_data);

    // Verify AXI write request
    `CHECK_WAIT_FOR(clk, m_axil_awvalid && m_axil_wvalid, 10);
    `CHECK_EQ(m_axil_wstrb, '1);
    `CHECK_EQ(m_axil_awaddr, test_addr);
    `CHECK_EQ(m_axil_wdata, test_data);

    // Respond to write address and data
    m_axil_awready = 1'b1;
    m_axil_wready  = 1'b1;
    `TICK(clk);
    m_axil_awready = 1'b0;
    m_axil_wready  = 1'b0;

    // Wait a few cycles before sending write response
    repeat (2) `TICK(clk);

    m_axil_bresp  = test_resp;
    m_axil_bvalid = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_bready, 10);
    `TICK(clk);
    m_axil_bvalid = 1'b0;

    // Wait for and verify response
    wait_for_tx_complete();

    // Check response components (write responses only have response code, no data)
    `CHECK_EQ(resp_data_bytes[0], 8'(test_resp));
  endtask

  task automatic test_invalid_op();
    // Send magic header
    send_magic();

    // Send invalid op
    send_byte(8'hFF);

    // Verify no AXI transactions initiated
    repeat (5) `TICK(clk);
    `CHECK_FALSE(m_axil_arvalid);
    `CHECK_FALSE(m_axil_awvalid);
    `CHECK_FALSE(m_axil_wvalid);
  endtask

  task automatic test_read_backpressure();
    logic [31:0] test_addr;
    logic [31:0] test_data;

    test_addr = 32'h11223344;
    test_data = 32'h55667788;

    // Send read command
    send_read_cmd(test_addr);

    // Address phase
    `CHECK_WAIT_FOR(clk, m_axil_arvalid, 10);
    m_axil_arready = 1'b1;
    `TICK(clk);
    m_axil_arready = 1'b0;

    // Delay read response to create backpressure
    repeat (10) `TICK(clk);

    // Send read response
    m_axil_rdata  = test_data;
    m_axil_rresp  = 2'b00;
    m_axil_rvalid = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_rready, 10);
    `TICK(clk);
    m_axil_rvalid = 1'b0;

    // Wait for and verify response
    wait_for_tx_complete();

    `CHECK_EQ(resp_data_bytes[0], 0);
    `CHECK_EQ(resp_data_bytes[1], test_data[7:0]);
    `CHECK_EQ(resp_data_bytes[2], test_data[15:8]);
    `CHECK_EQ(resp_data_bytes[3], test_data[23:16]);
    `CHECK_EQ(resp_data_bytes[4], test_data[31:24]);
  endtask

  task automatic test_tx_backpressure();
    logic [31:0] test_addr;
    logic [31:0] test_data;

    test_addr = 32'hAABBCCDD;
    test_data = 32'hEEFF0011;

    // Send read command
    send_read_cmd(test_addr);

    // Address phase
    `CHECK_WAIT_FOR(clk, m_axil_arvalid, 10);
    m_axil_arready = 1'b1;
    `TICK(clk);
    m_axil_arready = 1'b0;

    // Send read response
    m_axil_rdata   = test_data;
    m_axil_rresp   = 2'b00;
    m_axil_rvalid  = 1'b1;

    `CHECK_WAIT_FOR(clk, m_axil_rready, 10);
    `TICK(clk);
    m_axil_rvalid = 1'b0;

    // Create TX backpressure
    utx_ready     = 1'b0;
    repeat (5) `TICK(clk);

    // Check that TX hasn't completed handshake yet due to ready being low
    `CHECK_TRUE(utx_valid);

    // Release backpressure
    utx_ready = 1'b1;
    `TICK(clk);

    // Apply backpressure between bytes
    repeat (3) begin
      `TICK(clk);
      utx_ready = 1'b0;
      repeat (3) `TICK(clk);
      utx_ready = 1'b1;
      if (resp_data_idx < 5) begin
        `TICK(clk);
      end
    end

    // Wait for the transmission to complete
    repeat (20) `TICK(clk);

    // Check that we've received the response data
    `CHECK_EQ(resp_data_bytes[0], 8'h00);
    `CHECK_EQ(resp_data_bytes[1], test_data[7:0]);
    `CHECK_EQ(resp_data_bytes[2], test_data[15:8]);
    `CHECK_EQ(resp_data_bytes[3], test_data[23:16]);
    `CHECK_EQ(resp_data_bytes[4], test_data[31:24]);
  endtask

  task automatic test_invalid_magic();
    // Send invalid first byte
    send_byte(8'hAA);

    // No state change should occur
    repeat (5) `TICK(clk);
    `CHECK_FALSE(m_axil_arvalid);
    `CHECK_FALSE(m_axil_awvalid);

    // Send valid first byte but invalid second byte
    send_byte(CMD_MAGIC[7:0]);
    send_byte(8'hAA);  // Not the correct second magic byte

    // No state change should occur
    repeat (5) `TICK(clk);
    `CHECK_FALSE(m_axil_arvalid);
    `CHECK_FALSE(m_axil_awvalid);
  endtask

  `TEST_SUITE_BEGIN(svc_axil_bridge_uart_tb);
  `TEST_CASE(test_reset);
  `TEST_CASE(test_read_operation);
  `TEST_CASE(test_write_operation);
  `TEST_CASE(test_invalid_op);
  `TEST_CASE(test_read_backpressure);
  `TEST_CASE(test_tx_backpressure);
  `TEST_CASE(test_invalid_magic);
  `TEST_SUITE_END();

endmodule
