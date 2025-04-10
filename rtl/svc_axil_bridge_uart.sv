`ifndef SVC_AXIL_BRIDGE_UART_SV
`define SVC_AXIL_BRIDGE_UART_SV

`include "svc.sv"

// This is a very basic axil/uart bridge. It's designed for very basic
// debugging and/or command and control of benchmark modules running on
// the fpga. It isn't intended to be high performance, or to move lots of
// data in and out of the system.
//
// TODO: the implementation was straight line from 0 to demo. Go back
// and cleanup the read/write n-byte sort of functionality with the uart
// rather than having an explicit state per byte.
//
// Only 1 op can be outstanding at a time so that we don't have to worry
// about reads completing out of order from writes.
//
// The caller instantiates the uart_tx and uart_rx modules and only passes in
// the upper level (non pin) signals so that they can be multiplexed,
// if desired.
//
// The magic header is the crudest of protocol checks and is used to make
// sure we didn't drop a byte and end up out of alignment with the other
// side.
//
// Wire format:
//   Command:
//      Magic: 2 byte (0xF0B0)
//      Op: 1 byte
//      Payload: 4 to 8 bytes
//
//      Op:
//         0x00: read
//         0x01: write
//
//      Read payload:
//         32 bits: axi addr
//
//      Write payload:
//         32 bits: axi addr
//         32 bits: axi data
//
//  Response:
//      Magic: 1 byte (0xAB)
//      Resp: 1 byte (rresp or bresp)
//      Payload: 0 to 4 byes
//
//      Read resp payload:
//        32 bits: data response
//
//      Write resp payload: none
//
// It might be nice to break this up into a bridge interface that just
// does the uart processing and command/response serialization. This could
// then be passed to a more generic axi_bridge. This would make it easier
// to add other bridges, e.g. jtag, i2c, etc. But do the simple thing first
// for now (and maybe forever if no other protocols get added.)

module svc_axil_bridge_uart #(
    parameter AXIL_ADDR_WIDTH = 32,
    parameter AXIL_DATA_WIDTH = 32,
    parameter AXIL_STRB_WIDTH = AXIL_DATA_WIDTH / 8
) (
    input logic clk,
    input logic rst_n,

    input  logic       urx_valid,
    input  logic [7:0] urx_data,
    output logic       urx_ready,

    output logic       utx_valid,
    output logic [7:0] utx_data,
    input  logic       utx_ready,

    //
    // AXI-Lite subordinate interface
    //
    output logic [AXIL_ADDR_WIDTH-1:0] m_axil_awaddr,
    output logic                       m_axil_awvalid,
    input  logic                       m_axil_awready,
    output logic [AXIL_DATA_WIDTH-1:0] m_axil_wdata,
    output logic [AXIL_STRB_WIDTH-1:0] m_axil_wstrb,
    output logic                       m_axil_wvalid,
    input  logic                       m_axil_wready,
    input  logic [                1:0] m_axil_bresp,
    input  logic                       m_axil_bvalid,
    output logic                       m_axil_bready,

    output logic                       m_axil_arvalid,
    output logic [AXIL_ADDR_WIDTH-1:0] m_axil_araddr,
    input  logic                       m_axil_arready,
    input  logic [AXIL_DATA_WIDTH-1:0] m_axil_rdata,
    input  logic [                1:0] m_axil_rresp,
    input  logic                       m_axil_rvalid,
    output logic                       m_axil_rready
);
  localparam AW = AXIL_ADDR_WIDTH;
  localparam DW = AXIL_DATA_WIDTH;

  localparam logic [15:0] CMD_MAGIC = 16'hF0B0;
  localparam logic [7:0] OP_READ = 8'h00;
  localparam logic [7:0] OP_WRITE = 8'h01;

  localparam logic [7:0] RESP_MAGIC = 8'hAB;

  // TODO: the addr and data width are parameterized, but the states are not.
  // They should be using a more generic version of a byte iterator anyway.
  // As noted in the top comment, this is a straight line 0 to demo
  // implementation to get command and control off the ground.
  typedef enum {
    STATE_IDLE,
    STATE_CMD_MAGIC,
    STATE_CMD_OP,
    STATE_CMD_ADDR_0,
    STATE_CMD_ADDR_1,
    STATE_CMD_ADDR_2,
    STATE_CMD_ADDR_3,
    STATE_CMD_DATA_0,
    STATE_CMD_DATA_1,
    STATE_CMD_DATA_2,
    STATE_CMD_DATA_3,
    STATE_AXI_READ,
    STATE_AXI_READ_RESP,
    STATE_AXI_WRITE,
    STATE_AXI_WRITE_RESP,
    STATE_CMD_RESP_SEND,
    STATE_CMD_RESP_RESP,
    STATE_CMD_RESP_DATA_0,
    STATE_CMD_RESP_DATA_1,
    STATE_CMD_RESP_DATA_2,
    STATE_CMD_RESP_DATA_3
  } state_t;

  state_t          state;
  state_t          state_next;

  logic            cmd_rw;
  logic            cmd_rw_next;

  logic   [  31:0] cmd_addr;
  logic   [  31:0] cmd_addr_next;

  logic   [  31:0] cmd_data;
  logic   [  31:0] cmd_data_next;

  logic   [   1:0] cmd_resp;
  logic   [   1:0] cmd_resp_next;

  logic   [  31:0] cmd_resp_data;
  logic   [  31:0] cmd_resp_data_next;

  logic            m_axil_arvalid_next;
  logic   [AW-1:0] m_axil_araddr_next;

  logic            m_axil_awvalid_next;
  logic   [AW-1:0] m_axil_awaddr_next;

  logic            m_axil_wvalid_next;
  logic   [DW-1:0] m_axil_wdata_next;

  logic            utx_valid_next;
  logic   [   7:0] utx_data_next;

  logic            urx_ready_next;

  assign m_axil_wstrb = '1;

  always @(*) begin
    state_next          = state;

    cmd_rw_next         = cmd_rw;
    cmd_addr_next       = cmd_addr;
    cmd_data_next       = cmd_data;
    cmd_resp_next       = cmd_resp;
    cmd_resp_data_next  = cmd_resp_data;

    m_axil_arvalid_next = m_axil_arvalid && !m_axil_arready;
    m_axil_awvalid_next = m_axil_awvalid && !m_axil_awready;
    m_axil_wvalid_next  = m_axil_wvalid && !m_axil_wready;

    m_axil_araddr_next  = m_axil_araddr;
    m_axil_awaddr_next  = m_axil_awaddr;
    m_axil_wdata_next   = m_axil_wdata;

    m_axil_rready       = 1'b0;
    m_axil_bready       = 1'b0;

    utx_valid_next      = utx_valid && !utx_ready;
    utx_data_next       = utx_data;

    urx_ready_next      = urx_ready;

    case (state)
      STATE_IDLE: begin
        urx_ready_next = 1'b1;

        if (urx_valid && urx_ready) begin
          if (urx_data == CMD_MAGIC[7:0]) begin
            state_next = STATE_CMD_MAGIC;
          end
        end
      end

      STATE_CMD_MAGIC: begin
        if (urx_valid && urx_ready) begin
          if (urx_data == CMD_MAGIC[15:8]) begin
            state_next = STATE_CMD_OP;
          end else begin
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_CMD_OP: begin
        if (urx_valid && urx_ready) begin
          case (urx_data)
            OP_READ: begin
              cmd_rw_next = 1'b0;
              state_next  = STATE_CMD_ADDR_0;
            end

            OP_WRITE: begin
              cmd_rw_next = 1'b1;
              state_next  = STATE_CMD_ADDR_0;
            end

            default: begin
              state_next = STATE_IDLE;
            end
          endcase
        end
      end

      STATE_CMD_ADDR_0: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next[7:0] = urx_data;
          state_next         = STATE_CMD_ADDR_1;
        end
      end

      STATE_CMD_ADDR_1: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next[15:8] = urx_data;
          state_next          = STATE_CMD_ADDR_2;
        end
      end

      STATE_CMD_ADDR_2: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next[23:16] = urx_data;
          state_next           = STATE_CMD_ADDR_3;
        end
      end

      STATE_CMD_ADDR_3: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next[31:24] = urx_data;
          if (cmd_rw) begin
            state_next = STATE_CMD_DATA_0;
          end else begin
            // Don't accept new UART data while processing AXI request
            urx_ready_next = 1'b0;
            state_next     = STATE_AXI_READ;
          end
        end
      end

      STATE_CMD_DATA_0: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next[7:0] = urx_data;
          state_next         = STATE_CMD_DATA_1;
        end
      end

      STATE_CMD_DATA_1: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next[15:8] = urx_data;
          state_next          = STATE_CMD_DATA_2;
        end
      end

      STATE_CMD_DATA_2: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next[23:16] = urx_data;
          state_next           = STATE_CMD_DATA_3;
        end
      end

      STATE_CMD_DATA_3: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next[31:24] = urx_data;

          // Don't accept new UART data while processing AXI request
          urx_ready_next       = 1'b0;
          state_next           = STATE_AXI_WRITE;
        end
      end

      STATE_AXI_READ: begin
        if (!m_axil_arvalid) begin
          m_axil_arvalid_next = 1'b1;
          m_axil_araddr_next  = AW'(cmd_addr);
          state_next          = STATE_AXI_READ_RESP;
        end
      end

      STATE_AXI_READ_RESP: begin
        m_axil_rready = 1'b1;
        if (m_axil_rvalid) begin
          cmd_resp_next      = m_axil_rresp;
          cmd_resp_data_next = 32'(m_axil_rdata);
          state_next         = STATE_CMD_RESP_SEND;
        end
      end

      STATE_AXI_WRITE: begin
        // we're designing for simplicity in this module, not perf,
        // otherwise we would not wait for both channels (given that we
        // wait on bresp, it's unlikely that either are still high though,
        // unless subordinate is very badly designed)
        if (!m_axil_awvalid && !m_axil_wvalid) begin
          m_axil_awvalid_next = 1'b1;
          m_axil_awaddr_next  = AW'(cmd_addr);
          m_axil_wvalid_next  = 1'b1;
          m_axil_wdata_next   = DW'(cmd_data);
          state_next          = STATE_AXI_WRITE_RESP;
        end
      end

      STATE_AXI_WRITE_RESP: begin
        m_axil_bready = 1'b1;
        if (m_axil_bvalid) begin
          cmd_resp_next = m_axil_bresp;
          state_next    = STATE_CMD_RESP_SEND;
        end
      end

      STATE_CMD_RESP_SEND: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = RESP_MAGIC;
          state_next     = STATE_CMD_RESP_RESP;
        end
      end

      STATE_CMD_RESP_RESP: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = 8'(cmd_resp);
          if (!cmd_rw) begin
            state_next = STATE_CMD_RESP_DATA_0;
          end else begin
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_CMD_RESP_DATA_0: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = cmd_resp_data[7:0];
          state_next     = STATE_CMD_RESP_DATA_1;
        end
      end

      STATE_CMD_RESP_DATA_1: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = cmd_resp_data[15:8];
          state_next     = STATE_CMD_RESP_DATA_2;
        end
      end

      STATE_CMD_RESP_DATA_2: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = cmd_resp_data[23:16];
          state_next     = STATE_CMD_RESP_DATA_3;
        end
      end

      STATE_CMD_RESP_DATA_3: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = cmd_resp_data[31:24];
          state_next     = STATE_IDLE;
        end
      end

      default: begin
      end
    endcase
  end

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state          <= STATE_IDLE;

      m_axil_arvalid <= 1'b0;
      m_axil_awvalid <= 1'b0;
      m_axil_wvalid  <= 1'b0;

      utx_valid      <= 1'b0;
      utx_data       <= 8'h00;

      urx_ready      <= 1'b1;
    end else begin
      state          <= state_next;

      m_axil_arvalid <= m_axil_arvalid_next;
      m_axil_awvalid <= m_axil_awvalid_next;
      m_axil_wvalid  <= m_axil_wvalid_next;

      utx_valid      <= utx_valid_next;
      utx_data       <= utx_data_next;

      urx_ready      <= urx_ready_next;
    end
  end

  always_ff @(posedge clk) begin
    cmd_rw        <= cmd_rw_next;
    cmd_addr      <= cmd_addr_next;
    cmd_data      <= cmd_data_next;

    cmd_resp      <= cmd_resp_next;
    cmd_resp_data <= cmd_resp_data_next;

    m_axil_wdata  <= m_axil_wdata_next;
    m_axil_awaddr <= m_axil_awaddr_next;
    m_axil_araddr <= m_axil_araddr_next;
  end

endmodule
`endif
