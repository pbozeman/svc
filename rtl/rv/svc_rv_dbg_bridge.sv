`ifndef SVC_RV_DBG_BRIDGE_SV
`define SVC_RV_DBG_BRIDGE_SV

`include "svc.sv"

//
// Debug bridge for RISC-V SoC
//
// Provides UART-based debug interface for:
// - CPU stall/reset control
// - Direct memory writes to IMEM and DMEM (Harvard architecture)
//
// Wire format:
//   Command:
//      Magic: 1 byte (0xDB)
//      Op: 1 byte
//         0x00: read control register
//         0x01: write control register
//         0x02: write memory (single word)
//         0x03: write memory burst (multiple words)
//      Payload: variable
//
//      Read control payload:
//         None (reads and returns current control state)
//
//      Write control payload:
//         1 byte: control value (bit 0: stall, bit 1: reset)
//
//      Write memory payload:
//         4 bytes: address (little-endian)
//         4 bytes: data (little-endian)
//
//      Write memory burst payload:
//         4 bytes: start address (little-endian)
//         2 bytes: word count (little-endian, max 65535 words)
//         N*4 bytes: data words (little-endian, streamed back-to-back)
//
//   Response:
//      Magic: 1 byte (0xBD)
//      Status: 1 byte (0=OK, 1=error)
//      Payload: 0-4 bytes
//
//      Read control response:
//         1 byte: control value (bit 0: stalled, bit 1: in_reset)
//
//      Write responses:
//         None (just magic + status)
//
// Address decode (ADDR_WIDTH is word address width, so byte range is 4x larger):
//   IMEM range: IMEM_BASE_ADDR to IMEM_BASE_ADDR + (4 << IMEM_ADDR_WIDTH) - 1
//   DMEM range: DMEM_BASE_ADDR to DMEM_BASE_ADDR + (4 << DMEM_ADDR_WIDTH) - 1
//
module svc_rv_dbg_bridge #(
    parameter int IMEM_ADDR_WIDTH = 16,
    parameter int DMEM_ADDR_WIDTH = 16,

    parameter logic [31:0] IMEM_BASE_ADDR = 32'h0000_0000,
    parameter logic [31:0] DMEM_BASE_ADDR = 32'h0001_0000
) (
    input logic clk,
    input logic rst_n,

    // UART RX interface
    input  logic       urx_valid,
    input  logic [7:0] urx_data,
    output logic       urx_ready,

    // UART TX interface
    output logic       utx_valid,
    output logic [7:0] utx_data,
    input  logic       utx_ready,

    // CPU control outputs
    output logic dbg_stall,
    output logic dbg_rst_n,

    // IMEM write interface
    output logic                       dbg_imem_wen,
    output logic [IMEM_ADDR_WIDTH-1:0] dbg_imem_waddr,
    output logic [               31:0] dbg_imem_wdata,
    output logic [                3:0] dbg_imem_wstrb,

    // DMEM write interface
    output logic                       dbg_dmem_wen,
    output logic [DMEM_ADDR_WIDTH-1:0] dbg_dmem_waddr,
    output logic [               31:0] dbg_dmem_wdata,
    output logic [                3:0] dbg_dmem_wstrb,

    // Flow control for cache mode (optional - tie to 0 for BRAM)
    input logic dbg_dmem_busy
);
  // Protocol constants
  localparam logic [7:0] CMD_MAGIC = 8'hDB;
  localparam logic [7:0] RESP_MAGIC = 8'hBD;

  localparam logic [7:0] OP_READ_CTRL = 8'h00;
  localparam logic [7:0] OP_WRITE_CTRL = 8'h01;
  localparam logic [7:0] OP_WRITE_MEM = 8'h02;
  localparam logic [7:0] OP_WRITE_BURST = 8'h03;

  localparam logic [7:0] STATUS_OK = 8'h00;
  localparam logic [7:0] STATUS_ERROR = 8'h01;

  // State machine
  typedef enum logic [4:0] {
    STATE_IDLE,
    STATE_CMD_OP,
    // Write control states
    STATE_CTRL_DATA,
    // Write memory states
    STATE_MEM_ADDR_0,
    STATE_MEM_ADDR_1,
    STATE_MEM_ADDR_2,
    STATE_MEM_ADDR_3,
    STATE_MEM_DATA_0,
    STATE_MEM_DATA_1,
    STATE_MEM_DATA_2,
    STATE_MEM_DATA_3,
    // Burst states
    STATE_BURST_LEN_0,
    STATE_BURST_LEN_1,
    STATE_BURST_DATA_0,
    STATE_BURST_DATA_1,
    STATE_BURST_DATA_2,
    STATE_BURST_DATA_3,
    // Memory write execution
    STATE_MEM_WRITE,
    STATE_MEM_WAIT,
    // Response states
    STATE_RESP_MAGIC,
    STATE_RESP_STATUS,
    STATE_RESP_DATA
  } state_t;

  state_t        state;
  state_t        state_next;

  // Command registers
  logic   [ 7:0] cmd_op;
  logic   [ 7:0] cmd_op_next;
  logic   [31:0] cmd_addr;
  logic   [31:0] cmd_addr_next;
  logic   [31:0] cmd_data;
  logic   [31:0] cmd_data_next;
  logic   [15:0] burst_len;
  logic   [15:0] burst_len_next;
  logic   [15:0] burst_cnt;
  logic   [15:0] burst_cnt_next;

  // Response registers
  logic   [ 7:0] resp_status;
  logic   [ 7:0] resp_status_next;
  logic   [ 7:0] resp_data;
  logic   [ 7:0] resp_data_next;

  // Control registers (directly output)
  logic          ctrl_stall;
  logic          ctrl_stall_next;
  logic          ctrl_rst_n;
  logic          ctrl_rst_n_next;

  // UART interface registers
  logic          urx_ready_next;
  logic          utx_valid_next;
  logic   [ 7:0] utx_data_next;

  // Memory write registers
  logic          mem_wen;
  logic          mem_wen_next;
  logic   [31:0] mem_waddr;
  logic   [31:0] mem_waddr_next;

  // Address decode (use registered write address for memory outputs)
  logic          imem_select;
  logic          dmem_select;

  // Use generate to avoid UNSIGNED warning when base address is 0
  // Note: ADDR_WIDTH is in words, so add 2 to get byte address width
  generate
    if (IMEM_BASE_ADDR == 0) begin : g_imem_at_zero
      assign imem_select = mem_waddr < (32'h1 << (IMEM_ADDR_WIDTH + 2));
    end else begin : g_imem_offset
      assign imem_select = (mem_waddr >= IMEM_BASE_ADDR) &&
          (mem_waddr < (IMEM_BASE_ADDR + (32'h1 << (IMEM_ADDR_WIDTH + 2))));
    end

    if (DMEM_ADDR_WIDTH >= 30 && DMEM_BASE_ADDR == 0) begin : g_dmem_full_range
      assign dmem_select = 1'b1;
    end else if (DMEM_BASE_ADDR == 0) begin : g_dmem_at_zero
      assign dmem_select = mem_waddr < (32'h1 << (DMEM_ADDR_WIDTH + 2));
    end else begin : g_dmem_offset
      assign dmem_select = (mem_waddr >= DMEM_BASE_ADDR) &&
          (mem_waddr < (DMEM_BASE_ADDR + (32'h1 << (DMEM_ADDR_WIDTH + 2))));
    end
  endgenerate

  // Control outputs
  assign dbg_stall = ctrl_stall;
  assign dbg_rst_n = ctrl_rst_n;

  // Memory write outputs (use mem_waddr which is captured before increment)
  // Subtract base address before extracting word address to handle non-zero bases
  logic [31:0] imem_offset_addr;
  logic [31:0] dmem_offset_addr;

  assign imem_offset_addr = mem_waddr - IMEM_BASE_ADDR;
  assign dmem_offset_addr = mem_waddr - DMEM_BASE_ADDR;

  assign dbg_imem_wen     = mem_wen && imem_select;
  assign dbg_imem_waddr   = imem_offset_addr[2+:IMEM_ADDR_WIDTH];
  assign dbg_imem_wdata   = cmd_data;
  assign dbg_imem_wstrb   = 4'hF;

  assign dbg_dmem_wen     = mem_wen && dmem_select;
  assign dbg_dmem_waddr   = dmem_offset_addr[2+:DMEM_ADDR_WIDTH];
  assign dbg_dmem_wdata   = cmd_data;
  assign dbg_dmem_wstrb   = 4'hF;

  `SVC_UNUSED({imem_offset_addr, dmem_offset_addr})

  // Pre-extract bit slices to avoid Icarus "constant selects" warnings
  logic        urx_data_bit0;
  logic        urx_data_bit1;
  logic [23:0] cmd_addr_23_0;
  logic [15:0] cmd_addr_15_0;
  logic [ 7:0] cmd_addr_7_0;
  logic [23:0] cmd_addr_31_8;
  logic [15:0] cmd_addr_31_16;
  logic [ 7:0] cmd_addr_31_24;
  logic [23:0] cmd_data_23_0;
  logic [15:0] cmd_data_15_0;
  logic [ 7:0] cmd_data_7_0;
  logic [23:0] cmd_data_31_8;
  logic [15:0] cmd_data_31_16;
  logic [ 7:0] cmd_data_31_24;
  logic [ 7:0] burst_len_7_0;
  logic [ 7:0] burst_len_15_8;

  assign urx_data_bit0  = urx_data[0];
  assign urx_data_bit1  = urx_data[1];
  assign cmd_addr_23_0  = cmd_addr[23:0];
  assign cmd_addr_15_0  = cmd_addr[15:0];
  assign cmd_addr_7_0   = cmd_addr[7:0];
  assign cmd_addr_31_8  = cmd_addr[31:8];
  assign cmd_addr_31_16 = cmd_addr[31:16];
  assign cmd_addr_31_24 = cmd_addr[31:24];
  assign cmd_data_23_0  = cmd_data[23:0];
  assign cmd_data_15_0  = cmd_data[15:0];
  assign cmd_data_7_0   = cmd_data[7:0];
  assign cmd_data_31_8  = cmd_data[31:8];
  assign cmd_data_31_16 = cmd_data[31:16];
  assign cmd_data_31_24 = cmd_data[31:24];
  assign burst_len_7_0  = burst_len[7:0];
  assign burst_len_15_8 = burst_len[15:8];

  // State machine
  always_comb begin
    state_next       = state;

    cmd_op_next      = cmd_op;
    cmd_addr_next    = cmd_addr;
    cmd_data_next    = cmd_data;
    burst_len_next   = burst_len;
    burst_cnt_next   = burst_cnt;

    resp_status_next = resp_status;
    resp_data_next   = resp_data;

    ctrl_stall_next  = ctrl_stall;
    ctrl_rst_n_next  = ctrl_rst_n;

    urx_ready_next   = urx_ready;
    utx_valid_next   = utx_valid && !utx_ready;
    utx_data_next    = utx_data;

    mem_wen_next     = 1'b0;
    mem_waddr_next   = mem_waddr;

    case (state)
      STATE_IDLE: begin
        urx_ready_next = 1'b1;
        if (urx_valid && urx_ready) begin
          if (urx_data == CMD_MAGIC) begin
            state_next = STATE_CMD_OP;
          end
        end
      end

      STATE_CMD_OP: begin
        if (urx_valid && urx_ready) begin
          cmd_op_next = urx_data;
          case (urx_data)
            OP_READ_CTRL: begin
              urx_ready_next   = 1'b0;
              resp_status_next = STATUS_OK;
              resp_data_next   = {6'b0, ~ctrl_rst_n, ctrl_stall};
              state_next       = STATE_RESP_MAGIC;
            end

            OP_WRITE_CTRL: begin
              state_next = STATE_CTRL_DATA;
            end

            OP_WRITE_MEM: begin
              state_next = STATE_MEM_ADDR_0;
            end

            OP_WRITE_BURST: begin
              state_next = STATE_MEM_ADDR_0;
            end

            default: begin
              // Unknown op, send error response
              urx_ready_next   = 1'b0;
              resp_status_next = STATUS_ERROR;
              state_next       = STATE_RESP_MAGIC;
            end
          endcase
        end
      end

      // Write control state
      STATE_CTRL_DATA: begin
        if (urx_valid && urx_ready) begin
          ctrl_stall_next  = urx_data_bit0;
          ctrl_rst_n_next  = ~urx_data_bit1;
          urx_ready_next   = 1'b0;
          resp_status_next = STATUS_OK;
          state_next       = STATE_RESP_MAGIC;
        end
      end

      // Address reception states
      STATE_MEM_ADDR_0: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next = {cmd_addr_31_8, urx_data};
          state_next    = STATE_MEM_ADDR_1;
        end
      end

      STATE_MEM_ADDR_1: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next = {cmd_addr_31_16, urx_data, cmd_addr_7_0};
          state_next    = STATE_MEM_ADDR_2;
        end
      end

      STATE_MEM_ADDR_2: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next = {cmd_addr_31_24, urx_data, cmd_addr_15_0};
          state_next    = STATE_MEM_ADDR_3;
        end
      end

      STATE_MEM_ADDR_3: begin
        if (urx_valid && urx_ready) begin
          cmd_addr_next = {urx_data, cmd_addr_23_0};
          if (cmd_op == OP_WRITE_BURST) begin
            state_next = STATE_BURST_LEN_0;
          end else begin
            state_next = STATE_MEM_DATA_0;
          end
        end
      end

      // Single word data reception
      STATE_MEM_DATA_0: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next = {cmd_data_31_8, urx_data};
          state_next    = STATE_MEM_DATA_1;
        end
      end

      STATE_MEM_DATA_1: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next = {cmd_data_31_16, urx_data, cmd_data_7_0};
          state_next    = STATE_MEM_DATA_2;
        end
      end

      STATE_MEM_DATA_2: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next = {cmd_data_31_24, urx_data, cmd_data_15_0};
          state_next    = STATE_MEM_DATA_3;
        end
      end

      STATE_MEM_DATA_3: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next  = {urx_data, cmd_data_23_0};
          urx_ready_next = 1'b0;
          state_next     = STATE_MEM_WRITE;
        end
      end

      // Burst length reception
      STATE_BURST_LEN_0: begin
        if (urx_valid && urx_ready) begin
          burst_len_next = {burst_len_15_8, urx_data};
          state_next     = STATE_BURST_LEN_1;
        end
      end

      STATE_BURST_LEN_1: begin
        if (urx_valid && urx_ready) begin
          burst_len_next = {urx_data, burst_len_7_0};
          burst_cnt_next = 16'h0;
          state_next     = STATE_BURST_DATA_0;
        end
      end

      // Burst data reception
      STATE_BURST_DATA_0: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next = {cmd_data_31_8, urx_data};
          state_next    = STATE_BURST_DATA_1;
        end
      end

      STATE_BURST_DATA_1: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next = {cmd_data_31_16, urx_data, cmd_data_7_0};
          state_next    = STATE_BURST_DATA_2;
        end
      end

      STATE_BURST_DATA_2: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next = {cmd_data_31_24, urx_data, cmd_data_15_0};
          state_next    = STATE_BURST_DATA_3;
        end
      end

      STATE_BURST_DATA_3: begin
        if (urx_valid && urx_ready) begin
          cmd_data_next  = {urx_data, cmd_data_23_0};
          urx_ready_next = 1'b0;
          state_next     = STATE_MEM_WRITE;
        end
      end

      // Execute memory write
      STATE_MEM_WRITE: begin
        mem_wen_next     = 1'b1;
        mem_waddr_next   = cmd_addr;
        resp_status_next = STATUS_OK;

        if (cmd_op == OP_WRITE_BURST) begin
          cmd_addr_next  = cmd_addr + 32'h4;
          burst_cnt_next = burst_cnt + 16'h1;
        end

        state_next = STATE_MEM_WAIT;
      end

      // Wait for memory write to complete (cache mode flow control)
      STATE_MEM_WAIT: begin
        if (!dbg_dmem_busy) begin
          if (cmd_op == OP_WRITE_BURST) begin
            if (burst_cnt >= burst_len) begin
              state_next = STATE_RESP_MAGIC;
            end else begin
              // Stream next word immediately (no per-word ACK)
              urx_ready_next = 1'b1;
              state_next     = STATE_BURST_DATA_0;
            end
          end else begin
            state_next = STATE_RESP_MAGIC;
          end
        end
      end

      // Response states
      STATE_RESP_MAGIC: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = RESP_MAGIC;
          state_next     = STATE_RESP_STATUS;
        end
      end

      STATE_RESP_STATUS: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = resp_status;
          if (cmd_op == OP_READ_CTRL) begin
            state_next = STATE_RESP_DATA;
          end else begin
            state_next = STATE_IDLE;
          end
        end
      end

      STATE_RESP_DATA: begin
        if (!utx_valid || utx_ready) begin
          utx_valid_next = 1'b1;
          utx_data_next  = resp_data;
          state_next     = STATE_IDLE;
        end
      end

      default: begin
        state_next = STATE_IDLE;
      end
    endcase
  end

  // Sequential logic
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      state      <= STATE_IDLE;
      ctrl_stall <= 1'b1;
      ctrl_rst_n <= 1'b0;
      urx_ready  <= 1'b1;
      utx_valid  <= 1'b0;
      utx_data   <= 8'h00;
      mem_wen    <= 1'b0;
      mem_waddr  <= 32'h0;
    end else begin
      state      <= state_next;
      ctrl_stall <= ctrl_stall_next;
      ctrl_rst_n <= ctrl_rst_n_next;
      urx_ready  <= urx_ready_next;
      utx_valid  <= utx_valid_next;
      utx_data   <= utx_data_next;
      mem_wen    <= mem_wen_next;
      mem_waddr  <= mem_waddr_next;
    end
  end

  // Non-reset registers
  always_ff @(posedge clk) begin
    cmd_op      <= cmd_op_next;
    cmd_addr    <= cmd_addr_next;
    cmd_data    <= cmd_data_next;
    burst_len   <= burst_len_next;
    burst_cnt   <= burst_cnt_next;
    resp_status <= resp_status_next;
    resp_data   <= resp_data_next;
  end

endmodule

`endif
