# SVC Module Overview

This document provides a comprehensive reference of the main modules in the SVC
(SystemVerilog Core) repository, including their interfaces, parameters, and
usage patterns. This will be particularly useful when working with AI assistants
like Claude that don't have direct access to the repository files.

## Core Infrastructure

### `svc.sv`

Base include file with fundamental definitions.

```systemverilog
`include "svc.sv"  // Include this in all modules
```

**Key Macros:**

- `SVC_MAX_AXSIZE(dw)`: Calculates maximum AXI size based on data width

### `svc_unit.sv`

Testing framework for SystemVerilog designed to work with iverilog.

**Key Macros:**

```systemverilog
`TEST_CLK_NS(clk, 10);              // Create 10ns clock
`TEST_RST_N(clk, rst_n);            // Setup reset signal
`CHECK_TRUE(condition);             // Assert condition is true
`CHECK_EQ(a, b);                    // Assert a equals b
`TEST_SUITE_BEGIN(module_name_tb);  // Start test suite
`TEST_CASE(test_function);          // Define test case
`TEST_SUITE_END();                  // End test suite
```

### `svc_unused.sv`

Utility for handling unused signals to prevent linting warnings.

```systemverilog
`SVC_UNUSED({signal1, signal2, signal3});
```

## Basic Building Blocks

### `svc_delay.sv`

Configurable cycle delay element.

**Parameters:**

- `WIDTH`: Width of the data signal
- `CYCLES`: Number of cycles to delay

**Interface:**

```systemverilog
module svc_delay #(
    parameter WIDTH  = 8,
    parameter CYCLES = 1
) (
    input  logic             clk,
    input  logic             rst_n,
    input  logic [WIDTH-1:0] in,
    output logic [WIDTH-1:0] out
);
```

### `svc_edge_rose.sv`

Rising edge detection.

**Interface:**

```systemverilog
module svc_edge_rose (
    input  logic clk,
    input  logic rst_n,
    input  logic in,
    output logic out  // Single-cycle pulse on rising edge
);
```

### `svc_edge_fell.sv`

Falling edge detection.

**Interface:**

```systemverilog
module svc_edge_fell (
    input  logic clk,
    input  logic rst_n,
    input  logic in,
    output logic out  // Single-cycle pulse on falling edge
);
```

### `svc_sticky_bit.sv`

Implements a bit that stays set once triggered until explicitly cleared.

**Interface:**

```systemverilog
module svc_sticky_bit (
    input  logic clk,
    input  logic rst_n,
    input  logic set,   // Set the sticky bit
    input  logic clear, // Clear the sticky bit
    output logic value  // Current sticky bit value
);
```

### `svc_priority_encoder.sv`

Converts one-hot or binary input to encoded output.

**Parameters:**

- `WIDTH`: Width of unencoded input
- `ENCODED_WIDTH`: Width of encoded output (defaults to log2(WIDTH))

**Interface:**

```systemverilog
module svc_priority_encoder #(
    parameter WIDTH        = 8,
    parameter ENCODED_WIDTH = $clog2(WIDTH)
) (
    input  logic [   WIDTH-1:0] i_unencoded,  // Input vector
    output logic                o_valid,      // Valid indicator (any bit set)
    output logic [ENCODED_WIDTH-1:0] o_encoded  // Encoded priority output
);
```

## Memory and FIFOs

### `svc_sync_fifo.sv`

Synchronous FIFO with First-Word Fall-Through (FWFT).

**Parameters:**

- `ADDR_WIDTH`: Bit width of address (FIFO depth is 2^ADDR_WIDTH)
- `DATA_WIDTH`: Bit width of data

**Interface:**

```systemverilog
module svc_sync_fifo #(
    parameter ADDR_WIDTH = 3,
    parameter DATA_WIDTH = 8
) (
    input  logic                  clk,
    input  logic                  rst_n,
    // Write interface
    input  logic                  w_inc,      // Write increment
    input  logic [DATA_WIDTH-1:0] w_data,     // Write data
    output logic                  w_full,     // FIFO full indicator
    output logic                  w_half_full,// FIFO half full indicator
    // Read interface
    input  logic                  r_inc,      // Read increment
    output logic                  r_empty,    // FIFO empty indicator
    output logic [DATA_WIDTH-1:0] r_data      // Read data (FWFT)
);
```

### `svc_sync_fifo_n.sv`

Synchronous FIFO with depth of at least N elements.

**Parameters:**

- `N`: Minimum depth of FIFO
- `DATA_WIDTH`: Bit width of data
- `ADDR_WIDTH`: Set automatically based on N

**Interface:** Same as `svc_sync_fifo`

### `svc_sync_fifo_n1.sv`

Optimized version of sync FIFO for single-element depth.

**Parameters:**

- `DATA_WIDTH`: Bit width of data

**Interface:** Same as `svc_sync_fifo` (except ADDR_WIDTH)

### `svc_sync_fifo_zl.sv`

Zero-latency FIFO with customizable depth.

**Parameters:**

- `ADDR_WIDTH`: Bit width of address (FIFO depth is 2^ADDR_WIDTH)
- `DATA_WIDTH`: Bit width of data

**Interface:** Same as `svc_sync_fifo`

### `svc_sync_fifo_zl1.sv`

Zero-latency FIFO optimized for single-element depth.

**Parameters:**

- `DATA_WIDTH`: Bit width of data

**Interface:** Same as `svc_sync_fifo_n1`

### `svc_cdc_fifo.sv`

Clock Domain Crossing FIFO.

**Parameters:**

- `ADDR_WIDTH`: Bit width of address (FIFO depth is 2^ADDR_WIDTH)
- `DATA_WIDTH`: Bit width of data

**Interface:**

```systemverilog
module svc_cdc_fifo #(
    parameter ADDR_WIDTH = 3,
    parameter DATA_WIDTH = 8
) (
    // Write domain
    input  logic                  w_clk,      // Write clock
    input  logic                  w_rst_n,    // Write reset
    input  logic                  w_inc,      // Write increment
    input  logic [DATA_WIDTH-1:0] w_data,     // Write data
    output logic                  w_full,     // FIFO full indicator
    // Read domain
    input  logic                  r_clk,      // Read clock
    input  logic                  r_rst_n,    // Read reset
    input  logic                  r_inc,      // Read increment
    output logic                  r_empty,    // FIFO empty indicator
    output logic [DATA_WIDTH-1:0] r_data      // Read data
);
```

### `svc_skidbuf.sv`

Skid buffer for improved timing and handling backpressure.

**Parameters:**

- `WIDTH`: Width of data path

**Interface:**

```systemverilog
module svc_skidbuf #(
    parameter WIDTH = 8
) (
    input  logic             clk,
    input  logic             rst_n,
    // Input interface
    input  logic             s_valid,    // Input valid
    output logic             s_ready,    // Input ready
    input  logic [WIDTH-1:0] s_data,     // Input data
    // Output interface
    output logic             m_valid,    // Output valid
    input  logic             m_ready,    // Output ready
    output logic [WIDTH-1:0] m_data      // Output data
);
```

## Arbitration

### `svc_arbiter.sv`

Round-robin arbiter for multiple requesters.

**Parameters:**

- `NUM_M`: Number of requesters
- `IDX_WIDTH`: Bit width of grant index (defaults to log2(NUM_M))

**Interface:**

```systemverilog
module svc_arbiter #(
    parameter NUM_M     = 2,
    parameter IDX_WIDTH = $clog2(NUM_M)
) (
    input  logic                 clk,
    input  logic                 rst_n,
    input  logic [NUM_M-1:0]     request,      // Request signals from managers
    input  logic                 done,         // Current grant is complete
    output logic                 grant_valid,  // Valid grant indicator
    output logic [IDX_WIDTH-1:0] grant_idx     // Index of granted request
);
```

## AXI Infrastructure

### `svc_axi_arbiter.sv`

Arbitrates between multiple AXI managers to a single subordinate.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width
- `AXI_ID_WIDTH`: ID width
- `NUM_MANAGERS`: Number of manager interfaces to arbitrate

**Interface:**

```systemverilog
module svc_axi_arbiter #(
    parameter AXI_ADDR_WIDTH = 32,
    parameter AXI_DATA_WIDTH = 32,
    parameter AXI_ID_WIDTH   = 4,
    parameter NUM_MANAGERS   = 2
) (
    input logic clk,
    input logic rst_n,

    // Manager 0 AXI interface
    input  logic                      m0_axi_awvalid,
    input  logic [AXI_ADDR_WIDTH-1:0] m0_axi_awaddr,
    input  logic [  AXI_ID_WIDTH-1:0] m0_axi_awid,
    input  logic [               7:0] m0_axi_awlen,
    input  logic [               2:0] m0_axi_awsize,
    input  logic [               1:0] m0_axi_awburst,
    output logic                      m0_axi_awready,
    // Write data channel
    input  logic                      m0_axi_wvalid,
    input  logic [AXI_DATA_WIDTH-1:0] m0_axi_wdata,
    input  logic [AXI_DATA_WIDTH/8-1:0] m0_axi_wstrb,
    input  logic                      m0_axi_wlast,
    output logic                      m0_axi_wready,
    // Write response channel
    output logic                      m0_axi_bvalid,
    output logic [  AXI_ID_WIDTH-1:0] m0_axi_bid,
    output logic [               1:0] m0_axi_bresp,
    input  logic                      m0_axi_bready,
    // Read address channel
    input  logic                      m0_axi_arvalid,
    input  logic [  AXI_ID_WIDTH-1:0] m0_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] m0_axi_araddr,
    input  logic [               7:0] m0_axi_arlen,
    input  logic [               2:0] m0_axi_arsize,
    input  logic [               1:0] m0_axi_arburst,
    output logic                      m0_axi_arready,
    // Read data channel
    output logic                      m0_axi_rvalid,
    output logic [  AXI_ID_WIDTH-1:0] m0_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] m0_axi_rdata,
    output logic [               1:0] m0_axi_rresp,
    output logic                      m0_axi_rlast,
    input  logic                      m0_axi_rready,

    // Manager 1 AXI interface (if NUM_MANAGERS > 1)
    // [Same interface as Manager 0, with m1_ prefix]

    // Subordinate AXI interface (single output)
    output logic                      s_axi_awvalid,
    output logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_awid,
    output logic [               7:0] s_axi_awlen,
    output logic [               2:0] s_axi_awsize,
    output logic [               1:0] s_axi_awburst,
    input  logic                      s_axi_awready,
    // Write data channel
    output logic                      s_axi_wvalid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    output logic [AXI_DATA_WIDTH/8-1:0] s_axi_wstrb,
    output logic                      s_axi_wlast,
    input  logic                      s_axi_wready,
    // Write response channel
    input  logic                      s_axi_bvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    input  logic [               1:0] s_axi_bresp,
    output logic                      s_axi_bready,
    // Read address channel
    output logic                      s_axi_arvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    output logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    output logic [               7:0] s_axi_arlen,
    output logic [               2:0] s_axi_arsize,
    output logic [               1:0] s_axi_arburst,
    input  logic                      s_axi_arready,
    // Read data channel
    input  logic                      s_axi_rvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    input  logic [               1:0] s_axi_rresp,
    input  logic                      s_axi_rlast,
    output logic                      s_axi_rready
);
```

(Note: For brevity, only two manager interfaces are shown)

### `svc_axi_axil_adapter.sv`

Converts between AXI and AXI-Lite interfaces.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width
- `AXI_ID_WIDTH`: ID width
- `OUTSTANDING_IO_WIDTH`: Log2 of max outstanding transactions

**Interface:**

```systemverilog
module svc_axi_axil_adapter #(
    parameter AXI_ADDR_WIDTH       = 8,
    parameter AXI_DATA_WIDTH       = 16,
    parameter AXI_STRB_WIDTH       = AXI_DATA_WIDTH / 8,
    parameter AXI_ID_WIDTH         = 4,
    parameter OUTSTANDING_IO_WIDTH = 1
) (
    input logic clk,
    input logic rst_n,

    // AXI subordinate interface
    input  logic                      s_axi_awvalid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_awaddr,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_awid,
    input  logic [               7:0] s_axi_awlen,
    input  logic [               2:0] s_axi_awsize,
    input  logic [               1:0] s_axi_awburst,
    output logic                      s_axi_awready,
    // Write data
    input  logic                      s_axi_wvalid,
    input  logic [AXI_DATA_WIDTH-1:0] s_axi_wdata,
    input  logic [AXI_STRB_WIDTH-1:0] s_axi_wstrb,
    input  logic                      s_axi_wlast,
    output logic                      s_axi_wready,
    // Write response
    output logic                      s_axi_bvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_bid,
    output logic [               1:0] s_axi_bresp,
    input  logic                      s_axi_bready,
    // Read address
    input  logic                      s_axi_arvalid,
    input  logic [  AXI_ID_WIDTH-1:0] s_axi_arid,
    input  logic [AXI_ADDR_WIDTH-1:0] s_axi_araddr,
    input  logic [               7:0] s_axi_arlen,
    input  logic [               2:0] s_axi_arsize,
    input  logic [               1:0] s_axi_arburst,
    output logic                      s_axi_arready,
    // Read data
    output logic                      s_axi_rvalid,
    output logic [  AXI_ID_WIDTH-1:0] s_axi_rid,
    output logic [AXI_DATA_WIDTH-1:0] s_axi_rdata,
    output logic [               1:0] s_axi_rresp,
    output logic                      s_axi_rlast,
    input  logic                      s_axi_rready,

    // AXI-Lite manager interface
    output logic [AXI_ADDR_WIDTH-1:0] m_axil_awaddr,
    output logic                      m_axil_awvalid,
    input  logic                      m_axil_awready,
    output logic [AXI_DATA_WIDTH-1:0] m_axil_wdata,
    output logic [AXI_STRB_WIDTH-1:0] m_axil_wstrb,
    output logic                      m_axil_wvalid,
    input  logic                      m_axil_wready,
    input  logic [               1:0] m_axil_bresp,
    input  logic                      m_axil_bvalid,
    output logic                      m_axil_bready,
    output logic                      m_axil_arvalid,
    output logic [AXI_ADDR_WIDTH-1:0] m_axil_araddr,
    input  logic                      m_axil_arready,
    input  logic                      m_axil_rvalid,
    input  logic [AXI_DATA_WIDTH-1:0] m_axil_rdata,
    input  logic [               1:0] m_axil_rresp,
    output logic                      m_axil_rready
);
```

### `svc_axi_burst_adapter.sv`

Adapts between different AXI burst capabilities.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width
- `AXI_ID_WIDTH`: ID width
- `BURST_FIXED_SUPPORT`: Whether to support FIXED bursts

**Interface:** Similar to `svc_axi_arbiter` with subordinate (s\_) and manager
(m\_) AXI interfaces.

### `svc_axi_stripe.sv`

Implements address striping across multiple AXI subordinates.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width
- `AXI_ID_WIDTH`: ID width
- `NUM_SUBORDINATES`: Number of subordinate interfaces
- `SHIFT`: Address shift amount for striping (log2 of stripe width)

**Interface:**

- One manager AXI interface (m_axi\_\*)
- Multiple subordinate AXI interfaces (s0_axi\_\_, s1_axi\_\_, etc.)

### `svc_axi_mem.sv`

AXI memory controller interface.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width
- `AXI_ID_WIDTH`: ID width
- `AXI_STRB_WIDTH`: Byte strobe width (AXI_DATA_WIDTH/8)
- `MEM_ADDR_WIDTH`: Memory address width

**Interface:**

- AXI subordinate interface (s_axi\_\*)
- Simple memory interface (addr, write_en, write_data, read_data)

### `svc_axi_null.sv`

AXI sink that accepts all transactions but discards data.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width
- `AXI_ID_WIDTH`: ID width

**Interface:**

- AXI subordinate interface (s_axi\_\*)
- No outputs other than handshaking signals

### `svc_axil_sram_if.sv`

AXI-Lite to SRAM interface adapter.

**Parameters:**

- `ADDR_WIDTH`: Address width
- `DATA_WIDTH`: Data width
- `STRB_WIDTH`: Byte strobe width (DATA_WIDTH/8)

**Interface:**

```systemverilog
module svc_axil_sram_if #(
    parameter ADDR_WIDTH = 12,
    parameter DATA_WIDTH = 32,
    parameter STRB_WIDTH = DATA_WIDTH / 8
) (
    input  logic                  clk,
    input  logic                  rst_n,
    // AXI-Lite subordinate interface
    input  logic                  s_axil_awvalid,
    input  logic [ADDR_WIDTH-1:0] s_axil_awaddr,
    output logic                  s_axil_awready,
    input  logic                  s_axil_wvalid,
    input  logic [DATA_WIDTH-1:0] s_axil_wdata,
    input  logic [STRB_WIDTH-1:0] s_axil_wstrb,
    output logic                  s_axil_wready,
    output logic                  s_axil_bvalid,
    output logic [1:0]            s_axil_bresp,
    input  logic                  s_axil_bready,
    input  logic                  s_axil_arvalid,
    input  logic [ADDR_WIDTH-1:0] s_axil_araddr,
    output logic                  s_axil_arready,
    output logic                  s_axil_rvalid,
    output logic [DATA_WIDTH-1:0] s_axil_rdata,
    output logic [1:0]            s_axil_rresp,
    input  logic                  s_axil_rready,
    // SRAM interface
    output logic                  sram_we,
    output logic [ADDR_WIDTH-3:0] sram_addr,
    output logic [DATA_WIDTH-1:0] sram_wdata,
    output logic [STRB_WIDTH-1:0] sram_wstrb,
    input  logic [DATA_WIDTH-1:0] sram_rdata
);
```

## VGA and Graphics Modules

### `svc_vga_mode.sv`

VGA mode settings and timing parameters.

**Interface:** Standard VGA timing parameters (h_visible, h_sync_start, etc.).

### `svc_gfx_line.sv`

Line drawing algorithm implementation.

**Parameters:**

- `H_WIDTH`: Horizontal dimension width
- `V_WIDTH`: Vertical dimension width
- `PIXEL_WIDTH`: Pixel color depth

**Interface:**

```systemverilog
module svc_gfx_line #(
    parameter H_WIDTH     = 12,
    parameter V_WIDTH     = 12,
    parameter PIXEL_WIDTH = 12
) (
    input  logic                   clk,
    input  logic                   rst_n,
    // Command interface
    input  logic                   start,
    input  logic [H_WIDTH-1:0]     x0,
    input  logic [V_WIDTH-1:0]     y0,
    input  logic [H_WIDTH-1:0]     x1,
    input  logic [V_WIDTH-1:0]     y1,
    input  logic [PIXEL_WIDTH-1:0] color,
    output logic                   done,
    // Pixel output
    output logic                   pixel_valid,
    output logic [H_WIDTH-1:0]     pixel_x,
    output logic [V_WIDTH-1:0]     pixel_y,
    output logic [PIXEL_WIDTH-1:0] pixel_color,
    input  logic                   pixel_ready
);
```

### `svc_gfx_rect_fill.sv`

Rectangle fill operation.

**Parameters:**

- `H_WIDTH`: Horizontal dimension width
- `V_WIDTH`: Vertical dimension width
- `PIXEL_WIDTH`: Pixel color depth

**Interface:**

```systemverilog
module svc_gfx_rect_fill #(
    parameter H_WIDTH     = 12,
    parameter V_WIDTH     = 12,
    parameter PIXEL_WIDTH = 12
) (
    input  logic                   clk,
    input  logic                   rst_n,
    // Command interface
    input  logic                   start,
    input  logic [H_WIDTH-1:0]     x0,
    input  logic [V_WIDTH-1:0]     y0,
    input  logic [H_WIDTH-1:0]     x1,
    input  logic [V_WIDTH-1:0]     y1,
    input  logic [PIXEL_WIDTH-1:0] color,
    output logic                   done,
    // Pixel output
    output logic                   pixel_valid,
    output logic [H_WIDTH-1:0]     pixel_x,
    output logic [V_WIDTH-1:0]     pixel_y,
    output logic [PIXEL_WIDTH-1:0] pixel_color,
    input  logic                   pixel_ready
);
```

### `svc_gfx_fb.sv`

Framebuffer implementation for graphics.

**Parameters:**

- `H_WIDTH`: Horizontal dimension width
- `V_WIDTH`: Vertical dimension width
- `PIXEL_WIDTH`: Pixel color depth
- AXI interface parameters

**Interface:**

- Pixel input interface (s_gfx_valid, s_gfx_x, s_gfx_y, s_gfx_pixel)
- AXI manager interface for memory access (m_axi\_\*)
- VGA timing parameters (h_visible, v_visible)

### `svc_gfx_vga.sv`

Top-level VGA graphics controller.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width
- `AXI_ID_WIDTH`: ID width
- `COLOR_WIDTH`: Color component width
- `H_WIDTH`: Horizontal dimension width
- `V_WIDTH`: Vertical dimension width
- `PIXEL_WIDTH`: Pixel color depth

**Interface:**

```systemverilog
module svc_gfx_vga #(
    parameter AXI_ADDR_WIDTH = 12,
    parameter AXI_DATA_WIDTH = 16,
    parameter AXI_ID_WIDTH   = 4,
    parameter AXI_STRB_WIDTH = AXI_DATA_WIDTH / 8,
    parameter COLOR_WIDTH    = 4,
    parameter H_WIDTH        = 12,
    parameter V_WIDTH        = 12,
    parameter PIXEL_WIDTH    = 12
) (
    input logic clk,
    input logic rst_n,
    input logic pixel_clk,
    input logic pixel_rst_n,

    // Graphics input interface
    input  logic                   s_gfx_valid,
    input  logic [H_WIDTH-1:0]     s_gfx_x,
    input  logic [V_WIDTH-1:0]     s_gfx_y,
    input  logic [PIXEL_WIDTH-1:0] s_gfx_pixel,
    output logic                   s_gfx_ready,

    // Control signals
    input logic fb_start,  // Start framebuffer operation

    // AXI memory interface
    // Complete AXI manager interface (m_axi_*)

    // VGA timing parameters
    input logic [H_WIDTH-1:0] h_visible,
    input logic [H_WIDTH-1:0] h_sync_start,
    input logic [H_WIDTH-1:0] h_sync_end,
    input logic [H_WIDTH-1:0] h_line_end,
    input logic [V_WIDTH-1:0] v_visible,
    input logic [V_WIDTH-1:0] v_sync_start,
    input logic [V_WIDTH-1:0] v_sync_end,
    input logic [V_WIDTH-1:0] v_frame_end,

    // VGA output
    output logic [COLOR_WIDTH-1:0] vga_red,
    output logic [COLOR_WIDTH-1:0] vga_grn,
    output logic [COLOR_WIDTH-1:0] vga_blu,
    output logic                   vga_hsync,
    output logic                   vga_vsync,
    output logic                   vga_error
);
```

### `svc_gfx_vga_fade.sv`

VGA fading effect implementation.

**Parameters:**

- Color and dimension parameters similar to svc_gfx_vga

**Interface:**

- VGA input and output interfaces
- Fade control signals

## ICE40 FPGA Specific Modules

### `svc_ice40_pll_25.sv`

25MHz PLL configuration for iCE40 FPGAs.

**Interface:**

```systemverilog
module svc_ice40_pll_25 (
    input  logic clk_in,
    output logic clk_out,
    output logic locked
);
```

### `svc_ice40_vga_pll.sv`

PLL configuration for VGA on iCE40.

**Interface:**

```systemverilog
module svc_ice40_vga_pll (
    input  logic clk_in,
    output logic clk_out,
    output logic locked
);
```

### `svc_ice40_sram_io_if.sv`

Interface to external SRAM for iCE40 FPGAs.

**Parameters:**

- `ADDR_WIDTH`: Address width
- `DATA_WIDTH`: Data width

**Interface:**

```systemverilog
module svc_ice40_sram_io_if #(
    parameter ADDR_WIDTH = 18,
    parameter DATA_WIDTH = 16
) (
    input  logic                  clk,
    input  logic                  rst_n,
    // Memory controller interface
    input  logic                  we,
    input  logic [ADDR_WIDTH-1:0] addr,
    input  logic [DATA_WIDTH-1:0] wdata,
    output logic [DATA_WIDTH-1:0] rdata,
    // SRAM physical interface
    output logic                  sram_ce_n,
    output logic                  sram_oe_n,
    output logic                  sram_we_n,
    output logic [ADDR_WIDTH-1:0] sram_addr,
    inout  logic [DATA_WIDTH-1:0] sram_data
);
```

### `svc_ice40_axil_sram.sv`

AXI-Lite to on-chip SRAM adapter for iCE40 FPGAs.

**Parameters:**

- `AXI_ADDR_WIDTH`: Address width
- `AXI_DATA_WIDTH`: Data width

**Interface:**

- AXI-Lite subordinate interface
- Internal SRAM control signals

## Common Design Patterns

### Clock and Reset Pattern

```systemverilog
always_ff @(posedge clk) begin
    if (!rst_n) begin
        // Reset state
        counter <= '0;
        state   <= STATE_IDLE;
    end else begin
        // Normal operation
        counter <= counter_next;
        state   <= state_next;
    end
end
```

### Valid-Ready Handshaking

```systemverilog
// Combinational logic
always_comb begin
    out_valid = data_available && !output_blocked;
    in_ready  = !fifo_full && !output_blocked;
end

// Transfer data on handshake
always_ff @(posedge clk) begin
    if (out_valid && out_ready) begin
        // Process data transfer
    end
end
```

### State Machine Pattern

```systemverilog
typedef enum logic [1:0] {
    STATE_IDLE,
    STATE_BUSY,
    STATE_DONE
} state_t;

state_t state, state_next;

// Next state logic
always_comb begin
    state_next = state;

    case (state)
        STATE_IDLE: if (start) state_next = STATE_BUSY;
        STATE_BUSY: if (done)  state_next = STATE_DONE;
        STATE_DONE:            state_next = STATE_IDLE;
    endcase
end

// State update
always_ff @(posedge clk) begin
    if (!rst_n) begin
        state <= STATE_IDLE;
    end else begin
        state <= state_next;
    end
end
```

## Module Integration Examples

### AXI Memory System

```systemverilog
svc_axi_arbiter #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .AXI_ID_WIDTH(4),
    .NUM_MANAGERS(2)
) axi_arbiter_inst (
    .clk(clk),
    .rst_n(rst_n),
    // Connect manager 0
    .m0_axi_awvalid(cpu_axi_awvalid),
    .m0_axi_awaddr(cpu_axi_awaddr),
    // ...other signals...

    // Connect manager 1
    .m1_axi_awvalid(dma_axi_awvalid),
    .m1_axi_awaddr(dma_axi_awaddr),
    // ...other signals...

    // Connect to subordinate
    .s_axi_awvalid(mem_axi_awvalid),
    .s_axi_awaddr(mem_axi_awaddr),
    // ...other signals...
);

svc_axi_mem #(
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .AXI_ID_WIDTH(4),
    .MEM_ADDR_WIDTH(20)
) axi_mem_inst (
    .clk(clk),
    .rst_n(rst_n),
    // Connect AXI interface
    .s_axi_awvalid(mem_axi_awvalid),
    .s_axi_awaddr(mem_axi_awaddr),
    // ...other signals...

    // Connect to memory
    .mem_addr(sram_addr),
    .mem_we(sram_we),
    .mem_wdata(sram_wdata),
    .mem_rdata(sram_rdata)
);
```

### Graphics Pipeline

```systemverilog
// Line drawing to framebuffer pipeline
svc_gfx_line #(
    .H_WIDTH(12),
    .V_WIDTH(12),
    .PIXEL_WIDTH(12)
) gfx_line_inst (
    .clk(clk),
    .rst_n(rst_n),
    // Command interface
    .start(line_start),
    .x0(line_x0),
    .y0(line_y0),
    .x1(line_x1),
    .y1(line_y1),
    .color(line_color),
    .done(line_done),
    // Pixel output to framebuffer
    .pixel_valid(line_pixel_valid),
    .pixel_x(line_pixel_x),
    .pixel_y(line_pixel_y),
    .pixel_color(line_pixel_color),
    .pixel_ready(fb_pixel_ready)
);

svc_gfx_fb #(
    .H_WIDTH(12),
    .V_WIDTH(12),
    .PIXEL_WIDTH(12),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .AXI_ID_WIDTH(4)
) gfx_fb_inst (
    .clk(clk),
    .rst_n(rst_n),
    // Pixel input from graphics primitives
    .s_gfx_valid(line_pixel_valid),
    .s_gfx_x(line_pixel_x),
    .s_gfx_y(line_pixel_y),
    .s_gfx_pixel(line_pixel_color),
    .s_gfx_ready(fb_pixel_ready),
    // AXI interface to memory
    // ...AXI signals...
);
```

## Testing and Verification

- Unit tests are in the `tb/` directory (e.g., `tb/svc_module_tb.sv`)
- Formal verification files are in `tb/formal/` (e.g.,
  `tb/formal/svc_module.sby`)

To run tests:

- `make <module_name>_tb`: Run a specific testbench
- `make <module_name>_f`: Run formal verification for a module
- `make tb`: Run all testbenches
- `make formal`: Run all formal verification
- `make lint`: Lint all code with Verilator
- `make format`: Format all code to match style guidelines
