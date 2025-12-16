# Plan: Integrate svc_cache_axi for RISC-V SoC dmem

## Overview

Add data cache to RISC-V SoC using `svc_cache_axi`. Create new SoC variants with
CPU stall support on cache misses.

**Phase 1** (this plan):

- `svc_rv_soc_bram_cache` - BRAM-based, fully pipelined

**Phase 2** (follow-up):

- `svc_rv_soc_sram_cache` - SRAM-based, smaller footprint for synthesis attempt

**Note**: Do dmem first. imem (i$) requires remote program load capability
before it can use external memory - future work.

## Architecture

```
svc_rv (CPU)                    svc_rv_dmem_cache_if              svc_cache_axi
+-------------+                 +-------------------+             +-------------+
| dmem_ren    |---------------->| rd_valid          |------------>|             |
| dmem_raddr  |---------------->| rd_addr           |------------>|   D-Cache   |
| dmem_rdata  |<----------------| rd_data           |<------------|             |
|             |                 | rd_data_valid     |<------------|             |
| dmem_we     |---------------->| wr_valid          |------------>|             |
| dmem_waddr  |---------------->| wr_addr           |------------>|             |---> AXI
| dmem_wdata  |---------------->| wr_data           |------------>|             |
| dmem_wstrb  |---------------->| wr_strb           |------------>|             |
|             |                 |                   |             +-------------+
| dmem_stall  |<----------------| dmem_stall (NEW)  |
+-------------+                 +-------------------+
```

## Files to Modify

### 1. rtl/rv/svc_rv.sv

Add `dmem_stall` input to stall CPU on cache miss.

**Line 84** - Add after dmem_wstrb port:

```systemverilog
input logic dmem_stall,
```

**Line 424** - Modify stall_cpu:

```systemverilog
// Before:
assign stall_cpu = halt;

// After:
assign stall_cpu = halt || dmem_stall;
```

## Files to Create

### 2. rtl/rv/svc_rv_dmem_cache_if.sv

Bridge module: converts CPU dmem signals to cache valid/ready protocol.

**Responsibilities:**

- Convert `dmem_ren` pulse to `rd_valid` (hold until `rd_ready`)
- Convert `dmem_we` pulse to `wr_valid` (hold until `wr_ready`)
- Generate `dmem_stall` when cache not ready or data pending
- Handle I/O bypass (bit 31 = 1 bypasses cache)
- Register address/data for cache (CPU may change next cycle)

**Key Logic:**

```systemverilog
// Stall when:
// 1. Read pending and data not yet valid (cache miss)
// 2. Write pending and cache not ready
assign dmem_stall = (rd_pending && !cache_rd_data_valid) ||
                    (wr_pending && !cache_wr_ready);
```

**I/O Bypass:**

- Addresses with bit 31 = 1 go directly to I/O (no cache)
- I/O has BRAM timing (1-cycle), no stall needed

### 3. rtl/rv/svc_rv_soc_bram_cache.sv

New SoC variant based on `svc_rv_soc_bram.sv`.

**Parameters (new):**

```systemverilog
parameter int CACHE_SIZE_BYTES = 4096,
parameter int CACHE_LINE_BYTES = 32,
parameter bit CACHE_TWO_WAY    = 0,
parameter int AXI_ADDR_WIDTH   = 32,
parameter int AXI_DATA_WIDTH   = 128,
parameter int AXI_ID_WIDTH     = 4,
```

**Structure:**

- `svc_rv` CPU with new `dmem_stall` input
- `svc_mem_bram` for imem (unchanged)
- `svc_rv_dmem_cache_if` bridge
- `svc_cache_axi` D-cache
- AXI manager interface exposed at top level

**Ports (new):**

```systemverilog
// AXI manager interface for external data memory
output logic                      m_axi_arvalid,
output logic [AXI_ADDR_WIDTH-1:0] m_axi_araddr,
// ... full AXI4 read/write channels
```

### 4. tb/rv/svc_rv_soc_bram_cache_tb.sv

Testbench using `svc_axi_sram` as AXI backing store.

**Test cases:**

- Reset test
- Cache hit/miss behavior
- Write-through verification
- I/O bypass
- Existing RV test programs (fibonacci, etc.)

## Implementation Order

1. **svc_rv.sv**: Add `dmem_stall` input (minimal change)
2. **svc_rv_dmem_cache_if.sv**: Create bridge module
3. **svc_rv_soc_bram_cache.sv**: Create new SoC
4. **Testbench**: Verify functionality

## Key Design Decisions

1. **Global stall via `stall_cpu`**: Simplest integration - cache miss stalls
   entire pipeline. Existing stall propagation handles all stages correctly.

2. **I/O bypass**: Addresses with bit 31 = 1 bypass cache completely, matching
   existing SoC behavior. I/O has fixed 1-cycle BRAM timing.

3. **Write-through policy**: `svc_cache_axi` uses write-through,
   no-write-allocate. Writes go to both cache (if hit) and memory. No dirty bits
   needed.

4. **Address registration**: Bridge registers CPU address/data since CPU may
   change them while cache handles miss.

## Expected Behavior

- **Cache hit**: ~1-2 cycle latency (similar to BRAM)
- **Cache miss**: Multiple cycles for AXI burst (line fill)
- **Writes**: Stall until write acknowledged by cache
- **I/O**: No change from existing behavior (1-cycle BRAM timing)

## Testing Strategy

1. Unit test `svc_rv_dmem_cache_if` in isolation
2. Integration test with `svc_axi_sram` as backing memory
3. Run existing RV test programs (expect higher CPI due to cold cache)
4. Verify I/O bypass works correctly
