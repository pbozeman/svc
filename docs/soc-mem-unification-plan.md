# SoC Memory Interface Unification Plan

This document outlines a phased approach to unify the BRAM and SRAM memory
interfaces, enabling variable-latency instruction fetch and paving the way for
an instruction cache.

## Problem Statement

Currently, the RISC-V implementation has two parallel paths for instruction
fetch:

- `svc_rv_stage_if_bram.sv`: Handles 1-cycle BRAM latency with explicit PC/BTB
  buffering
- `svc_rv_stage_if_sram.sv`: Handles 0-cycle SRAM latency with passthrough

The memory type is a compile-time parameter (`MEM_TYPE`) that selects between
these implementations via generate blocks. This approach:

1. Duplicates logic between the two implementations
2. Cannot handle variable latency (e.g., cache hit vs. miss)
3. Requires changes in multiple places to add new memory types

## Goal

Introduce an AXI-like interface with explicit request/response signaling:

- **Request (AR channel):** `imem_arvalid`, `imem_araddr`
- **Response (R channel):** `imem_rvalid`, `imem_rdata`

This allows:

1. Unified IF stage logic that waits for valid response
2. Memory-type-agnostic CPU design
3. Foundation for icache with variable hit/miss latency
4. Easy extension to full AXI (add `arready`/`rready`) if needed

## Architecture Overview

### Current Interface

```
svc_rv                          SoC
┌────────────┐               ┌─────────────┐
│            │──imem_ren────>│             │
│   stage_if │──imem_raddr──>│  BRAM/SRAM  │
│            │<──imem_rdata──│             │
└────────────┘               └─────────────┘
     │
     │ (MEM_TYPE selects bram vs sram impl)
     ▼
┌────────────────┐  OR  ┌────────────────┐
│ stage_if_bram  │      │ stage_if_sram  │
│ (1-cycle buf)  │      │ (passthrough)  │
└────────────────┘      └────────────────┘
```

### Target Interface

```
svc_rv                              SoC
┌────────────┐                   ┌─────────────┐
│            │──imem_arvalid────>│             │
│   stage_if │──imem_araddr─────>│  Memory     │
│  (unified) │<──imem_rdata──────│  Subsystem  │
│            │<──imem_rvalid─────│             │
└────────────┘                   └─────────────┘
                                       │
                          ┌────────────┴────────────┐
                          ▼                         ▼
                    ┌──────────┐              ┌──────────┐
                    │   BRAM   │              │  ICache  │
                    │(1 cycle) │              │(variable)│
                    └──────────┘              └──────────┘
```

## Implementation Phases

### Phase 0: Rename to AXI-like Interface

**Goal:** Rename existing signals to AXI-like naming before adding new
functionality.

**Signal mapping:**

| Current      | New            | Description             |
| ------------ | -------------- | ----------------------- |
| `imem_ren`   | `imem_arvalid` | Address request valid   |
| `imem_raddr` | `imem_araddr`  | Address request address |
| `imem_rdata` | `imem_rdata`   | Read response data      |
| (new)        | `imem_rvalid`  | Read response valid     |

**Files to modify:**

- `rtl/rv/svc_rv.sv`: Rename ports
- `rtl/rv/svc_rv_stage_if.sv`: Rename signals
- `rtl/rv/svc_rv_stage_if_bram.sv`: Rename signals
- `rtl/rv/svc_rv_stage_if_sram.sv`: Rename signals
- `rtl/rv/svc_rv_soc_bram.sv`: Rename signals
- `rtl/rv/svc_rv_soc_sram.sv`: Rename signals

**Behavior:** Pure rename, no functional change. All tests must pass.

**Verification:**

- All existing testbenches pass
- All formal verification passes

### Phase 1: Add imem_rvalid to Interface

**Files to modify:**

- `rtl/rv/svc_rv.sv`: Add `imem_rvalid` input port
- `rtl/rv/svc_rv_stage_if.sv`: Pass through to child modules
- `rtl/rv/svc_rv_stage_if_bram.sv`: Accept but initially ignore (use existing
  timing)
- `rtl/rv/svc_rv_stage_if_sram.sv`: Accept but initially ignore (use existing
  timing)
- `rtl/rv/svc_rv_soc_bram.sv`: Generate `imem_rvalid` (registered
  `imem_arvalid`)
- `rtl/rv/svc_rv_soc_sram.sv`: Generate `imem_rvalid` (combinational,
  `= imem_arvalid`)

**Behavior:** No functional change. Signal is added but not yet consumed.
Existing tests must pass.

**Verification:**

- All existing testbenches pass
- All formal verification passes

### Phase 2: Consume imem_rvalid in stage_if_bram

**Goal:** Replace implicit 1-cycle latency assumption with explicit valid
signal.

**Changes to `svc_rv_stage_if_bram.sv`:**

- Use `imem_rvalid` to gate instruction capture instead of `started` flag
- Simplify validity tracking: `valid_buf = imem_rvalid && !flush`
- PC/BTB buffering remains the same (still need to align with response)

**Key insight:** The buffering logic stays, but the "when is data ready" check
becomes explicit rather than implicit cycle counting.

```systemverilog
// Before: implicit timing
always_ff @(posedge clk) begin
  if (m_ready) begin
    started   <= 1'b1;
    valid_buf <= started && !if_id_flush && !flush_extend;
  end
end

// After: explicit valid signal
always_ff @(posedge clk) begin
  if (m_ready) begin
    valid_buf <= imem_rvalid && !if_id_flush && !flush_extend;
  end
end
```

**Verification:**

- BRAM testbenches pass
- BRAM formal verification passes
- SRAM tests unaffected (still using old logic)

### Phase 3: Consume imem_rvalid in stage_if_sram

**Goal:** Align SRAM implementation with the same valid-based protocol.

**Changes to `svc_rv_stage_if_sram.sv`:**

- Pipelined mode: use `imem_rvalid` instead of hardcoded `1'b1`
- Non-pipelined mode: passthrough `imem_rvalid` as `valid_to_if_id`

```systemverilog
// Before (pipelined)
valid_buf <= 1'b1;

// After (pipelined)
valid_buf <= imem_rvalid && !if_id_flush;

// Before (non-pipelined)
assign valid_to_if_id = rst_n;

// After (non-pipelined)
assign valid_to_if_id = imem_rvalid;
```

**Verification:**

- All SRAM testbenches pass
- All BRAM testbenches still pass

### Phase 4: Unify stage_if_bram and stage_if_sram

**Goal:** Single implementation that handles any latency via `imem_rvalid`.

**Approach:**

The key difference between BRAM and SRAM is buffering:

- BRAM: Buffer PC, BTB, RAS for 1 cycle to align with instruction
- SRAM: No buffering needed

With `imem_rvalid`, we can handle this uniformly:

1. When `imem_arvalid` is asserted, capture PC/BTB/RAS into a "pending" buffer
2. When `imem_rvalid` arrives, transfer pending buffer to output
3. For 0-cycle latency, this collapses to passthrough (same cycle)
4. For 1-cycle latency, this provides the needed buffering

**New unified module: `svc_rv_stage_if_fetch.sv`**

```systemverilog
// Capture request metadata when fetch is issued
always_ff @(posedge clk) begin
  if (imem_arvalid && !pc_stall) begin
    pending_pc       <= imem_araddr;
    pending_btb_hit  <= btb_hit_if;
    // ... other metadata
  end
end

// Output when response arrives
always_ff @(posedge clk) begin
  if (m_ready) begin
    if (imem_rvalid) begin
      pc_buf       <= pending_pc;
      btb_hit_buf  <= pending_btb_hit;
      instr_buf    <= imem_rdata;
      valid_buf    <= !if_id_flush;
    end else begin
      valid_buf    <= 1'b0;
    end
  end
end
```

**Files to modify:**

- Create `rtl/rv/svc_rv_stage_if_fetch.sv`
- Modify `rtl/rv/svc_rv_stage_if.sv`: Remove generate block, instantiate unified
  module
- Delete `rtl/rv/svc_rv_stage_if_bram.sv`
- Delete `rtl/rv/svc_rv_stage_if_sram.sv`

**Verification:**

- All BRAM and SRAM testbenches pass with unified implementation
- Performance metrics unchanged

### Phase 5: Remove MEM_TYPE from CPU

**Goal:** CPU becomes memory-type-agnostic.

**Changes:**

- Remove `MEM_TYPE` parameter from `svc_rv.sv` and `svc_rv_stage_if.sv`
- Remove `MEM_TYPE_BRAM`/`MEM_TYPE_SRAM` from `svc_rv_defs.svh` (if no longer
  used)
- SoCs still know their memory type (for generating correct `imem_rvalid`)

**Note:** The `PIPELINED` parameter remains - it controls whether IF/ID has
pipeline registers, independent of memory type.

### Phase 6: Add Stall Support for Variable Latency

**Goal:** Handle cases where `imem_rvalid` doesn't arrive for multiple cycles.

**Changes:**

- When `imem_arvalid` is asserted but `imem_rvalid` is low, stall PC advancement
- Propagate stall through hazard unit
- Handle in-flight requests during flush (cancel or wait)

**New signal flow:**

```
imem_arvalid ────────────────────────────────>│ Memory │
                                              │Subsystem│
imem_rvalid <─────────────────────────────────│        │
        │
        ▼
   ┌─────────┐
   │ Hazard  │──> pc_stall (when waiting for rvalid)
   │  Unit   │
   └─────────┘
```

**Verification:**

- Create testbench with variable-latency memory model
- Verify correct behavior with 0, 1, 2+ cycle latencies
- Verify flush during outstanding request

### Phase 7: Instruction Cache Integration

**Goal:** Add icache between CPU and memory.

With phases 0-6 complete, adding an icache becomes straightforward:

```
svc_rv                    ICache               Memory
┌────────┐             ┌─────────┐          ┌────────┐
│        │─arvalid────>│         │─arvalid─>│        │
│        │─araddr─────>│         │─araddr──>│        │
│ CPU    │<──rdata─────│ ICache  │<──rdata──│  BRAM  │
│        │<──rvalid────│         │<──rvalid─│        │
└────────┘             └─────────┘          └────────┘
```

The icache:

- Returns `rvalid` immediately on hit (0 or 1 cycle)
- Stalls on miss until refill completes (N cycles)
- CPU sees variable latency, handles it uniformly via `imem_rvalid`

## Interface Summary

### Current svc_rv Instruction Interface

```systemverilog
output logic        imem_ren,
output logic [31:0] imem_raddr,
input  logic [31:0] imem_rdata,
```

### After Phase 0 (Rename)

```systemverilog
output logic        imem_arvalid,
output logic [31:0] imem_araddr,
input  logic [31:0] imem_rdata,
```

### After Phase 1 (Add rvalid)

```systemverilog
output logic        imem_arvalid,
output logic [31:0] imem_araddr,
input  logic [31:0] imem_rdata,
input  logic        imem_rvalid,
```

### Memory Response Timing

| Memory Type   | Latency  | imem_rvalid Timing               |
| ------------- | -------- | -------------------------------- |
| SRAM          | 0 cycles | `= imem_arvalid` (same cycle)    |
| BRAM          | 1 cycle  | `= imem_arvalid_p1` (registered) |
| ICache (hit)  | 0-1      | Depends on cache design          |
| ICache (miss) | N cycles | After refill completes           |

## Risk Mitigation

### Backward Compatibility

- Each phase maintains existing behavior
- Tests must pass after each phase
- Can stop at any phase if issues arise

### Performance Validation

After Phase 4 (unification):

- SRAM single-cycle CPI should remain ~1.0
- BRAM pipelined CPI should be unchanged
- No additional pipeline bubbles introduced

### Rollback Points

- Phase 0: Pure rename - easy to revert
- Phase 1-3: Signal added but behavior unchanged - easy rollback
- Phase 4: Major change - keep old files until verification complete
- Phase 5+: Committed to new architecture

## Open Questions

1. **BPRED interaction:** The current BRAM+BPRED uses `pc_next` for early fetch.
   Does this still work with `imem_rvalid`? (Answer: Yes, the valid signal just
   confirms when the speculatively-fetched instruction arrives)

2. **Flush timing:** When a flush occurs with an outstanding fetch, should we:

   - Wait for rvalid and discard? (simpler)
   - Cancel the request? (requires cancel signal to memory)

3. **Data memory:** Should `dmem` also get AXI-like naming? (Future work, needed
   for dcache)

## Success Criteria

1. All existing testbenches pass after each phase
2. Unified stage_if implementation (Phase 4)
3. Variable-latency support verified (Phase 6)
4. No performance regression for existing configurations
