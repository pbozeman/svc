# Section 1.3 Detailed Plan: Surgical Reverts

## Current State Summary

After 1.2 revert to 411b5585:

| Component                   | Current State                    | Needs Work? |
| --------------------------- | -------------------------------- | ----------- |
| `svc_rv_stage_mem`          | Has MEM_TYPE, unified ren/rvalid | Done        |
| `svc_rv_stage_if`           | FIFO-based, unified interface    | **Yes**     |
| `svc_rv_stage_if_bram/sram` | Deleted (7f0c174e)               | Optional    |
| `svc_rv_bpred_if`           | Deleted (7f0c174e)               | Optional    |

## Decision Point: Scope of IF Revert

**Option A**: Remove FIFOs only (undo eb88e9dd)

- Keep unified IF stage
- Simpler change, smaller diff
- IF stage remains MEM_TYPE-agnostic (SOC presents same interface)

**Option B**: Full revert to pre-7f0c174e (undo 7f0c174e + eb88e9dd)

- Restore `svc_rv_stage_if_bram.sv` and `svc_rv_stage_if_sram.sv`
- Restore `svc_rv_bpred_if.sv`
- Add MEM_TYPE parameter to IF stage
- Larger change but cleaner separation of concerns

### Recommendation

Start with **Option A**. The MEM_TYPE parameter in IF stage was primarily needed
because BRAM and SRAM had different timing requirements. With the current
architecture:

- SOC already adapts SRAM to BRAM-like timing (1-cycle latency via registered
  hold)
- `imem_rvalid` signal tells IF stage when data is ready
- Unified interface is simpler to maintain

If Option A proves insufficient (e.g., CPI regression for SRAM), then proceed to
Option B.

---

## Option A: Remove FIFOs from IF Stage

### Step 1: Understand the Pre-FIFO Interface

The pre-FIFO IF stage (before eb88e9dd) had:

```systemverilog
// Ready signal to PC stage
// Backpressure from downstream: accept new PC when ID stage can accept.
assign s_ready = m_ready;
```

Key difference: No FIFOs, direct passthrough with pipeline registers.

### Step 2: Create New Branch

```bash
git checkout -b if-remove-fifo
```

### Step 3: Restore Pre-FIFO IF Stage

Get the pre-FIFO version and apply renames:

```bash
# Get the file before FIFO addition
git show eb88e9dd^:rtl/rv/svc_rv_stage_if.sv > /tmp/if_prefifo.sv

# The file needs signal renames applied (a631022, 8ecaf69):
# - btb_target -> btb_tgt
# - ras_target -> ras_tgt
# - pc_redirect_target -> pc_redir_tgt
# - etc.
```

#### 3a. Extract Pre-FIFO Logic

From the pre-FIFO version, the key sections are:

1. **Module ports** - Same as current, no FIFO-related signals
2. **s_ready assignment** - `assign s_ready = m_ready;`
3. **imem interface** - Same patterns (BPRED vs non-BPRED addressing)
4. **Pipeline registers** - Standard IF/ID registers without FIFO indirection
5. **m_valid generation** - Based on `imem_rvalid` not FIFO state

#### 3b. Key Changes to Make

1. Remove `svc_sync_fifo` include and instantiations
2. Remove FIFO control logic (`fifo_clr`, `pc_fifo_*`, `instr_fifo_*`, etc.)
3. Remove stale response discard logic (unnecessary without FIFOs)
4. Simplify `s_ready = m_ready`
5. Restore direct pipeline register logic for PC, instruction, metadata

#### 3c. Handle Pipelined vs Single-Cycle

Pre-FIFO logic for pipelined mode:

```systemverilog
if (PIPELINED != 0) begin : g_pipelined
  // Pipeline registers for PC, BTB metadata, etc.
  always_ff @(posedge clk) begin
    if (!rst_n) begin
      // Reset state
    end else if (m_ready) begin
      // Capture on handshake
    end
  end

  // m_valid from imem_rvalid with flush handling
  assign m_valid = imem_rvalid && !flush_extend;
end
```

### Step 4: Update Formal Verification

The current formal section has FIFO-specific assertions. Simplify to:

1. Keep valid/ready handshake assertions
2. Remove shadow queue tracking (no longer needed)
3. Keep `imem_rvalid` latency assumptions
4. Simplify cover properties

### Step 5: Test Incrementally

```bash
# Lint first
make lint

# Run IF formal (should be quick)
make svc_rv_stage_if_f

# Run one BRAM testbench
make svc_rv_soc_bram_tb

# Run one SRAM testbench
make svc_rv_soc_sram_tb

# Run full suite
make tb
```

### Step 6: Run riscv-formal

```bash
# This is the critical correctness check
make formal  # or just the rv formal targets
```

### Step 7: Check CPI Benchmarks

Compare CPI before/after for:

- BRAM pipelined
- SRAM pipelined
- SRAM single-cycle

---

## Option B: Full Revert to Pre-7f0c174e (If Needed)

Only proceed here if Option A shows problems.

### Step 1: Restore Deleted Files

```bash
git checkout 7f0c174e^ -- rtl/rv/svc_rv_stage_if_bram.sv
git checkout 7f0c174e^ -- rtl/rv/svc_rv_stage_if_sram.sv
git checkout 7f0c174e^ -- rtl/rv/svc_rv_bpred_if.sv
```

### Step 2: Restore Wrapper IF Stage

```bash
git checkout 7f0c174e^ -- rtl/rv/svc_rv_stage_if.sv
```

### Step 3: Apply Signal Renames

Apply the renames from a631022 and 8ecaf69:

- `btb_target` → `btb_tgt`
- `ras_target` → `ras_tgt`
- `pc_redirect_target` → `pc_redir_tgt`
- `load_*` → `ld_*`

### Step 4: Update svc_rv.sv

Add MEM_TYPE parameter to IF stage instantiation.

### Step 5: Update SOCs

Ensure BRAM and SRAM SOCs pass correct MEM_TYPE to core.

### Step 6: Test

Same testing sequence as Option A.

---

## Checklist

- [ ] Create branch `if-remove-fifo`
- [ ] Remove FIFO logic from `svc_rv_stage_if.sv`
- [ ] Update formal verification
- [ ] `make format`
- [ ] `make lint`
- [ ] `make svc_rv_stage_if_f`
- [ ] `make svc_rv_soc_bram_tb`
- [ ] `make svc_rv_soc_sram_tb`
- [ ] `make tb`
- [ ] `make formal`
- [ ] CPI benchmark comparison
- [ ] If issues, proceed to Option B
