# Phase 3 Detailed Plan: Convert Backpressure to Stalls

## Strategy: Work Backwards

Remove `m_ready` dependencies stage-by-stage, starting from WB and working
backwards. Each stage change is isolated and testable - when stage N sets
`s_ready = 1`, stage N-1's `m_ready` becomes constant, enabling the next
simplification.

## Stage Order

1. **WB** (simplest - end of pipeline)
2. **MEM** (has redirect skid buffer - key complexity)
3. **EX** (has multi-cycle state machine)
4. **ID** (has data_hazard_id interaction)
5. **PC/IF** (already mostly done)

---

## Step 1: WB Stage

**Files**: `rtl/rv/svc_rv_stage_wb.sv`, `rtl/rv/svc_rv.sv`

### 1a. Remove m_ready from WB stage

**Current** (svc_rv_stage_wb.sv line 187):

```systemverilog
assign s_ready = !m_valid || m_ready;
```

**Change to**:

```systemverilog
assign s_ready = 1'b1;
```

Also remove `m_ready` from the module port list entirely.

### 1b. Convert halt to stall source

**Current** (svc_rv.sv):

```systemverilog
// line 427
assign stall_cpu = 1'b0;

// line 731
assign wb_m_ready = !halt;
```

**Change to**:

```systemverilog
// Halt now contributes to global stall instead of backpressure
assign stall_cpu = halt;

// Remove wb_m_ready entirely (no longer needed)
```

### 1c. Update WB instantiation

Remove `.m_ready(wb_m_ready)` from WB stage instantiation in svc_rv.sv.

**Rationale**: WB is the end of the pipeline. Halt should freeze the entire
pipeline via global stall, not backpressure. This is the first step in
converting backpressure to stalls.

**Test**:

```bash
make format && make lint && make svc_rv_soc_bram_tb && make svc_rv_soc_sram_tb
```

---

## Step 2: MEM Stage

**File**: `rtl/rv/svc_rv_stage_mem.sv`

### 2a. Simplify s_ready

**Current** (line 505):

```systemverilog
assign s_ready = !m_valid || m_ready;
```

**Change to**:

```systemverilog
assign s_ready = 1'b1;
```

### 2b. Redirect Skid Buffer (lines 324-359)

**Current purpose**: Latches redirect when pipeline is stalled by multi-cycle op
on wrong path (e.g., DIVU after mispredicted branch).

**Decision**: Keep the redirect skid buffer. It handles a real case
(misprediction detected while multi-cycle op is active). The skid buffer doesn't
use m_ready - it uses `redir_ready_mem` which is a separate interface.

**Test**:

```bash
make format && make lint && make svc_rv_soc_bram_tb && make svc_rv_soc_sram_tb
```

---

## Step 3: EX Stage

**File**: `rtl/rv/svc_rv_stage_ex.sv`

### 3a. Simplify s_ready

EX has two generate blocks (lines 544-562):

**Pipelined (g_registered)**:

```systemverilog
// Current (lines 548-549):
assign ex_mem_en = !m_valid || m_ready;
assign s_ready   = ex_mem_en && !op_active_ex;

// Change to:
assign s_ready = !op_active_ex;
```

**Single-cycle (g_passthrough)**:

```systemverilog
// Current (line 558):
assign s_ready = m_ready && !op_active_ex;

// Change to:
assign s_ready = !op_active_ex;
```

**Rationale**: `m_ready` is now always 1 (from MEM's s_ready=1). Both paths
simplify to `s_ready = !op_active_ex`.

### 3b. Multi-cycle State Machine

**Current**: EX has state machine (EX_IDLE, EX_MC_EXEC, EX_MC_DONE) that
generates `op_active_ex` and checks `m_valid && m_ready` for handshakes.

**Decision**: Keep `op_active_ex` gating `s_ready` locally. This is equivalent
to a local stall. Converting to global stall (`div_stall_ex` → `cpu_stall`) can
be done later.

**Simplify state machine m_ready checks** (line 203, 227):

With m_ready=1, `!m_valid || m_ready` is always true, so these conditions
simplify.

**Test**:

```bash
make format && make lint && make svc_rv_soc_bram_tb && make svc_rv_soc_sram_tb
# Also test M-extension variants for multi-cycle ops:
make svc_rv_soc_bram_m_tb && make svc_rv_soc_bram_zmmul_tb
```

---

## Step 4: ID Stage

**File**: `rtl/rv/svc_rv_stage_id.sv`

### 4a. Simplify s_ready

**Current** (line 291):

```systemverilog
assign s_ready = m_ready && !data_hazard_id;
```

**Change to**:

```systemverilog
assign s_ready = !data_hazard_id;
```

**Rationale**: `m_ready` is now always 1 (from EX's simplified s_ready). Data
hazard still gates s_ready - this is correct, as data hazards need to stall
fetch of new instructions.

### 4b. Data Hazard Handling

**Decision**: Keep data_hazard_id gating s_ready. This is effectively a local
stall for the IF→ID boundary. Converting to global stall is optional.

**Test**:

```bash
make format && make lint && make tb
# Run full testbench suite to catch hazard edge cases
```

---

## Step 5: PC/IF Stages

**Files**: `rtl/rv/svc_rv_stage_pc.sv`, `rtl/rv/svc_rv_stage_if.sv`

**Current state**: These are already mostly stall-based from Phase 1-2.

**Verify**:

- `stage_pc` uses `stall_pc` via `pipe_ctrl`
- `stage_if` has `s_ready = m_ready` (line 104) and `pc_stall = !m_ready`
  (line 112)

**Potential simplification**: If ID's s_ready is `!data_hazard_id`, then IF's
m_ready = `!data_hazard_id`, and `pc_stall = data_hazard_id`. This is correct -
data hazards should stall PC.

**No changes needed** - data_hazard_id continues to gate ID's s_ready, which
propagates correctly to PC stall.

---

## Step 6: Global Stall Generation (Future)

**File**: `rtl/rv/svc_rv.sv`

**After Step 1** (halt converted to stall):

```systemverilog
assign stall_cpu = halt;
```

**Future expansion** (when adding cache):

```systemverilog
assign stall_cpu = halt | load_stall_mem | div_stall_ex;
```

**Note**: Per-stage local stalls (`op_active_ex`, `data_hazard_id`) continue to
work via s_ready gating. Global stall expansion is for future cache miss
handling - not needed for this phase.

---

## Testing Sequence

After each step:

1. `make format`
2. `make lint`
3. `make svc_rv_soc_bram_tb` (basic BRAM)
4. `make svc_rv_soc_sram_tb` (basic SRAM)

After all steps:

1. `make tb` (full testbench suite)
2. `make formal` (formal verification)
3. riscv-formal

---

## Files to Modify

| Step | File                         | Change                                    |
| ---- | ---------------------------- | ----------------------------------------- |
| 1a   | `rtl/rv/svc_rv_stage_wb.sv`  | Remove m_ready port, `s_ready = 1'b1`     |
| 1b   | `rtl/rv/svc_rv.sv`           | `stall_cpu = halt`, remove wb_m_ready     |
| 2    | `rtl/rv/svc_rv_stage_mem.sv` | `s_ready = 1'b1`                          |
| 3    | `rtl/rv/svc_rv_stage_ex.sv`  | Remove m_ready from s_ready, simplify FSM |
| 4    | `rtl/rv/svc_rv_stage_id.sv`  | Remove m_ready from s_ready               |
| 5    | (verify only)                | PC/IF already done                        |

---

## Checklist

- [ ] Step 1a: WB remove m_ready port, s_ready = 1
- [ ] Step 1b: svc_rv.sv stall_cpu = halt, remove wb_m_ready
- [ ] Step 2: MEM s_ready = 1 (keep redirect skid buffer)
- [ ] Step 3: EX simplify s_ready and state machine
- [ ] Step 4: ID remove m_ready from s_ready
- [ ] Step 5: Verify PC/IF
- [ ] Full test suite
- [ ] Formal verification
- [ ] riscv-formal
