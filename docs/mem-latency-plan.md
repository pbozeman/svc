# Memory Latency Simplification Plan

## Problem Statement

The current ready/valid backpressure through the pipeline is overly complex and
creates subtle bugs (redirect lost under backpressure, flush/stall timing
issues). The backpressure infrastructure was built to support variable memory
latency, but it's solving a problem we don't actually have in most pipeline
stages.

Real stall sources:

1. **Data hazards** - Handled by hazard unit (data_hazard_id)
2. **Division** - Handled locally in EX (op_active_ex)
3. **Cache miss** - Should be global freeze, not backpressure

## Phase 1: Revert to Known Good State

### 1.1 Identify Changes to Keep

**REVIEWED**: No changes worth keeping. All formal additions since 411b5585 are
tied to ready/valid backpressure (f_outstanding tracking, stability assumes for
s_valid && !s_ready, etc.) which we're removing entirely. Clean revert is safe.

### 1.2 Revert to 411b5585

```bash
git checkout 411b55851b26e321295b49807db2dd9577ccfac5 -- rtl/rv/ tb/rv/
```

### 1.3 Surgical Reverts

**Undo MEM_TYPE removal** (cd8ff616):

- Restore MEM_TYPE parameter to svc_rv_stage_mem.sv
- Restore MEM_TYPE-based latency handling

**Undo IF fifo/fetch buffer** (eb88e9dd):

- Revert svc_rv_stage_if.sv to pre-fifo version
- Remove imem backpressure

### 1.4 Verify Baseline

- Run full testbench suite
- Run riscv-formal
- Check CPI benchmarks

## Phase 2: Add Stall Infrastructure

### 2.1 Modify pipe_ctrl

Add `stall_i` input to `svc_rv_pipe_ctrl`:

```systemverilog
module svc_rv_pipe_ctrl #(
    parameter bit REG = 1
) (
    input logic clk,
    input logic rst_n,

    input  logic valid_i,
    output logic valid_o,
    input  logic ready_i,   // Keep for now, will remove later

    input logic stall_i,    // NEW: Global stall
    input logic flush_i,
    input logic bubble_i,

    output logic advance_o,
    output logic flush_o,
    output logic bubble_o
);

  if (REG != 0) begin : g_registered
    logic can_accept;
    // Stall takes priority - when stalled, nothing advances
    assign can_accept = !stall_i && (!valid_o || ready_i);
    // ...
  end
```

### 2.2 Add Tests for pipe_ctrl Stall

- Create tb/rv/svc_rv_pipe_ctrl_tb.sv
- Test stall holds pipeline state
- Test stall interacts correctly with flush/bubble

### 2.3 Add Formal for pipe_ctrl Stall

- Stall holds valid_o stable
- Stall prevents advance_o
- Stall interacts correctly with flush

### 2.4 Wire Stall Through svc_rv

Pass stall signal through all stages, initially hardwired to 1'b0:

```systemverilog
// In svc_rv.sv
logic cpu_stall;
assign cpu_stall = 1'b0;  // Initially disabled

// Pass to all pipe_ctrl instances
.stall_i(cpu_stall)
```

## Phase 3: Convert Backpressure to Stalls

### 3.1 Current Backpressure Points

| Stage | Current Mechanism                | New Mechanism                                   |
| ----- | -------------------------------- | ----------------------------------------------- |
| PC    | m_ready from IF                  | cpu_stall                                       |
| IF    | s_ready/m_ready                  | cpu_stall                                       |
| ID    | s_ready/m_ready + data_hazard_id | cpu_stall + data_hazard                         |
| EX    | s_ready/m_ready + op_active_ex   | cpu_stall + op_active                           |
| MEM   | s_ready/m_ready + load_stall     | cpu_stall (load_stall becomes cpu_stall source) |
| WB    | s_ready/m_ready                  | cpu_stall                                       |

### 3.2 Stall Sources (Managed by Hazard Unit)

```systemverilog
// In svc_rv_hazard.sv or new svc_rv_stall.sv
assign cpu_stall = load_stall_mem    // Cache miss
                 | div_stall_ex;     // Division in progress
```

Data hazards remain as-is (gate m_valid in ID via data_hazard_id).

### 3.3 Remove Backpressure

Once stalls work:

1. Remove ready_i from pipe_ctrl (or ignore it)
2. Simplify s_ready assignments in stages to constant 1
3. Remove skid buffer logic from stage_pc

## Phase 4: Verification

### 4.1 Random Latency SOC

Create test SOC that injects random memory latency:

```systemverilog
module svc_rv_soc_random_latency #(...) (
    // Randomly delay dmem_rvalid by 0-N cycles
    // Verify CPU handles all patterns correctly
);
```

### 4.2 Full Regression

- All testbenches pass
- All formal checks pass
- riscv-formal passes
- CPI benchmarks match or improve

## Phase 5: Future - Cache Integration

(Separate plan after Phase 4 complete)

- Cache miss sets cpu_stall
- Cache hit allows normal operation
- No pipeline backpressure needed

## Files to Modify

### Phase 1

- rtl/rv/\*.sv (revert)
- tb/rv/\*.sv (revert)

### Phase 2

- rtl/rv/svc_rv_pipe_ctrl.sv (add stall_i)
- rtl/rv/svc_rv.sv (wire stall)
- tb/rv/svc_rv_pipe_ctrl_tb.sv (new)
- tb/formal/svc_rv_pipe_ctrl.sby (update)

### Phase 3

- rtl/rv/svc_rv_hazard.sv (stall generation)
- rtl/rv/svc*rv_stage*\*.sv (simplify ready logic)
- rtl/rv/svc_rv.sv (remove ready wiring)

### Phase 4

- tb/rv/svc_rv_soc_random_latency_tb.sv (new)
