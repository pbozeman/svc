# RV Pipeline Valid Signal Cleanup Plan

## Overview

The pipeline previously attempted a full valid/ready handshake protocol, but
this was abandoned. What remains is `m_valid`/`s_valid` signals between stages
without corresponding ready signals—an awkward halfway state.

The `pipe_ctrl` and `pipe_data` modules already support bubbles via `bubble_i`
and `bubble_o` signals. Control signals (`reg_write`, `mem_read`, etc.) are
cleared on bubbles, which implicitly carries validity information.

## Key Insight

**Validity is only needed for `instret` CSR** (counts retired instructions). For
synthesis, control signals carry implicit validity:

| Use Case        | With Bubbles                                |
| --------------- | ------------------------------------------- |
| Regfile write   | `reg_write` is bubble-cleared               |
| Memory ops      | `mem_read/write` are bubble-cleared         |
| Halt logic      | `trap_ret`, `ebreak_ret` are bubble-cleared |
| Instruction cnt | Needs explicit `instr_valid` for `instret`  |

## Approach

**`instr_valid` is a simple signal in the control bundle**, not a first-class
`pipe_ctrl` citizen. It flows through `pipe_data` like any other control signal
and is bubble-cleared automatically.

## Implementation Strategy

**Work backwards from WB, one stage at a time, testing after each change.**

Each phase must pass `make formal` before proceeding to the next.

---

## Phase 1: WB Stage

### 1a: Add instr_valid to WB stage

**File: `svc_rv_stage_wb.sv`**

1. Add `instr_valid_wb` input port
2. Add `instr_valid_ret` output port
3. Add `instr_valid` to the `pipe_data` bundle (first field)
4. Remove `s_valid` input port
5. Remove `m_valid` output port

```systemverilog
// Port changes
input logic instr_valid_wb,      // ADD
output logic instr_valid_ret,    // ADD
// input logic s_valid,          // REMOVE
// output logic m_valid,         // REMOVE

// Update pipe_data bundle
localparam int PIPE_WIDTH = 1 + 32 + 4 * XLEN + 1 + 2 + 1 + 1;  // +1 for instr_valid

.data_i({
  instr_valid_wb,  // ADD at front
  instr_wb,
  pc_wb,
  ...
}),
.data_o({
  instr_valid_ret,  // ADD at front
  instr_ret,
  pc_ret,
  ...
})
```

### 1b: Add instr_valid_wb output to MEM stage

**File: `svc_rv_stage_mem.sv`**

1. Add `instr_valid_wb` output port
2. Add to `pipe_ctrl_data` bundle (first field, bubble-cleared)
3. Source from `s_valid` for now (will remove `s_valid` in Phase 2)

```systemverilog
// Port changes
output logic instr_valid_wb,     // ADD

// Update pipe_ctrl_data bundle
svc_rv_pipe_data #(
    .WIDTH(3),  // was 2, now 3
    .REG  (PIPELINED)
) pipe_ctrl_data (
    ...
    .data_i({s_valid, reg_write_mem && !misalign_trap, misalign_trap}),
    .data_o({instr_valid_wb, reg_write_wb, trap_wb})
);
```

### 1c: Update svc_rv.sv wiring

**File: `svc_rv.sv`**

1. Add `instr_valid_wb` wire
2. Add `instr_valid_ret` wire
3. Connect MEM's `instr_valid_wb` output to WB's `instr_valid_wb` input
4. Update `retired` signal: `assign retired = instr_valid_ret && !stall_wb;`
5. Remove `wb_s_valid` signal and connection
6. Remove `wb_m_valid` signal and connection

```systemverilog
// Add signals
logic instr_valid_wb;
logic instr_valid_ret;

// Update retired
assign retired = instr_valid_ret && !stall_wb;

// Update halt_next (trap_ret/ebreak_ret are bubble-cleared)
assign halt_next = (retired && (ebreak_ret || trap_ret)) || halt;
```

### 1d: Test Phase 1

```bash
make formal
```

---

## Phase 2: MEM Stage

### 2a: Remove s_valid/m_valid from MEM stage

**File: `svc_rv_stage_mem.sv`**

1. Remove `s_valid` input port
2. Remove `m_valid` output port
3. Update `instr_valid_wb` source in `pipe_ctrl_data`:
   - Was: `s_valid`
   - Now: `!bubble_i` or track from EX stage input

**Key question**: Where does MEM get its validity from?

- Option A: Add `instr_valid_mem` input from EX stage
- Option B: Derive from `!bubble_i` (instruction arrived this cycle)

For now, use Option A for clarity.

### 2b: Add instr_valid_mem output to EX stage

**File: `svc_rv_stage_ex.sv`**

1. Add `instr_valid_mem` output port
2. Source from `s_valid` for now (will remove in Phase 3)

### 2c: Update svc_rv.sv wiring

1. Add `instr_valid_mem` wire
2. Connect EX's output to MEM's input
3. Remove `mem_s_valid`, `mem_m_valid` signals

### 2d: Test Phase 2

```bash
make formal
```

---

## Phase 3: EX Stage

Similar pattern:

1. Add `instr_valid_ex` input from ID
2. Add `instr_valid_mem` output (already done in 2b)
3. Remove `s_valid` input, `m_valid` output
4. Update svc_rv.sv wiring
5. Test

---

## Phase 4: ID Stage

Similar pattern:

1. Add `instr_valid_id` input from IF
2. Add `instr_valid_ex` output
3. Remove `s_valid` input, `m_valid` output
4. Update svc_rv.sv wiring
5. Test

---

## Phase 5: IF/PC Stages

1. IF stage generates `instr_valid_id` from successful fetch
2. PC stage: remove `m_valid` (always produces valid when advancing)
3. Update svc_rv.sv wiring
4. Test

---

## Phase 6: Simplify pipe_ctrl

Remove `valid_i`/`valid_o` ports from `pipe_ctrl` entirely.

**Changes to `svc_rv_pipe_ctrl.sv`:**

1. Remove `valid_i` input port
2. Remove `valid_o` output port
3. Simplify `advance_o` logic:

```systemverilog
// Before
assign advance_o = can_accept && valid_i && !bubble_i && !flush_i;

// After
assign advance_o = can_accept && !bubble_i && !flush_i;
```

4. Remove `valid_o` register logic

**Potential difficulties:**

- Some stages may rely on `valid_i` for advance gating in ways not covered by
  `bubble_i`. Need to audit each stage's `bubble_i` source.
- The `advance_o` semantics change: previously "advance when valid input", now
  "advance when not bubbling". Stages must ensure `bubble_i` is set correctly
  when there's no valid input.
- Formal properties in `pipe_ctrl` reference `valid_i`/`valid_o` - need update.

**Update all stages:**

Remove `.valid_i()` and `.valid_o()` connections from all `pipe_ctrl`
instantiations.

**Test thoroughly** - this is the riskiest change.

---

## Phase 7: Final Cleanup

1. Update formal properties in `pipe_ctrl` and all stages
2. Remove any remaining `SVC_UNUSED` for valid signals
3. Update comments/documentation
4. Final test

---

## Signal Flow After Cleanup

```
PC -> IF -> ID -> EX -> MEM -> WB -> retired
       |     |     |      |      |
       v     v     v      v      v
     instr_valid flows through pipe_data bundles
     (bubble-cleared at each stage)
```

## Benefits

1. **Simpler design**: No redundant validity tracking
2. **Smaller synthesis**: Fewer FFs, less routing
3. **Cleaner semantics**: Control signals carry implicit validity
4. **Incremental**: Each phase is testable independently

## Testing Strategy

After each sub-phase:

1. Run `make formal`
2. If failures, fix before proceeding
3. Do NOT proceed to next phase until current phase passes
