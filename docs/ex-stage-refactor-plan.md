# Plan: Refactor svc_rv_stage_ex (Incremental Approach)

## Overview

Incrementally refactor `svc_rv_stage_ex` to use an explicit 3-state state
machine, then later add `svc_rv_pipe_ctrl` and `svc_rv_pipe_data`.

## Phase 1: State Machine Refactor (Complete)

Convert the implicit state machine (mc_state + mc_in_progress_reg + valid_reg)
to an explicit 3-state state machine using 2-process style. Keep the existing
pipeline register logic mostly unchanged.

### Current State (Implicit)

Two interacting mechanisms:

1. `mc_state`: `MC_STATE_IDLE` / `MC_STATE_EXEC` (divider control)
2. `valid_reg` + `mc_in_progress_reg`: Track pipeline valid during MC ops

### New State Machine (Explicit, 2-Process Style)

```
              ┌─────────────┐
    reset ───►│  EX_IDLE    │◄──────────────────────────────────┐
              │             │                                    │
              └──────┬──────┘                                    │
                     │                                           │
      s_valid &&     │                                           │
      is_mc_ex &&    │                                           │
      ex_mem_en      │                                           │
                     ▼                                           │
              ┌─────────────┐                                    │
              │  EX_MC_EXEC │ divider busy, block s_ready        │
              │             │                                    │
              └──────┬──────┘                                    │
                     │                                           │
      !m_busy_ex     │                                           │
      (op done)      │                                           │
                     ▼                                           │
              ┌─────────────┐                                    │
              │  EX_MC_DONE │ result ready, assert m_valid       │
              │             │ wait for downstream handshake      │
              └──────┬──────┘                                    │
                     │                                           │
      m_valid &&     │                                           │
      m_ready        └───────────────────────────────────────────┘
```

### State Descriptions

| State      | s_ready     | m_valid            | Description       |
| ---------- | ----------- | ------------------ | ----------------- |
| EX_IDLE    | ex_mem_en   | valid_reg (normal) | Normal operation  |
| EX_MC_EXEC | 0 (blocked) | 0                  | Divider executing |
| EX_MC_DONE | ex_mem_en   | valid_reg          | Result ready      |

### Implementation

```systemverilog
typedef enum logic [1:0] {
  EX_IDLE,
  EX_MC_EXEC,
  EX_MC_DONE
} ex_state_t;

ex_state_t ex_state;
ex_state_t ex_state_next;

//
// Process 1: Next state and outputs (always_comb)
//
always_comb begin
  ex_state_next = ex_state;
  op_active_ex  = 1'b0;
  op_en_ex      = 1'b0;

  case (ex_state)
    EX_IDLE: begin
      if (s_valid && is_mc_ex && ex_mem_en) begin
        ex_state_next = EX_MC_EXEC;
        op_en_ex      = 1'b1;
        op_active_ex  = 1'b1;
      end
    end

    EX_MC_EXEC: begin
      op_active_ex = 1'b1;
      if (!m_busy_ex) begin
        ex_state_next = EX_MC_DONE;
      end
    end

    EX_MC_DONE: begin
      if (m_valid && m_ready) begin
        ex_state_next = EX_IDLE;
      end
    end
  endcase
end

//
// Process 2: State register (always_ff)
//
always_ff @(posedge clk) begin
  if (!rst_n) begin
    ex_state <= EX_IDLE;
  end else begin
    ex_state <= ex_state_next;
  end
end
```

### Key Changes

1. **Replace mc_state** with `ex_state` (3 states instead of 2)
2. **Remove mc_in_progress_reg** - absorbed into state machine:
   - `mc_in_progress_reg` is true when
     `ex_state == EX_MC_EXEC || ex_state == EX_MC_DONE`
3. **Keep valid_reg and ex_mem_en** - existing pipeline register logic unchanged
4. **Update m_valid logic**:
   - Old: `m_valid = valid_reg && !mc_in_progress_ex`
   - New: `m_valid = valid_reg && (ex_state != EX_MC_EXEC)`
5. **Update mc_in_progress_ex**:
   - Old: `mc_in_progress_ex = (mc_state == MC_STATE_EXEC)`
   - New: `mc_in_progress_ex = (ex_state == EX_MC_EXEC)`
6. **Update effective_flush**:
   - Old: `mc_active = op_active_ex || mc_in_progress_reg`
   - New: `mc_active = (ex_state != EX_IDLE)`
7. **Update formal assertions** to use new state names

### Files to Modify

- `rtl/rv/svc_rv_stage_ex.sv`

## Phase 2: Add pipe_ctrl/pipe_data (Complete)

Convert pipeline registers to use `svc_rv_pipe_ctrl` and `svc_rv_pipe_data`.

### Design

- **pipe_ctrl**: Takes `m_valid_next` from state machine as `valid_i`, produces
  `m_valid` and control signals
- **pipe_data**: 3 instances for control signals, payload, and m_result
- **REG=PIPELINED**: Both modules handle pipelined vs passthrough via parameter

### Policy Choices

- `flush_i = effective_flush` (existing MC-aware flush logic)
- `bubble_i = !pipe_valid_i` (insert bubble when no valid output)
- All pipe_data use defaults (FLUSH_VAL=0, BUBBLE_VAL=0) - data clears to 0 on
  flush/bubble

### Key Implementation Details

**pipe_valid_i computation:**

```systemverilog
// In pipelined mode: use m_valid_next from state machine (includes hold logic)
// In passthrough mode: use original logic (no hold, direct from s_valid)
logic pipe_valid_i;
assign pipe_valid_i = (PIPELINED != 0) ?
    m_valid_next : (s_valid && !mc_in_progress_ex);
```

**Modules added:**

| Instance           | Purpose         | Notes                                |
| ------------------ | --------------- | ------------------------------------ |
| pipe_ctrl_inst     | Manages m_valid | valid_i=pipe_valid_i                 |
| pipe_ctrl_data     | Control signals | reg_write, mem_read, mem_write, trap |
| pipe_payload_data  | Payload signals | All other data                       |
| pipe_m_result_data | M-ext result    | Separate for clarity                 |

**What remains in g_registered/g_passthrough:**

- `s_ready` calculation (different between modes)
- `ex_mem_en`, `mc_active`, `effective_flush` (pipelined only)

### Formal Verification Updates

- Updated `svc_rv_pipe_ctrl` assertions to handle flush/bubble cases
- Updated `svc_rv_pipe_ctrl` valid_i stability to allow drop after handshake
- Updated stage_ex data stability assertions to account for flush

---

_Status: Phase 1 and Phase 2 complete_
