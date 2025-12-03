# Pipeline Ready/Valid Conversion Plan

## Overview

Convert the RISC-V pipeline from centralized stall/flush hazard control to
distributed ready/valid handshaking. This enables:

- Variable-latency cache at MEM stage
- IF stage split for BTB timing (deferred to Step 10)
- Cleaner stage isolation and composability

**Phase 1 (Steps 0-8)**: Convert all stage boundaries to ready/valid signaling
while keeping the existing IF stage structure (single IF1 stage).

**Phase 2 (Step 9)**: Add variable-latency cache integration.

**Phase 3 (Step 10)**: Split IF stage for BTB timing optimization (future work).

## Conventions

### Signal Naming

Stage outputs use `m_` prefix (manager), stage inputs use `s_` prefix
(subordinate), matching AXI convention:

```
Stage N                          Stage N+1
─────────                        ─────────
        m_valid  ──────────────► s_valid
        m_ready  ◄────────────── s_ready
        m_*      ──────────────► s_*      (payload signals)
```

### Handshake Rules

1. Transfer occurs when `valid && ready` on rising clock edge
2. Once `valid` asserted, it must stay high until `ready` (no dropping valid)
3. `ready` can change freely (no stability requirement)
4. Payload must be stable while `valid && !ready`

### Two Orthogonal Signal Planes

The pipeline has two independent signaling concerns that must not be conflated:

**Flow Control (Ready/Valid)**

- **Purpose**: Backpressure - "can data transfer?"
- **Signals**: `m_ready`, `s_ready`, `m_valid`, `s_valid`
- **Direction**: Ready flows backward (downstream → upstream), Valid flows
  forward
- **Scope**: Local to each stage boundary
- **Replaces**: Stall signals (`ex_mem_stall`, `id_ex_stall`, etc.)

**Control Signals (Flush/Kill)**

- **Purpose**: Instruction validity - "should this instruction execute?"
- **Signals**: `ex_mem_flush`, `id_ex_flush`, `if_id_flush`
- **Direction**: From hazard unit to stages
- **Scope**: Centralized in hazard unit, distributed to stages
- **Source**: Misprediction detection, multi-cycle ops, traps

**Why Keep Them Separate?**

1. **Different concerns**: Flow control is about bandwidth/timing; flush is
   about correctness
2. **Different sources**: Backpressure comes from downstream stages; flush comes
   from centralized hazard detection
3. **Centralized control**: Hazard unit coordinates flush response across all
   stages simultaneously
4. **Orthogonal behavior**: An instruction can transfer (`valid && ready`) but
   still be flushed - these are independent decisions

**Implementation**: Stages receive both `m_ready` (from downstream) and flush
signals (from hazard unit). Pipeline register updates gate on `m_ready` for flow
control. Flush signals zero out payload validity bits (like `reg_write`) to
create bubbles without blocking the handshake.

**Future Optimization**: Instead of transferring flushed instructions as NOPs,
gate `m_valid` with flush so flushed instructions don't transfer at all. Bubbles
become "absence of handshake" rather than "instruction that does nothing." This
reduces unnecessary pipeline activity but requires the basic ready/valid
conversion to be stable first.

### Flush/Kill Semantics

With ready/valid, flush becomes "kill" - mark in-flight data as invalid:

- Add `m_kill` signal from control (misprediction, trap)
- Receiving stage treats killed data as bubble (don't execute side effects)
- Killed transactions still complete handshake (valid/ready) to drain pipe
- Alternative: `m_valid` gated by `!kill` so killed instructions become bubbles

For this design, use the gating approach: upstream stages gate their `m_valid`
with flush conditions. This is simpler and matches current behavior where flush
inserts bubbles.

### Replacing Existing `valid_*` Signals

The current pipeline has `valid_if1`, `valid_id`, `valid_ex`, `valid_mem`,
`valid_wb` signals that track "this is a real instruction" vs "bubble from
flush". These are used for:

- Gating regfile writes
- RVFI retirement tracking
- BTB updates
- Multi-cycle operation gating

With ready/valid, the handshake `m_valid` serves both purposes:

1. Flow control: "I have data ready to transfer"
2. Instruction validity: "This is a real instruction"

Bubbles become **absence of handshake** rather than explicit invalid state. When
flushed, the stage deasserts `m_valid`, so no transfer occurs and downstream
sees nothing.

**The existing `valid_*` signals can be removed** as each step progresses. The
payload structs do NOT need a validity field - validity is implicit in the
handshake occurring.

### Skidbuf Usage

Use `svc_skidbuf` at each stage boundary:

- `OPT_OUTREG=0`: Combinational output, better for timing on ready path
- `OPT_OUTREG=1`: Registered output, better for timing on valid/data path

Start with `OPT_OUTREG=0` (matches current registered pipeline behavior where
the register is at stage input). Switch to `OPT_OUTREG=1` if timing requires.

### Signal Definitions

Pipeline signals are defined as individual wires in `svc_rv.sv` (the existing
pattern). We avoid SystemVerilog packages and structs due to inconsistent Yosys
open-source support (see comment in `svc_rv_defs.svh`).

Skidbuf instances will use explicit signal connections rather than packed
structs. This is more verbose but ensures maximum tool compatibility.

---

## Step 0: Signal Cleanup

**Goal**: Rename long signal names before structural changes.

**Files to Modify**:

- `rtl/rv/svc_rv_stage_mem.sv`
- `rtl/rv/svc_rv_stage_wb.sv`
- `rtl/rv/svc_rv.sv`

**Changes**:

Rename for clarity and shorter names:

- `dmem_rdata_ext_wb` → `ld_data_wb` (load data for WB stage)
- `dmem_rdata_ext_mem` → `ld_data_mem` (load data in MEM stage)

**Validation**:

- `make lint` passes
- `make tb` passes
- `make formal` passes (RVFI tests)

---

## Step 1: MEM→WB Interface (Ports Only)

**Goal**: Add ready/valid ports to MEM and WB stages without changing internal
logic. This is the minimal first step.

**Why First**: WB has no downstream. Always ready (regfile write is
single-cycle). Simplest case to establish the pattern.

**Files to Modify**:

- `rtl/rv/svc_rv_stage_mem.sv` - Add m_valid/m_ready ports
- `rtl/rv/svc_rv_stage_wb.sv` - Add s_valid/s_ready ports
- `rtl/rv/svc_rv.sv` - Wire the new signals

**Changes**:

1. MEM stage - Add ports, trivial wiring:

   ```systemverilog
   output logic m_valid,
   input  logic m_ready,

   // Trivial implementation - just expose existing valid
   assign m_valid = valid_wb;  // Output what we already compute
   // m_ready unused for now (mark with SVC_UNUSED)
   ```

2. WB stage - Add ports, trivial wiring:

   ```systemverilog
   input  logic s_valid,
   output logic s_ready,

   assign s_ready = 1'b1;  // Always ready
   // s_valid unused for now (still use valid_wb internally)
   ```

3. Top-level - Wire directly (no skidbuf yet):

   ```systemverilog
   logic mem_m_valid, mem_m_ready;
   logic wb_s_valid, wb_s_ready;

   assign wb_s_valid = mem_m_valid;
   assign mem_m_ready = wb_s_ready;
   ```

**Key Point**: NO internal logic changes. All existing always_ff blocks
unchanged. This is purely adding interface wires.

**Validation**:

- `make lint` passes
- `make tb` passes
- `make formal` passes
- Behavior identical to before (no functional change)

---

## Step 2: MEM→WB - m_valid as Source of Truth

**Goal**: Have m_valid be computed in MEM stage, valid_wb follows it.

**Files to Modify**:

- `rtl/rv/svc_rv_stage_mem.sv` - m_valid drives valid_wb
- `rtl/rv/svc_rv_stage_wb.sv` - Use s_valid for retirement

**Changes**:

1. MEM stage:

   - Keep existing valid_wb pipeline register logic
   - Add: `assign m_valid = valid_wb;`
   - OR: Rename internal signal, have m_valid be the registered output

2. WB stage:
   - Change retirement logic to use s_valid instead of valid_wb
   - `retired = s_valid;`
   - `ebreak = s_valid && (instr_wb == I_EBREAK);`

**Validation**:

- All tests pass
- Retirement still works correctly

---

## Step 3: MEM→WB - Remove Stall Dependency

**Goal**: MEM stage uses m_ready instead of mem_wb_stall for flow control.

**Files to Modify**:

- `rtl/rv/svc_rv_stage_mem.sv` - Use m_ready for pipeline register updates
- `rtl/rv/svc_rv_hazard.sv` - Stop generating mem_wb_stall (or ignore it)

**Changes**:

1. MEM stage pipeline registers:

   - Change `if (!mem_wb_stall)` to `if (m_ready)`
   - Or use proper valid/ready handshake: update when `m_valid && m_ready`

2. Hazard unit:
   - Remove mem_wb_stall generation
   - Or keep generating but MEM stage ignores it

**Validation**:

- All tests pass
- Backpressure works via ready/valid

---

## Step 4: EX→MEM Boundary

**Goal**: Convert EX→MEM to ready/valid. This is where cache backpressure will
originate.

**Files to Modify**:

- `rtl/rv/svc_rv_stage_ex.sv` - Add valid/ready output interface
- `rtl/rv/svc_rv_stage_mem.sv` - Add valid/ready input interface
- `rtl/rv/svc_rv.sv` - Wire the new signals

**Interface Changes**:

EX stage outputs (add):

```
output logic m_valid,
input  logic m_ready,
// Existing payload signals unchanged
```

MEM stage inputs (add):

```
input  logic s_valid,
output logic s_ready,
// Existing payload signals unchanged
```

**Implementation Notes**:

1. MEM stage `s_ready`:

   - For now: `s_ready = m_ready` (pass through from WB)
   - Later with cache: `s_ready = m_ready && !cache_busy`

2. EX stage:

   - `m_valid` = `valid_ex && !flush_condition`
   - Multi-cycle ops: `m_valid` stays low until op completes
   - Remove EX/MEM pipeline registers
   - Stall when `!m_ready` (don't advance internal state)

3. Flush handling:

   - Misprediction detected in EX gates `m_valid` for following instructions
   - Instructions already in MEM/WB drain normally
   - Add `kill` input to MEM that gates side effects (mem writes)

4. Top-level:
   - Wire signals directly (no skidbuf yet - preserve existing timing)
   - Remove `ex_mem_stall` and `ex_mem_flush` from hazard unit
   - Hazard unit signals misprediction via `kill` instead of `flush`

**Multi-cycle Operation Changes**:

Current: `op_active_ex` feeds hazard unit which asserts stalls.

New: EX stage internally stalls (holds `m_valid` low, ignores `s_valid`) until
multi-cycle op completes. Hazard unit doesn't need to know.

**Validation**:

- All testbenches pass
- Formal verification passes
- Test multi-cycle ops (DIV/REM) still work
- Test branch misprediction still flushes correctly

---

## Step 5: ID→EX Boundary

**Goal**: Convert ID→EX to ready/valid.

**Files to Modify**:

- `rtl/rv/svc_rv_stage_id.sv` - Add valid/ready output interface
- `rtl/rv/svc_rv_stage_ex.sv` - Add valid/ready input interface
- `rtl/rv/svc_rv.sv` - Wire the new signals

**Implementation Notes**:

1. ID stage `m_valid`:

   - Valid when instruction decoded and not flushed
   - Gate with flush from EX (misprediction)

2. EX stage `s_ready`:

   - Ready when not stalled by multi-cycle op
   - `s_ready = m_ready && !op_active_ex`

3. Load-use hazard:

   - Currently: Hazard unit detects, stalls ID
   - New: EX knows it needs forwarded data from MEM. If MEM hasn't produced it
     yet, EX deasserts `s_ready` to stall ID.
   - Alternative: Keep hazard detection in ID, gate `m_valid` on hazard

4. Data forwarding:
   - Forwarding paths remain combinational
   - No change to forwarding logic itself
   - Just need to ensure forwarded data validity aligns with handshake

**Hazard Unit Changes**:

- Remove `id_ex_stall` and `id_ex_flush`
- Load-use hazard: EX deasserts ready, or ID detects and gates valid
- Misprediction: EX signals kill to ID

**Validation**:

- All tests pass
- Forwarding still works (run tests with FWD=1)
- Load-use stalls work correctly

---

## Step 6: IF→ID Boundary

**Goal**: Convert IF→ID to ready/valid signaling. Keep IF as a single stage
(IF1) for now - the IF0→IF1→IF2 split is deferred to Step 11.

**Files to Modify**:

- `rtl/rv/svc_rv_stage_if1.sv` - Add valid/ready output interface
- `rtl/rv/svc_rv_stage_id.sv` - Add valid/ready input interface
- `rtl/rv/svc_rv.sv` - Wire signals

**Implementation Notes**:

1. IF1 outputs instruction and prediction info with m_valid/m_ready
2. ID `s_ready`:

   - Ready when EX is ready and no internal stall
   - `s_ready = m_ready` (pass through)

3. IF1 `m_valid`:

   - Valid when instruction fetched and not flushed
   - Gate with flush from EX (misprediction)

4. Flush from EX:

   - Misprediction kills IF1 stage instruction
   - IF1 gates `m_valid` when killed

5. PC update:

   - IF1 only advances PC when `m_valid && m_ready`
   - Redirect (misprediction) still overrides PC

6. Pipeline registers:
   - Keep IF1→ID pipeline registers for now (preserve timing)
   - Skidbufs added later if needed for backpressure

**Note**: The IF stage split (IF0→IF1→IF2 for BTB timing) is deferred to Step 11
as a separate optimization phase after the full pipeline is converted to
ready/valid.

**Validation**:

- All tests pass
- Branch prediction still works
- Misprediction recovery works
- Instruction fetch works correctly

---

## Step 7: Refactor Hazard Unit

**Goal**: Convert hazard unit from stall/flush generation to kill signal
generation. Move data hazard stall logic into stages.

**Current Responsibilities**:

1. Data hazard detection (RAW dependencies) → generates stalls
2. Control hazard detection (branches/jumps) → generates flushes
3. Load-use hazard detection → generates stalls
4. Multi-cycle op coordination → generates stalls

**New Responsibilities**:

1. Control hazard detection → generates kill signals
2. Misprediction detection → generates kill signals

**Moved to Stages**:

1. Data hazard stalls → EX deasserts `s_ready` on load-use hazard
2. Multi-cycle op stalls → EX deasserts `s_ready` during operation

**Files to Modify**:

- `rtl/rv/svc_rv_hazard.sv` - Replace stall/flush with kill signals
- `rtl/rv/svc_rv_stage_ex.sv` - Add load-use hazard detection for `s_ready`
- `rtl/rv/svc_rv.sv` - Update signal wiring

**Implementation Notes**:

1. Hazard unit becomes "kill controller":

   - Detects misprediction, trap, ebreak
   - Outputs `kill_if0`, `kill_if1`, `kill_id`, `kill_ex` signals
   - Stages use kill to gate their `m_valid`

2. EX stage handles its own stalls:

   - Detects load-use hazard (needs rd_mem, reg_write_mem, etc.)
   - Deasserts `s_ready` when hazard detected or op_active
   - This is local backpressure, not centralized control

3. Remove stall signals from hazard unit:

   - `pc_stall`, `if_id_stall`, `id_ex_stall`, `ex_mem_stall` removed
   - Backpressure flows through ready/valid chain

4. Remove flush signals from hazard unit:
   - `if_id_flush`, `id_ex_flush`, `ex_mem_flush` removed
   - Kill signals replace them

**Note**: Forwarding logic (`svc_rv_fwd_ex.sv`, `svc_rv_fwd_id.sv`) is
unchanged. It remains combinational and works with the ready/valid flow.

**Validation**:

- All tests pass
- Forwarding still works (FWD=1 configurations)
- Load-use stalls still work
- Multi-cycle ops still work

---

## Step 8: Skidbuf Integration

**Goal**: Add skidbufs at stage boundaries for proper backpressure buffering.

**Why Last**: Skidbufs add register stages that change timing. By adding them
last, we can verify the ready/valid conversion works with existing timing first,
then add skidbufs only where needed for backpressure (cache stalls).

**Files to Modify**:

- `rtl/rv/svc_rv.sv` - Instantiate skidbufs at stage boundaries

**Implementation Notes**:

1. Start with MEM→WB boundary (where cache backpressure originates)
2. Add skidbufs upstream as needed for proper buffering
3. Use `OPT_OUTREG=0` initially (matches current timing)
4. Pack/unpack payload signals through each skidbuf

**Validation**:

- All tests pass
- Pipeline functions correctly with buffering
- Timing analysis if needed

---

## Step 9: Variable-Latency Cache Integration

**Goal**: Add cache at MEM stage that can stall on miss.

**Files to Create**:

- `rtl/rv/svc_rv_dcache.sv` - Data cache with ready/valid interface

**Files to Modify**:

- `rtl/rv/svc_rv_stage_mem.sv` - Integrate cache, update `s_ready`

**Implementation Notes**:

1. Cache interface:

   - Request: `req_valid`, `req_ready`, `req_addr`, `req_write`, `req_wdata`
   - Response: `resp_valid`, `resp_ready`, `resp_rdata`
   - Or simpler: single-cycle hit, multi-cycle miss with busy signal

2. MEM stage changes:

   - `s_ready = m_ready && !cache_busy`
   - On cache miss, hold `s_ready` low until data returns
   - Cache hit: single cycle, no stall

3. Memory write handling:
   - Write buffer or write-through
   - May need separate handling for stores vs loads

**Validation**:

- Test cache hits (should be fast path)
- Test cache misses (pipeline stalls correctly)
- Test back-to-back accesses
- Test mixed loads/stores

---

## Step 10: Split IF Stage (Future Optimization)

**Prerequisite**: Complete Steps 1-8 first. The full pipeline must be converted
to ready/valid before splitting IF. This is a separate optimization phase.

**Goal**: Split IF into IF0→IF1→IF2 for BTB timing.

**Current IF Timing Problem**:

```
BTB lookup (IF0) → BTB result (IF1) → prediction → next PC (IF0)
```

The prediction→next PC path is the critical path.

**New Structure**:

- IF0: PC register, issue IMEM address
- IF1: BTB lookup, IMEM access
- IF2: BTB result registered, prediction decision, instruction output

**Files to Create**:

- `rtl/rv/svc_rv_stage_if2.sv` - New IF2 stage

**Files to Modify**:

- `rtl/rv/svc_rv_stage_if0.sv` - Simplify, just PC and IMEM address
- `rtl/rv/svc_rv_stage_if1.sv` - BTB lookup, pass through IMEM data
- `rtl/rv/svc_rv.sv` - Wire new stage

**Implementation Notes**:

1. IF0:

   - Owns PC register
   - Outputs PC to IMEM and BTB
   - `m_valid` when not killed

2. IF1:

   - Receives PC from IF0
   - BTB lookup in progress
   - IMEM read in progress (or complete for SRAM)
   - Outputs PC, raw BTB results

3. IF2:

   - BTB results are now registered (timing clean)
   - Makes prediction decision
   - Outputs instruction + prediction info to ID

4. PC feedback path:
   - Prediction decision in IF2 feeds back to IF0
   - Path is: IF2 registered output → mux → IF0 PC register
   - This is the path we're trying to shorten

**Validation**:

- All tests pass
- Timing improved on BTB→PC path
- Branch prediction still works
- Misprediction penalty may increase by 1 cycle (acceptable)

---

## Testing Strategy

### After Each Step

1. `make lint` - No new warnings
2. `make svc_rv_tb` - All testbench configurations pass
3. `make svc_rv_f` - Formal verification passes (if applicable)
4. Manual review of waveforms for key scenarios:
   - Normal execution
   - Branch taken/not-taken
   - Misprediction recovery
   - Load-use stall
   - Multi-cycle operation (DIV)

### Configuration Matrix

Test each step with all pipeline configurations:

- `PIPELINED=0` (single-cycle, may need adjustment)
- `PIPELINED=1, FWD=0` (pipelined, no forwarding)
- `PIPELINED=1, FWD=1` (pipelined with forwarding)
- `PIPELINED=1, FWD=1, BPRED=1` (with branch prediction)
- `PIPELINED=1, FWD=1, BPRED=1, BTB_ENABLE=1` (with BTB)
- `PIPELINED=1, EXT_M=1` (with M extension)

### Regression Markers

After each step, tag the commit:

- `pipeline-rv-step0-pkg`
- `pipeline-rv-step1-mem-wb`
- `pipeline-rv-step2-ex-mem`
- etc.

This allows easy bisection if issues found later.

---

## Rollback Plan

If a step causes issues that can't be resolved quickly:

1. Revert to previous step's commit
2. Analyze what went wrong
3. Adjust plan if needed
4. Re-attempt with fixes

Each step is designed to be independently revertible.

---

## Notes for Context-Free Execution

Each step should be executable with only:

1. This plan document
2. The current codebase state
3. Knowledge of SystemVerilog and ready/valid protocols

When starting a step:

1. Read the relevant section of this plan
2. Read the files listed in "Files to Modify"
3. Implement changes as described
4. Run validation tests
5. Commit with step marker

No prior conversation context needed.

---

## Future Cleanup Tasks

These are additional cleanup items identified during implementation:

### Remove op_active_ex as EX Output

Once all stages use ready/valid internally, `op_active_ex` no longer needs to be
an output from EX stage. Currently it's still used for:

- `pc_stall` and `if_id_stall` in svc_rv.sv

The plan is to have IF stalls also driven by ready/valid backpressure. When
that's complete, `op_active_ex` can become internal to EX stage only.

### Debug Display Stall Indicator

Change the debug display (`svc_rv_dbg.svh`) stall indicator to only show "s"
when `valid && !ready` (actual backpressure), not just `!ready`. This gives a
more accurate picture of when instructions are actually stalled vs when the
stage is simply empty.

Current:

```systemverilog
stall_str = !stage_id.m_ready ? "s" : " ";
```

Should be:

```systemverilog
stall_str = (stage_id.m_valid && !stage_id.m_ready) ? "s" : " ";
```

Apply similar pattern to all stage debug displays.
