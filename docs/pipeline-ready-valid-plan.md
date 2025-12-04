# Pipeline Ready/Valid Conversion Plan

## Overview

Convert the RISC-V pipeline from centralized stall/flush hazard control to
distributed ready/valid handshaking. This enables:

- Variable-latency cache at MEM stage
- IF stage split for BTB timing (deferred to Step 10)
- Cleaner stage isolation and composability

**Key Goal**: Remove ALL stall signals from the hazard unit. The hazard unit
should only generate flush/kill signals for control hazards (misprediction,
traps). All backpressure/stall behavior flows through the ready/valid chain -
each stage manages its own readiness based on downstream availability and
internal state.

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

## Step 6: IF Stage Split (stage_pc + stage_if)

**Goal**: Split IF into `stage_pc` and `stage_if` with ready/valid interfaces.
This makes the implicit IF0 (PC register) explicit and unifies BRAM/SRAM
handling.

**Background**

The current IF stage has an implicit IF0 (PC register controlled by `pc_stall`)
embedded within `svc_rv_stage_if.sv`. The BRAM/SRAM differences are handled via
conditional instantiation of `svc_rv_stage_if_bram.sv` or
`svc_rv_stage_if_sram.sv`.

Analysis revealed:

- `pc_stall` is really IF0's backpressure signal
- BRAM's 1-cycle latency provides natural registration (like I-cache hit)
- SRAM's 0-cycle latency is combinational, needs explicit registration for
  timing
- I-cache hit ≈ BRAM latency, so BRAM path is the "real" design for cache

**Proposed Structure**

```
stage_pc           stage_if            stage_id
────────           ────────            ────────
PC register        IMEM interface      Decode
Next PC mux        BTB lookup
                   Output buffering
```

**Stage Responsibilities**

`svc_rv_stage_pc`:

- Owns PC register
- Next PC mux: sequential (+4), predicted, redirect
- Issues address to IMEM and BTB
- `m_valid`: always valid after reset (always has a PC)
- `m_ready`: from stage_if, backpressure when stage_if can't accept

`svc_rv_stage_if`:

- Receives PC from stage_pc
- IMEM interface (address out, data in)
- BTB lookup (address out, result in)
- Output buffering (unified for BRAM/SRAM)
- `s_valid`/`s_ready`: from stage_pc
- `m_valid`/`m_ready`: to stage_id

**Memory-Type Handling in stage_if**

The key insight: I-cache hit ≈ BRAM ≈ 1-cycle latency. Design for this as
primary.

| Memory | IMEM Latency | BTB Latency | stage_if Output Buffer             |
| ------ | ------------ | ----------- | ---------------------------------- |
| SRAM   | 0-cycle      | 0-cycle     | Register (add 1 cycle for timing)  |
| BRAM   | 1-cycle      | 0-cycle\*   | Align BTB with BRAM (register BTB) |
| Cache  | 1-cycle hit  | 0-cycle\*   | Same as BRAM                       |

\*BTB assumed SRAM-based for fast lookup. If BTB is BRAM, it naturally aligns.

**SRAM Mode**

For simplicity, use unified structure where SRAM uses same pipeline as BRAM:

- SRAM "wastes" a cycle (adds registration it doesn't strictly need)
- Simpler code, same structure for all memory types
- Can optimize later with skidbuf passthrough if SRAM timing matters

**BTB Timing**

With stage_pc/stage_if split:

```
Cycle N:   stage_pc issues PC to BTB
Cycle N:   BTB lookup (combinational, SRAM-based BTB)
Cycle N+1: stage_if output registered
           BTB result now registered, clean timing for prediction
```

The BTB result gets registered as part of stage_if's output buffering, not as a
separate stage. This avoids the "extra step vs Rocket" problem.

**Ready/Valid Flow**

```
stage_pc               stage_if               stage_id
────────               ────────               ────────
      m_valid ────────► s_valid
      m_ready ◄──────── s_ready
                              m_valid ────────► s_valid
                              m_ready ◄──────── s_ready
```

stage_pc `m_ready` low when:

- stage_if can't accept (stage_if's `s_ready` low)
- stage_if stalled waiting for stage_id

stage_if `s_ready` low when:

- Output buffer full and stage_id not accepting
- Cache miss (future)

**Migration Path (Incremental Sub-steps)**

Each sub-step is independently testable. Run `make tb` and `make formal` after
each.

### Step 6a: Create stage_pc as pure extraction (internal to stage_if)

Create `svc_rv_stage_pc.sv` by extracting PC logic from `svc_rv_stage_if.sv`:

- PC register (lines ~132-138)
- Next PC mux (lines ~120-127)
- PC_INIT calculation (lines ~110-111)

stage_if instantiates stage_pc internally - no top-level changes yet. This
validates the extraction is correct before changing any wiring.

**Files**:

- New: `rtl/rv/svc_rv_stage_pc.sv`
- Modified: `rtl/rv/svc_rv_stage_if.sv` (instantiates stage_pc internally)

**Validation**: All tests pass (behavior identical)

### Step 6b: Move stage_pc to top level

Move stage_pc instantiation from stage_if to svc_rv.sv:

- Remove stage_pc instantiation from stage_if
- Add PC-related ports to stage_if (`pc` input, `pc_next` output)
- Instantiate stage_pc in svc_rv.sv
- Wire stage_pc ↔ stage_if

**Files**:

- Modified: `rtl/rv/svc_rv_stage_if.sv` (PC now comes from ports)
- Modified: `rtl/rv/svc_rv.sv` (instantiates stage_pc, wires to stage_if)

**Validation**: All tests pass (behavior identical)

### Step 6c: Add ready/valid interface between stage_pc and stage_if

Add handshake signals between the two stages:

- Add `m_valid`/`m_ready` ports to stage_pc
- Add `s_valid`/`s_ready` ports to stage_if (subordinate interface from PC)
- Initial implementation:
  - `m_valid` = 1 after reset (always has a PC to issue)
  - `s_ready` = `!pc_stall` (maps existing stall to ready)
- Wire in svc_rv.sv

**Files**:

- Modified: `rtl/rv/svc_rv_stage_pc.sv` (add m_valid/m_ready)
- Modified: `rtl/rv/svc_rv_stage_if.sv` (add s_valid/s_ready)
- Modified: `rtl/rv/svc_rv.sv` (wire handshake)

**Validation**: All tests pass (behavior identical, just new interface)

### Step 6d: Convert pc_stall to ready/valid (optional, can defer)

Replace pc_stall with ready/valid backpressure:

- stage_pc uses `m_ready` instead of `pc_stall` for PC register enable
- stage_if generates `s_ready` based on its ability to accept
- Remove `pc_stall` from hazard unit for IF stage

**Files**:

- Modified: `rtl/rv/svc_rv_stage_pc.sv` (use m_ready)
- Modified: `rtl/rv/svc_rv_stage_if.sv` (generate s_ready)
- Modified: `rtl/rv/svc_rv_hazard.sv` (remove pc_stall generation)
- Modified: `rtl/rv/svc_rv.sv` (remove pc_stall wiring)

**Validation**: All tests pass (backpressure via ready/valid)

### Future: Unify BRAM/SRAM (can be separate step)

Merge `svc_rv_stage_if_bram.sv` and `svc_rv_stage_if_sram.sv` into unified
stage_if with consistent buffering. This is orthogonal to the stage_pc split and
can be done separately.

**Files**:

- Modified: `rtl/rv/svc_rv_stage_if.sv` (unified implementation)
- Removed: `rtl/rv/svc_rv_stage_if_bram.sv`
- Removed: `rtl/rv/svc_rv_stage_if_sram.sv`

**Validation**:

- All tests pass
- Branch prediction still works
- Misprediction recovery works
- Instruction fetch works correctly

---

## Step 7: Remove id_stall from Hazard Unit

**Goal**: Remove `id_stall` from hazard unit. Stall behavior flows through
ready/valid backpressure instead of centralized stall signals.

**Current State** (after Step 6):

- `pc_stall` removed (Step 6d) - stage_pc uses `m_ready` backpressure
- `id_stall` still exists - goes to stage_id for data hazards, load-use,
  multi-cycle ops
- Flush signals work correctly - no changes needed

**What id_stall Currently Does**:

1. Data hazards (RAW dependencies) - stall ID while EX/MEM/WB have pending
   writes
2. Load-use hazards - stall ID when load result not yet available
3. Multi-cycle ops (`op_active_ex`) - stall ID while divider runs
4. Halt - stall everything

**Why NOT to Put Hazard in EX's s_ready**:

Putting `!data_hazard` in EX's s_ready causes **deadlock**:

1. Writer instruction (e.g., `addi x6, x0, 10`) is in the **ID/EX register**
2. Dependent instruction (e.g., `addi x7, x6, 5`) is in **ID stage**, blocked
3. `data_hazard = 1` → `s_ready = 0`
4. Capture to EX/MEM uses `s_accepted = s_valid && s_ready = 0`
5. Writer never advances from ID/EX to EX/MEM → **deadlock**

The problem: s_ready=0 is meant to block the dependent instruction (in ID) from
advancing to ID/EX. But it also blocks the writer instruction (already in ID/EX)
from being captured to EX/MEM, because EX's capture logic is gated by s_ready.

**Correct Approach: Hazard Handling in ID Stage**:

The hazard should be handled in ID stage, not EX stage:

1. **ID stage** receives `data_hazard` signal from hazard unit
2. **ID keeps m_valid low** when `data_hazard` is true
   - Doesn't present the dependent instruction to EX
3. **ID lowers s_ready** to backpressure IF
   - `s_ready = downstream_ready && !data_hazard`
4. **EX's s_ready is pure flow control** (no hazard term)
   - `s_ready = ex_mem_en && !op_active_ex`
5. Writer instruction in ID/EX advances normally to EX/MEM

This works because:
- The hazard blocks the **right thing**: the dependent instruction in ID
- The writer instruction (already in ID/EX) is **not blocked** - it advances
- Once writer reaches WB, hazard clears, dependent instruction can proceed

**Multi-cycle ops**: EX stage still gates s_ready with `!op_active_ex` for
multi-cycle operations (divider). This is flow control, not hazard handling.

**Halt**: Moves to stage_pc or top-level (stage_pc ignores m_ready when halted).

**Files to Modify**:

- `rtl/rv/svc_rv_hazard.sv` - Remove `id_stall` output, keep `data_hazard` output
- `rtl/rv/svc_rv_stage_id.sv` - Gate m_valid and s_ready with data_hazard
- `rtl/rv/svc_rv_stage_ex.sv` - s_ready is pure flow control (no hazard term)
- `rtl/rv/svc_rv.sv` - Wire data_hazard to ID stage

**Implementation Details**:

ID stage changes:
```systemverilog
// m_valid: Don't present dependent instruction during hazard
assign m_valid = has_valid_instruction && !data_hazard;

// s_ready: Backpressure IF during hazard
assign s_ready = downstream_ready && !data_hazard;
```

EX stage s_ready (pure flow control):
```systemverilog
assign s_ready = ex_mem_en && !op_active_ex;
```

**Flush signals unchanged**:

- `if_id_flush`, `id_ex_flush`, `ex_mem_flush` remain in hazard unit
- They handle control hazards (misprediction, traps)
- Orthogonal to flow control (ready/valid)

**Note**: Forwarding logic (`svc_rv_fwd_ex.sv`, `svc_rv_fwd_id.sv`) is
unchanged. It remains combinational and works with the ready/valid flow.

**Validation**:

- All tests pass
- Forwarding still works (FWD=1 configurations)
- Load-use stalls still work
- Multi-cycle ops still work
- No deadlock on data hazards

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

### Load Data Path Valid/Ready

Consider adding a valid/ready handshake on the load data forwarding path from
MEM to EX. When EX has an instruction that needs load data:

1. EX asserts request for forwarded load data (valid)
2. MEM responds with data when available (ready + data)
3. If MEM doesn't have the data yet (cache miss), handshake doesn't complete
4. EX naturally stalls waiting for the handshake, lowering its `s_ready`

This eliminates `id_stall` for load-use hazards entirely - EX manages its own
backpressure based on whether the data it needs is available. The hazard unit no
longer needs to detect load-use hazards; EX simply waits for the data path
handshake to complete.

Current: Hazard unit detects load-use → `id_stall` → ID lowers `s_ready` → IF
stalls.

Future: EX needs load data → requests via handshake → MEM not ready → EX lowers
`s_ready` → backpressure propagates naturally.

---

## Lessons Learned from Step 6 WIP Implementation

These insights emerged from the initial implementation attempt and should guide
future work.

### 1. Separate PC Selection Module (`svc_rv_pc_sel.sv`)

The original plan had the "Next PC mux" inside stage_pc. In practice, it's much
cleaner to extract all PC source arbitration into a standalone combinational
module:

- Priority: MEM misprediction > EX redirect > RAS > BTB > ID static > sequential
- ~270 lines of complex RAS/BTB/static prediction arbitration
- Keeps `svc_rv_stage_pc.sv` dead simple (~90 lines)

**Recommendation**: Create `svc_rv_pc_sel.sv` as a separate module that handles
all PC source arbitration. stage_pc just owns the PC register and applies the
selected next PC.

### 2. stage_pc is Simpler Than Expected

The final stage_pc only needs:

- PC register with reset to PC_INIT
- pc_next 3-way mux (redirect, predicted, sequential)
- `m_valid = 1'b1` always (always have a PC to issue)
- PC update gated by `m_ready`

All the PC source selection complexity lives in pc_sel, not stage_pc.

### 3. PC_INIT Depends on BPRED+MEM_TYPE

```systemverilog
//
// For BRAM with BPRED, PC starts at RESET_PC-4 so pc_next = RESET_PC
// on first cycle (early speculative fetch uses pc_next as address)
//
localparam logic [XLEN-1:0] PC_INIT =
    (MEM_TYPE == MEM_TYPE_BRAM && BPRED != 0) ? RESET_PC - 4 : RESET_PC;
```

This is a subtle but critical detail for correct first-instruction fetch with
BRAM + branch prediction.

### 4. BRAM Timing Subtleties

Several timing patterns emerged for BRAM handling:

**flush_extend**: Without BPRED, BRAM needs extended flush (one extra cycle)
because the sequential instruction is already in the pipeline when a redirect is
detected.

```systemverilog
//
// With BPRED: Target fetched immediately, no flush_extend needed
// Without BPRED: Sequential instruction in flight, need extra flush cycle
//
assign flush_extend = (BPRED != 0) ? 1'b0 : registered_if_id_flush;
```

**started flag**: Wait one cycle after reset before valid_buf goes high. This
accounts for BRAM latency on the first instruction.

```systemverilog
logic started;

always_ff @(posedge clk) begin
  if (!rst_n) begin
    started   <= 1'b0;
    valid_buf <= 1'b0;
  end else if (m_ready) begin
    started   <= 1'b1;
    valid_buf <= started && !if_id_flush && !flush_extend;
  end
end
```

**Buffer imem_raddr not pc**: For BRAM PC tracking, buffer the actual fetch
address (`imem_raddr`), not `pc`. With BPRED early fetch,
`imem_raddr = pc_next`, and this ensures the buffered PC matches the instruction
even during stalls.

### 5. pc_stall Eliminated

The `pc_stall` signal was removed from the hazard unit. PC update is now purely
gated by `m_ready` from stage_if, making it part of the ready/valid flow. This
is the correct pattern - backpressure should flow through ready/valid, not
through separate stall signals.

### 6. Signal Naming Conventions

Consistent naming emerged for different signal categories:

- `*_to_if_id`: Intermediate signals going to IF/ID pipeline register
- `*_buf`: Buffered versions of signals (one cycle delayed)
- `*_if`: IF-stage prediction signals from pc_sel (combinational)
- `*_id`: ID-stage versions of signals (registered)

### 7. Unified Memory Interface Simplification

With unified BRAM/SRAM interface (on svc-mem branch), many of these
BRAM-specific patterns can be simplified. The unified interface abstracts memory
latency differences, so stage_if doesn't need separate BRAM/SRAM
implementations.

**Note**: When redoing Step 6 on the unified memory branch, the flush_extend and
started patterns may need adjustment based on how the unified interface handles
latency.
