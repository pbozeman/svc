# RISC-V Pipeline Optimization Analysis

## Executive Summary

Analysis of the RISC-V pipeline implementation reveals several optimization
opportunities. The most aggressive configuration (SRAM + Branch Prediction +
Forwarding) achieves CPI of 1.17-2.50 across benchmarks. With targeted
optimizations, we can approach the theoretical limit of 1.0 CPI for most
workloads.

## Current Performance Baseline

### CPI Results: SRAM + BPRED + FWD Configuration

| Benchmark       | Actual CPI | Theoretical Best | Gap    | Root Cause                 |
| --------------- | ---------- | ---------------- | ------ | -------------------------- |
| ALU_Independent | 1.166      | 1.00             | +0.166 | Loop branch overhead       |
| ALU_Chain       | 1.375      | 1.00             | +0.375 | Branch and hazard overhead |
| Branch_Taken    | 2.498      | 1.00             | +1.498 | Branch penalty ~1.5 cycles |
| Load_Use        | 1.747      | 1.00-1.30        | +0.447 | Branch loop overhead       |
| Fib100          | 1.173      | 1.00             | +0.173 | Recursive call overhead    |
| BubbleSort      | 1.406      | 1.00             | +0.406 | Nested loop branches       |

## Critical Bottlenecks

### 1. Branch Penalty is ~3 Cycles (Highest Impact)

**Evidence:**

- Branch_Taken CPI: 2.498 (expected ~1.0 with good prediction)
- Per-branch overhead: ~3 cycles/branch
- Even correctly predicted branches pay significant penalty

**Root Cause:**

In `rtl/rv/svc_rv_hazard.sv:220`:

```systemverilog
assign if_id_flush = pc_sel || mispredicted_ex || (pred_taken_id && !data_hazard);
```

When a branch is predicted taken in ID stage:

1. Pipeline immediately flushes IF/ID registers
2. Branch comparison doesn't complete until EX stage (2-stage comparator)
3. Must wait for target instruction fetch
4. Lose 2-3 cycles even on correct prediction

**Why 2-Stage Branch Comparator:**

From `rtl/rv/svc_rv_bcmp.sv:18-23`:

```
// Splitting into 2 phases was a huge improvement in early testing on
// an hx8k, whereas this was consistently the critical path when all in EX.
```

The branch comparator splits across two stages for timing:

- ID stage: Compare lower 16 bits
- EX stage: Complete with upper 16 bits + funct3

Trade-off: Better fmax (timing closure) vs worse CPI (longer branch latency)

### 2. Branches Cannot Use Forwarded Data

**Evidence:**

In `rtl/rv/svc_rv_hazard.sv:191-192`:

```systemverilog
logic branch_hazard;
assign branch_hazard = is_branch_id && (ex_hazard || mem_hazard);
```

Branches stall on ANY EX or MEM hazard, even if the branch doesn't use those
registers.

**Root Cause:**

- Data forwarding only goes to EX stage (`rs1_fwd_ex`, `rs2_fwd_ex`)
- Branches read operands in ID stage
- No forwarding path from EX→ID or MEM→ID

**Common Pattern:**

```asm
ADDI x1, x1, 1    # Counter increment in EX
BNE  x1, x2, loop # Branch in ID needs x1 - STALL!
```

Even though x1 is available in EX from the previous ADDI, the branch in ID must
stall because there's no backward forwarding to ID stage.

**Impact:** Adds significant overhead to loop-intensive code (Load_Use,
ALU_Chain benchmarks)

### 3. Flush-on-Predict vs Speculative Fetch

**Current Behavior:**

```
Cycle 1: Branch in ID, predict taken → FLUSH IF/ID, redirect PC
Cycle 2: Wait for target instruction fetch
Cycle 3: Target instruction in IF
Cycle 4: Target instruction in ID
```

**Better Approach (Speculative Fetch):**

```
Cycle 1: Branch in ID, predict taken → start fetching target (keep IF/ID)
Cycle 2: Branch in EX confirms → commit speculation, target in IF
Cycle 3: Target in ID
```

Saves 1-2 cycles on correctly predicted branches by allowing IF/ID to continue
speculatively.

### 4. Conservative Branch Hazard Detection

**Current Implementation:**

```systemverilog
assign branch_hazard = is_branch_id && (ex_hazard || mem_hazard);
```

Stalls if ANY register in EX or MEM stage has a hazard, regardless of whether
the branch actually uses those registers.

**Better Approach:** Only stall if the branch ACTUALLY uses the hazarded
registers:

```systemverilog
assign branch_hazard = is_branch_id &&
                       ((ex_hazard_rs1 && rs1_used_id) ||
                        (ex_hazard_rs2 && rs2_used_id) ||
                        (mem_hazard_rs1 && rs1_used_id) ||
                        (mem_hazard_rs2 && rs2_used_id));
```

### 5. No Store-to-Load Forwarding

**Missing Pattern:**

```asm
SW  x3, 0(x10)   # Store to address
LW  x4, 0(x10)   # Load from same address - could forward!
```

Current implementation in `svc_rv_forward.sv` only forwards register results,
not memory data. Store-to-load forwarding would require:

- Address comparison logic
- Store buffer
- Memory data forwarding path

**Impact:** Moderate - not tested in current microbenchmarks but would help
real-world code with pointer aliasing patterns.

## Optimization Opportunities

Ranked by estimated impact on CPI:

| #     | Optimization                                   | Estimated CPI Gain | Complexity         | Priority |
| ----- | ---------------------------------------------- | ------------------ | ------------------ | -------- |
| **1** | **ID-stage forwarding for branches**           | **~0.3-0.5**       | Medium             | HIGH     |
| **2** | **Speculative fetch (don't flush on predict)** | **~0.2-0.3**       | Medium             | HIGH     |
| **3** | **Single-cycle branch comparison**             | **~0.5-1.0**       | High (fmax impact) | MEDIUM   |
| **4** | **Smarter branch hazard detection**            | **~0.1-0.2**       | Low                | MEDIUM   |
| 5     | Store-to-load forwarding                       | ~0.05-0.1          | High               | LOW      |
| 6     | Better branch predictor (2-bit, BTB)           | ~0.1-0.2           | Medium             | LOW      |

## Detailed Optimization Proposals

### OPT-1: ID-Stage Forwarding for Branches (HIGH PRIORITY)

**Goal:** Allow branches to use values from EX/MEM stages without stalling

**Implementation:**

1. **Add ID-stage forwarding outputs** in `svc_rv_forward.sv`:

```systemverilog
output logic [XLEN-1:0] rs1_fwd_id,  // NEW: Forward to ID stage
output logic [XLEN-1:0] rs2_fwd_id   // NEW: Forward to ID stage
```

2. **Implement EX→ID forwarding** (1 cycle backward):

```systemverilog
// Forward from EX stage to ID stage
logic ex_to_id_fwd_a, ex_to_id_fwd_b;

always_comb begin
  ex_to_id_fwd_a = 1'b0;
  ex_to_id_fwd_b = 1'b0;

  if (reg_write_ex && rd_ex != 5'd0 && !is_load_ex && !is_csr_ex) begin
    ex_to_id_fwd_a = (rd_ex == rs1_id);
    ex_to_id_fwd_b = (rd_ex == rs2_id);
  end
end

assign rs1_fwd_id = ex_to_id_fwd_a ? alu_result_ex : rs1_data_id;
assign rs2_fwd_id = ex_to_id_fwd_b ? alu_result_ex : rs2_data_id;
```

3. **Update branch comparator** to use forwarded values in `svc_rv.sv`:

```systemverilog
svc_rv_bcmp bcmp (
  .a_id(rs1_fwd_id),  // Was: rs1_data_id
  .b_id(rs2_fwd_id),  // Was: rs2_data_id
  // ... rest of signals
);
```

4. **Reduce branch stalls** in `svc_rv_hazard.sv`:

```systemverilog
// Only stall branches on load-use hazards (loads can't forward to ID)
logic branch_load_hazard;
assign branch_load_hazard = is_branch_id &&
                            ((is_load_ex && (ex_hazard_rs1 || ex_hazard_rs2)) ||
                             (is_load_mem && (mem_hazard_rs1 || mem_hazard_rs2)));

// OLD: assign branch_hazard = is_branch_id && (ex_hazard || mem_hazard);
// NEW: assign branch_hazard = branch_load_hazard;
```

**Expected Results:**

- Branch_Taken: 2.498 → ~2.0-2.2
- Load_Use: 1.747 → ~1.5-1.6
- ALU_Chain: 1.375 → ~1.2-1.3

### OPT-2: Speculative Fetch on Branch Prediction (HIGH PRIORITY)

**Goal:** Don't flush pipeline on predicted-taken branches; commit speculation
when confirmed

**Implementation:**

1. **Add speculation state** in `svc_rv_reg_if_id.sv`:

```systemverilog
logic speculative;  // NEW: Mark instruction as speculative
```

2. **Modify flush behavior** in `svc_rv_hazard.sv`:

```systemverilog
// OLD:
assign if_id_flush = pc_sel || mispredicted_ex || (pred_taken_id && !data_hazard);

// NEW:
assign if_id_flush = pc_sel || mispredicted_ex;
// pred_taken_id no longer causes immediate flush
```

3. **Add speculation tracking** in `svc_rv.sv`:

```systemverilog
// When branch predicted taken in ID, mark IF/ID as speculative
// but don't flush - let it continue
assign if_id_speculative_next = pred_taken_id && !data_hazard;

// In EX, if mispredicted, flush happens via existing logic
// If correctly predicted, commit speculation (no action needed)
```

4. **Handle control flow**:

```systemverilog
// Continue fetching from predicted target while branch resolves
// If misprediction detected in EX, existing flush logic handles recovery
```

**Expected Results:**

- Branch_Taken: 2.498 → ~1.8-2.0
- Saves 1-2 cycles per correctly predicted branch

### OPT-3: Optimize Branch Hazard Detection (MEDIUM PRIORITY)

**Goal:** Only stall branches when they actually depend on hazarded registers

**Implementation:**

In `svc_rv_hazard.sv`:

```systemverilog
// OLD:
assign branch_hazard = is_branch_id && (ex_hazard || mem_hazard);

// NEW:
assign branch_hazard = is_branch_id &&
                       ((ex_hazard_rs1 && rs1_used_id) ||
                        (ex_hazard_rs2 && rs2_used_id) ||
                        (mem_hazard_rs1 && rs1_used_id) ||
                        (mem_hazard_rs2 && rs2_used_id));
```

**Note:** Requires adding `rs1_used_id` and `rs2_used_id` signals from
instruction decoder.

**Expected Results:**

- Small improvement ~0.1 CPI in branch-heavy code
- Most benefit when branches don't use hazarded registers

### OPT-4: Single-Cycle Branch Comparison (MEDIUM PRIORITY)

**Goal:** Complete branch comparison in ID stage instead of splitting across
ID/EX

**Trade-off:** Potentially reduces fmax (timing critical path)

**Implementation:**

1. **Move all comparison logic to ID stage** in `svc_rv_bcmp.sv`:

```systemverilog
// Remove 2-stage split, do full comparison in ID
assign rs_eq = (a_id == b_id);
assign rs_lt_u = (a_id < b_id);
assign rs_lt_s = ($signed(a_id) < $signed(b_id));

// Compute branch_taken in ID instead of EX
always_comb begin
  case (funct3)
    FUNCT3_BEQ:  branch_taken_id = rs_eq;
    FUNCT3_BNE:  branch_taken_id = !rs_eq;
    FUNCT3_BLT:  branch_taken_id = rs_lt_s;
    // ... etc
  endcase
end
```

2. **Update pipeline**: Branch resolution happens in ID, not EX
3. **Reduce branch penalty**: From ~3 cycles to ~1-2 cycles

**Expected Results:**

- Branch_Taken: 2.498 → ~1.5-1.8
- **Risk:** May reduce fmax significantly (needs timing analysis)
- Only pursue if timing budget allows

### OPT-5: Store-to-Load Forwarding (LOW PRIORITY)

**Goal:** Forward store data directly to load when addresses match

**Implementation:**

1. **Add store buffer** to track recent stores:

```systemverilog
logic [31:0] store_addr;
logic [31:0] store_data;
logic        store_valid;
```

2. **Compare load address** with store buffer:

```systemverilog
logic store_load_match;
assign store_load_match = store_valid &&
                          (load_addr == store_addr);
```

3. **Forward store data** if match:

```systemverilog
assign load_data = store_load_match ? store_data : mem_data;
```

**Complexity:** High - requires address comparison, partial write handling,
multi-entry buffer for performance

**Expected Results:**

- ~0.05-0.1 CPI improvement on pointer-heavy code
- Current benchmarks don't test this pattern

### OPT-6: Better Branch Predictor (LOW PRIORITY)

**Current:** Static backward-taken prediction

**Options:**

- 2-bit saturating counter
- Branch Target Buffer (BTB)
- Return Address Stack (RAS)

**Expected Results:**

- ~0.1-0.2 CPI improvement
- Diminishing returns with other optimizations (reduced branch penalty means
  predictor matters less)

## Expected CPI with Optimizations

| Benchmark       | Current | +OPT-1 | +OPT-2 | +OPT-3 | Combined       |
| --------------- | ------- | ------ | ------ | ------ | -------------- |
| ALU_Independent | 1.166   | ~1.10  | ~1.05  | ~1.05  | **~1.00-1.05** |
| ALU_Chain       | 1.375   | ~1.20  | ~1.10  | ~1.05  | **~1.05-1.10** |
| Branch_Taken    | 2.498   | ~2.20  | ~2.00  | ~1.95  | **~1.50-1.70** |
| Load_Use        | 1.747   | ~1.60  | ~1.50  | ~1.45  | **~1.30-1.40** |
| Fib100          | 1.173   | ~1.10  | ~1.05  | ~1.03  | **~1.00-1.05** |
| BubbleSort      | 1.406   | ~1.30  | ~1.20  | ~1.15  | **~1.10-1.15** |

**Target:** 1.0-1.5 CPI across all benchmarks with combined optimizations

## Implementation Roadmap

### Phase 1: Quick Wins (Low Risk)

1. **Smarter branch hazard detection (OPT-3)**

   - Lowest risk, contained change
   - Modify hazard detection logic only
   - Immediate benefit for branch-heavy code

2. **ID-stage forwarding (OPT-1)**
   - High impact, moderate complexity
   - Well-understood forwarding technique
   - Biggest CPI improvement opportunity

### Phase 2: Moderate Effort (Medium Risk)

3. **Speculative fetch (OPT-2)**
   - Requires careful pipeline control
   - Speculation state management
   - Significant CPI improvement potential

### Phase 3: Consider Later (Trade-offs)

4. **Store-to-load forwarding (OPT-5)**

   - Only if real workloads show need
   - High complexity for modest gain
   - Not visible in current benchmarks

5. **Better branch predictor (OPT-6)**

   - Diminishing returns with other optimizations
   - Consider after reducing branch penalty

6. **Single-cycle branch (OPT-4)**
   - Only if fmax budget allows
   - High risk to timing
   - Needs thorough timing analysis

## Testing Recommendations

For each optimization:

1. **Verify CPI improvement** with `SVC_TB_RPT=1` on all benchmarks
2. **Run timing analysis** to check fmax impact
3. **Validate correctness** with full test suite
4. **Update CPI thresholds** to reflect improvements
5. **Document** architectural changes and trade-offs

## References

- Current CPI data: `tb/rv/svc_rv_soc_test_defs.svh`
- Pipeline implementation: `rtl/rv/svc_rv.sv`
- Hazard detection: `rtl/rv/svc_rv_hazard.sv`
- Forwarding logic: `rtl/rv/svc_rv_forward.sv`
- Branch comparison: `rtl/rv/svc_rv_bcmp.sv`
