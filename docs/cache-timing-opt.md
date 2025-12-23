# Cache Timing Optimization Plan

Breaking the critical timing path in `svc_cache_axi` for 1-cycle dcache hits on
Xilinx.

## Problem

Vivado reports a long timing path through:

```
rd_addr → tag compare → hit → evict_way (LRU) → state_next → dmem_stall → CPU PC
```

The LRU/eviction logic is "always live" and contaminates the hit fast path.

## Constraints

- Hits must remain single-cycle (rd_valid cycle N → rd_data_valid cycle N+1)
- No stall-then-release bubbles on hits
- No CPU replay/flush mechanisms
- Additional latency acceptable only on misses/fills

## Staged Changes

### Stage 1: Simplify `rd_ready`

**File:** `rtl/common/svc_cache_axi.sv`

**Current (line 806-807):**

```systemverilog
assign rd_ready = (state == STATE_IDLE) ||
                  (state != STATE_READ_BURST && state != STATE_READ_SETUP && hit);
```

**Change to:**

```systemverilog
assign rd_ready = (state == STATE_IDLE);
```

**Rationale:** The bridge (`svc_rv_dmem_cache_if`) marks `cache_rd_ready` as
unused. The second clause pulls `hit` into `rd_ready`'s fanin unnecessarily.

**Risk:** Low - `rd_ready` is unused by the bridge.

**Verification:** Run `make svc_cache_axi_tb` and existing dcache testbenches.

---

### Stage 2: Isolate `hit` in `rd_data_valid_next`

**File:** `rtl/common/svc_cache_axi.sv`

**Current (line 773):**

```systemverilog
assign rd_data_valid_next = (rd_valid && rd_ready && hit) || fill_done;
```

**Change to:**

```systemverilog
logic hit_complete;
assign hit_complete = (state == STATE_IDLE) && rd_valid && hit;
assign rd_data_valid_next = hit_complete || fill_done;
```

**Rationale:** Removes `rd_ready` from the `rd_data_valid_next` cone. After
Stage 1, this is equivalent but makes the intent explicit.

**Risk:** Low - functionally equivalent.

**Verification:** Same as Stage 1.

---

### Stage 3: Defer Eviction Selection to `STATE_READ_SETUP`

**File:** `rtl/common/svc_cache_axi.sv`

This is the key timing fix. Move `fill_way` capture from the miss transition to
the setup state.

#### 3a: Delete original `gen_evict_2way` block (lines 303-315)

Remove entirely to prevent Vivado from keeping dead logic in timing cones:

```systemverilog
// DELETE this entire block:
if (TWO_WAY) begin : gen_evict_2way
  always_comb begin
    if (!way0_valid) begin
      evict_way = 1'b0;
    end else if (!way1_valid) begin
      evict_way = 1'b1;
    end else begin
      evict_way = lru_table[addr_set];
    end
  end
end else begin : gen_evict_direct
  assign evict_way = 1'b0;
end
```

Also remove the `evict_way` signal declaration (line 207).

#### 3b: Compute eviction INSIDE the FSM case branch

Do NOT add a separate always_comb - compute it inline in STATE_READ_SETUP to
keep synthesizer from making it "always live":

**Modify FSM STATE_IDLE branch (line 356-359):**

```systemverilog
// Before:
if (rd_valid && !hit) begin
  state_next         = STATE_READ_SETUP;
  beat_word_idx_next = '0;
  fill_way_next      = evict_way;  // REMOVE THIS LINE
end

// After:
if (rd_valid && !hit) begin
  state_next         = STATE_READ_SETUP;
  beat_word_idx_next = '0;
  // fill_way computed in STATE_READ_SETUP from registered address
end
```

**Modify FSM STATE_READ_SETUP branch (line 367-371):**

```systemverilog
// Before:
STATE_READ_SETUP: begin
  state_next         = STATE_READ_BURST;
  m_axi_arvalid_next = 1'b1;
  m_axi_araddr_next  = fill_addr_line_aligned;
end

// After:
STATE_READ_SETUP: begin
  state_next         = STATE_READ_BURST;
  m_axi_arvalid_next = 1'b1;
  m_axi_araddr_next  = fill_addr_line_aligned;

  // Compute eviction way from REGISTERED address (miss-only path)
  if (TWO_WAY) begin
    if (!valid_table[fill_addr_set][0]) begin
      fill_way_next = 1'b0;
    end else if (!valid_table[fill_addr_set][1]) begin
      fill_way_next = 1'b1;
    end else begin
      fill_way_next = lru_table[fill_addr_set];
    end
  end else begin
    fill_way_next = 1'b0;
  end
end
```

#### 3c: Guard fill writes with state check

Ensure fill write logic only fires in STATE_READ_BURST (defensive against weird
AXI timing, also helps timing cones):

**Modify data write control (line 504):**

```systemverilog
// Before:
if (fill_beat_pending || (m_axi_rvalid && m_axi_rready)) begin

// After:
if ((state == STATE_READ_BURST) &&
    (fill_beat_pending || (m_axi_rvalid && m_axi_rready))) begin
```

**Rationale:** The miss path becomes `rd_addr → !hit → state_next=READ_SETUP`.
Eviction selection happens one cycle later using the registered `fill_addr_set`.
This removes `lru_table[addr_set]` and the eviction mux from the hit/miss
decision timing. The state guard on fill writes prevents any fill bookkeeping
from being "live" during IDLE/hit.

**Risk:** Medium - changes when `fill_way` is sampled.

**Verification:**

- `make svc_cache_axi_f` (formal)
- `make svc_cache_axi_direct_tb svc_cache_axi_twoway_tb`
- Full dcache SOC testbenches

---

### Stage 4: Split LRU Update Paths (Optional)

**File:** `rtl/common/svc_cache_axi.sv`

Replace the single LRU update block (lines 629-674) with three independent
registered paths.

```systemverilog
if (TWO_WAY) begin : gen_lru_update
  //
  // Split LRU updates into independent registered paths to reduce

// combinational depth. Each source has its own small pipeline.
  //

  // Read-hit LRU request
  logic                 rd_lru_req;
  logic [SET_WIDTH-1:0] rd_lru_set;
  logic                 rd_lru_val;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      rd_lru_req <= 1'b0;
    end else begin
      rd_lru_req <= (state == STATE_IDLE) && rd_valid && hit;
      rd_lru_set <= addr_set;
      rd_lru_val <= ~way1_hit;
    end
  end

  // Write-hit LRU request
  logic                 wr_lru_req;
  logic [SET_WIDTH-1:0] wr_lru_set;
  logic                 wr_lru_val;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      wr_lru_req <= 1'b0;
    end else begin
      wr_lru_req <= wr_valid && wr_ready && wr_hit;
      wr_lru_set <= wr_addr_set;
      wr_lru_val <= ~wr_way1_hit;
    end
  end

  // Fill-done LRU request
  logic                 fill_lru_req;
  logic [SET_WIDTH-1:0] fill_lru_set;
  logic                 fill_lru_val;

  always_ff @(posedge clk) begin
    if (!rst_n) begin
      fill_lru_req <= 1'b0;
    end else begin
      fill_lru_req <= fill_done;
      fill_lru_set <= fill_addr_set;
      fill_lru_val <= ~fill_way;
    end
  end

  // Priority write to LRU table (simple 3-input mux on registered values)
  always_ff @(posedge clk) begin
    if (rd_lru_req) begin
      lru_table[rd_lru_set] <= rd_lru_val;
    end else if (wr_lru_req) begin
      lru_table[wr_lru_set] <= wr_lru_val;
    end else if (fill_lru_req) begin
      lru_table[fill_lru_set] <= fill_lru_val;
    end
  end
end else begin : gen_lru_unused
  for (genvar s = 0; s < NUM_SETS; s++) begin : gen_lru_zero
    assign lru_table[s] = 1'b0;
  end
end
```

**Rationale:** Eliminates the large priority-mux cone in `lru_update_value`.
Each path is independent with minimal combinational logic. Adds one more cycle
of LRU latency (2 cycles total from access to table update).

**Risk:** Low - LRU accuracy slightly reduced for rapid same-set accesses.

**Verification:** Same as Stage 3.

---

## Signals Checklist

After all stages, these signals must NOT be in the `dmem_stall`/PC fanin:

| Signal                                 | Removed by |
| -------------------------------------- | ---------- |
| `evict_way` (from `addr_set`)          | Stage 3a   |
| `lru_table[addr_set]`                  | Stage 3a   |
| `way0_valid`/`way1_valid` for eviction | Stage 3a   |
| `fill_addr_set` (when state==IDLE)     | Stage 3c   |
| `fill_way`, `fill_beat_pending`        | Stage 3c   |
| `lru_update_value` mux                 | Stage 4    |

Signals expected in hit path (unavoidable):

- `rd_addr` → `addr_tag`, `addr_set`
- `tag_table[addr_set]` lookups
- `way0_hit`, `way1_hit`, `hit`
- `hit_data`
- `rd_data_valid_next` (minimal: `hit`, `rd_valid`, `state==IDLE`, `fill_done`)

---

## Execution Order

Pause after each stage for user to run tests and Vivado timing analysis.

1. **Stage 1+2** - Low risk cleanup
   - User runs: `make svc_cache_axi_tb` + Vivado timing
   - Confirm no regressions, check if timing path moves

2. **Stage 3 (3a+3b+3c together)** - Main timing fix
   - User runs: `make svc_cache_axi_f` + full dcache SOC testbenches + Vivado
   - Measure timing improvement

3. **Stage 4** - Optional, implement only if Stage 3 insufficient
   - User runs: same as Stage 3
