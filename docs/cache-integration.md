# Cache Integration Plan (I$ + D$ + AXI Arbiter)

This document describes an incremental plan to integrate `svc_cache_axi` as an
instruction cache (I$) and data cache (D$) behind a shared AXI arbiter, while
keeping debug/verification tight and isolating failures quickly.

## Why Split It Up

We saw a regression where cache-enabled sims diverge/hang while non-cache sims
pass. The quickest way to localize is to:

1. Prove the AXI arbiter path is correct with **only one cache active**.
2. Prove each cache works when it is the **only arbiter client**.
3. Only then enable **both** and debug any interaction (priority, fairness,
   write/read coupling, response routing, etc.).

This avoids debugging “I$ + D$ + arbiter + backing store” as a single blob.

## Branch / Main Workflow (Suggested)

1. **Create a working branch** from the current state (keep it as the “reference
   integration” branch for the I$ work, redirect handling, etc.).
2. **Reset `main`** to known-good commit:
   `d84b8020f80177d692de01c211b42fb92c1b6ada` (D$ was known-good before I$
   integration).
3. Re-introduce integration in small, verifiable steps (below), cherry-picking
   from the reference branch when appropriate.

## Step 0: Add Explicit Feature Switches

Add build-time parameters (preferred) to the cache SoC wrapper so we can test in
isolation without invasive diffs:

- `ICACHE_ENABLE` (default `0`)
- `DCACHE_ENABLE` (default `1`)

These should live in `svc/rtl/rv/svc_rv_soc_bram_cache.sv` and propagate down to
instantiation choices.

### Null/Stub Interfaces

When a cache is disabled, keep the arbiter interface shape intact using a “null
client” that:

- Never asserts `*_axi_*valid`
- Always deasserts `*_axi_*ready` where it is a manager-side ready
- Drives safe constant IDs/addresses/data/strb/last

This lets the arbiter remain a constant part of the design while enabling
single-client testing.

## Step 1: Arbiter + D$ Only (I$ Disabled)

Goal: Validate “D$ through arbiter to backing store” with no I$ present.

**Implementation sketch**

- Keep `svc_axi_arbiter` in the system, `NUM_M=2`.
- Connect D$ to one arbiter port (e.g. index 1).
- Connect a null client to the other port (e.g. index 0) in place of I$.
- Instructions come from a known-good path:
  - Option A (simplest): use a BRAM IMEM like `svc_rv_soc_bram` for instruction
    fetch (no I$).
  - Option B: keep the cache-style IMEM interface bridge but point it at a
    “direct memory” reader (more work, less reuse).

**Verification**

- Run `cd svc && make tb` after each change.
- Run a cache-enabled sim workload that stresses stores/loads (e.g. dhrystone)
  but with I$ disabled.
- Compare with the pre-arbiter baseline (trace-level if needed).

Exit criteria:

- D$ regression tests pass.
- No hangs/timeouts in the D$-only sim.

## Step 2: Arbiter + I$ Only (D$ Disabled)

Goal: Validate “I$ through arbiter to backing store” with no D$ present.

**Implementation sketch**

- Keep `svc_axi_arbiter`, `NUM_M=2`.
- Connect I$ to one arbiter port (e.g. index 0).
- Connect a null client to the other port (e.g. index 1) in place of D$.
- Data memory comes from a known-good path so programs still run:
  - Use the BRAM DMEM path from `svc_rv_soc_bram` (no D$), or
  - Keep the existing D$ interface bridge but bypass it to a BRAM (if address
    mapping needs to be preserved).

**Verification**

- `cd svc && make tb`
- Run a sim that is sensitive to front-end correctness (e.g. dhrystone, hello),
  with CPU tracing if needed.

Exit criteria:

- I$-only sims execute correctly (no wrong instruction fetch / PC mismatch).
- No regressions in formal/TB targets touched by these changes.

## Step 3: Enable Both I$ and D$ (Full Integration)

Goal: Combine both caches behind the arbiter only after each works alone.

**Integration checks**

- Confirm ID routing: `{grant_idx, axi_id}` tagging must round-trip correctly on
  both read and write responses.
- Confirm arbiter write-path invariants:
  - AW/W pairing is preserved per-client.
  - No cross-client W beats under a single AW.
- Confirm fairness/starvation expectations:
  - If I$ is strictly higher priority, ensure D$ still makes progress.

**Verification**

- `cd svc && make tb`
- Re-run the sim workloads:
  - `make rv_hello_cache_im_simi`
  - `make rv_dhrystone_cache_im_simi`
- Compare against non-cache traces where meaningful (use `rv_diff`).

Exit criteria:

- Cache and non-cache variants complete (no hangs).
- No architectural trace divergence before `main`.

## Debugging Hooks (Keep Small, Turnkey)

Prefer optional, plusarg-gated debug in the simulation harness:

- `+SVC_RV_DBG_CPU=1` (pipeline trace)
- `+SVC_AXI_TRACE` (AXI transaction tracing around a narrow address window)

Keep debug output gated and easy to enable/disable so it doesn’t pollute normal
logs.

## Notes / Practical Guidance

- If a failure reproduces only when both caches are enabled, prioritize proving:
  1. arbiter correctness (ID routing, AW/W coupling), then
  2. cache client behavior under backpressure/starvation.
- Avoid “semantic fixes” in the core pipeline until you can reproduce a minimal
  failing case under a single cache client; otherwise it’s too easy to mask the
  real integration fault.
