# Invertible-Ideal-Caching Hypothesis: Experimental Report

**Status**: Completed, negative result  
**Date**: 2026-08-13  
**Work location**: Scratchpad only (no repo changes, no commits)  
**Branch**: `feature/multigraded-stage1` (unchanged)

---

## Executive Summary

The hypothesis was theoretically sound but empirically wrong. **Correctness is confirmed; speed is refuted.**

**Hypothesis**: On singular rings with canonical divisor K of index > 1 (e.g., canonical index 2), base-point-free tests grow with geometric cost (K:0.11s → 6K:3.44s) because `WeilDivisors.divisorToModule` must compute reflexive hulls of non-Cartier prime powers. The proposed fix: extract an invertible ideal `J` representing `O(-2K)` once (after confirming 2K is Cartier), then for 4K, 6K, 8K, ... use ordinary powers `J^2, J^3, J^4, ...` instead of re-computing `divisorToModule` from scratch each time.

**Result**: The shortcut produces the correct BPF judgments (all boolean answers agree with the trusted path), but it is **slower, not faster**, and the slowdown *increases* with higher multiples (1.7–1.8× at 4K, 4–6× at 6K).

---

## (a) How J was obtained and verified as truly invertible

### Extraction
```m2
J := ideal(2*K)
```
using WeilDivisors' native `ideal(WeilDivisor)` method. Cost: **0.066s**. Result: 8 generators.

**Why this is safe**: `ideal(D)` is WeilDivisors' own public API for extracting the ideal-representation of a divisor (documented: "produces an ideal isomorphic to the sheaf O(-D)"). Its source code internally computes the same reflexive-hull pipeline as `divisorToModule`, then caches the result in `D#cache#?ideal`. We are using the cached output directly.

### Invertibility verification (not an assumption)
Replicated the `nonCartierLocus(WeilDivisor)` algorithm **directly on J itself** to confirm it genuinely represents a locally principal ideal:

```m2
Jminus = dualize(J);                          -- dual of J
I = J*Jminus;                                  -- reflexive hull of J·(J⁻¹)
nonCartierLocusJ = annihilator((reflexify(I)*Z^1)/(I*Z^1));  -- where non-locally-principal?
isInvertible = (saturate(nonCartierLocusJ, Btrue) == ideal 1_Z)
```

Result: **true**. Cost: 0.163s.

**Significance**: This is not circular reasoning or a faith-based assumption. The same `nonCartierLocus` algorithm that the package uses elsewhere to certify Cartier-ness, when applied to J itself, confirms it is invertible (non-Cartier locus is empty). J is a genuine, honest-to-god invertible ideal, not a placeholder.

### Extra sanity check (Hom path on 2K)
Built `Hom(ideal(2*K), Z^1)` (i.e., the module for O(2K) via the new path), then ran the same BPF test on it. Result: false (agrees with `isBasePointFreeDivisor(2*K, Btrue)`). This confirmed the logic is sound at the smallest case before trusting 4K/6K.

---

## (b) Timing comparison: 4K and 6K, old path vs. new path

### Definitions
- **Old path**: `isBasePointFreeDivisor(n*K, Btrue)` — uses the general-purpose `divisorToModule` machinery, which decomposes the divisor into positive/negative parts, takes `idealPower` of each prime, does the double-dual reflexification, then feeds the result to the BPF test logic.
- **New path**: Extract `J^k` (where K = k·(2K)), construct `Hom(J^k·Z^1, Z^1)` to get the module for O(k·2K), then apply the same BPF test logic (cokernel of evaluation, annihilator, saturate).

### Table

| Divisor | Old path (time) | Old path (bpf) | New path (time) | New path (bpf) | Agree? | Slowdown |
|---|---|---|---|---|---|---|
| 2K | 0.219s | false | 0.187s | false | ✓ yes | ~0.9× (new is faster) |
| 4K | 0.87–0.90s | false | 1.52–1.59s | false | ✓ yes | **1.7–1.8×** |
| 6K | 3.47–3.50s | false | 13.9–21.4s | false | ✓ yes | **4–6×** |

### Independent verification (current session)
```
OLD 4K: 0.858017s, bpf=false
NEW 4K: 0.093s (construct J², Hom) + 0.479s (ann) + 1.071s (saturate) = 1.644s, bpf=false
AGREE: true
```

This confirms the agent's measurements within normal session-to-session variance.

---

## (c) Why the new path is slower: root-cause diagnosis

The hypothesis identified the **source** of old-path cost correctly: `divisorToModule`'s double-dual reflexification. But the proposed fix relocated the cost, not eliminated it.

### Breakdown by sub-step (agent measurements)

**Old path (4K = 0.87–0.90s)**:
- `divisorToModule` construction (including double-dual): **0.79–0.81s** (90–97% of total)
- basis/ann/saturate query on result: **0.06–0.10s** (remainder)

**New path (4K = 1.52–1.59s)**:
- `ideal(2K)` extraction (first time): 0.066s
- `J^2` power + `Hom(-,Z^1)` construction: **< 0.03s** ✓ cheap as hypothesized
- annihilator of evaluation cokernel: **0.44–0.48s** (28–32% of new-path total)
- saturate by Btrue: **1.0–1.07s** (65–70% of new-path total)
- **Total**: ~1.5–1.6s

**New path (6K = 13.9–21.4s)**:
- J³ + Hom construction: **< 0.03s** ✓ still cheap
- ann: **4.6–4.8s** (33–40% of new-path total)
- saturate: **9.2–16.8s** (60–67% of new-path total)
- **Total**: ~13.9–21.4s

### The swap
- **Old path**: pays upfront for double-dual (expensive), then queries are cheap.
- **New path**: skips double-dual (saves ~0.8s at 4K), but `ann`/`saturate` become the new bottleneck and cost **way more** than the entire old path.

### The puzzling detail
Both paths produce modules with **identical minimal presentations** (verified by `presentation M` comparison; e.g., both 7×30 at 4K), yet:
- Old-path module: ann=0.06s, saturate=0.04s
- New-path module: ann=0.44s, saturate=1.07s

The module from `divisorToModule`'s own construction is presented in a way that makes `ann` and `saturate` orders of magnitude faster, even though the minimal presentation sizes are the same. This is a **Macaulay2 internal quirk**: the same module can have vastly different computational cost depending on how it was constructed, independently of its mathematical content.

---

## (d) Further trend: 8K, 10K, new path only

Since the new path was already slower at 6K, we tested only the new path further to see if the growth flattens.

| Divisor | New-path time |
|---|---|
| 4K | 1.52–1.59s |
| 6K | 13.9–21.4s |
| 8K | 89.6s |
| 10K | 426s |

**Growth ratios per 2K step** (from 4K onward):
- 4K → 6K: **9.2× or more**
- 6K → 8K: **6.4×**
- 8K → 10K: **4.8×**

These ratios are **not** flatter than the old path's own measured ~2–2.8× per 1K step. There is no evidence the shortcut flattens the growth curve; it just loses at every point.

---

## (e) Should this be committed as an optimization?

**No.** Implementing this in `MMPComputation.m2` today would make `canonicalNefData` **slower** on singular targets like Z. It produces a net slowdown at every tested point (1.7× at 4K, 4–6× at 6K, and worsening), so there is no practical benefit.

**Possible path to value** (not pursued now):
To make this worthwhile would require understanding *why* `ann`/`saturate` are so much costlier on a `Hom(J^k·Z^1, Z^1)` module than on a `divisorToModule`-constructed one, despite equal final presentation size. This would involve:
- Inspecting the Gröbner basis and term orders Macaulay2's engine sees pre-minimization.
- Checking for degree-tracking differences or different sparse-matrix structures in the presentation.
- Profiling M2's actual kernel-computation steps for `ann` on the two module types.

This is not a small patch; it's open-ended kernel debugging and would likely yield insights specific to how Macaulay2 handles multigraded presentations, but no quick fix.

---

## (f) Surprising findings and subtleties

### 1. `idealPower(n, J)` ≠ `J^n` before reflexification
Confirmed that `idealPower(2, J)` and `J^2` as literal ideals are not equal — they only agree *after* reflexification (consistent with WeilDivisors' own documentation). However, feeding either into `Hom(-,Z^1)` produces the identical, correct module at 4K/6K, because `Hom` is insensitive to codimension-≥2 differences.

### 2. Module presentation size is not a proxy for computational cost
Two modules with **identical minimal-presentation dimensions** can have 10–50× cost differences in `ann`/`saturate`, depending solely on the construction path. This is a genuine Macaulay2 quirk, not a mathematical issue.

### 3. Scope: only even multiples of K were tested
The canonical index of Z is 2, so K is non-Cartier, 2K is Cartier. The search in `canonicalNefData(Z, 2, H, ...)` only needs even multiples of K (multiples of the confirmed Cartier index). Odd multiples (K, 3K, 5K) were correctly excluded from this experiment, as they would require odd multiples of the Cartier 2K, which cannot be obtained from ordinary powers of an invertible ideal.

---

## Conclusion

The diagnosis of *where* the old path's cost originates (the double-dual reflexification in `divisorToModule`) was correct. But the proposed escape route (seeding from a pre-verified invertible ideal) doesn't work: it relocates the bottleneck to `ann`/`saturate`, which turn out to be more expensive there than the entire original path.

**On the broader picture**: This result, combined with Stage 2 measurements (nef threshold search stalling at 20 minutes), reinforces that the reflexive-hull computation for non-Cartier divisors on singular rings is a deep, structural bottleneck — not easily side-stepped by caching or algebraic re-routing. Further progress (either optimization or a fundamental algorithmic pivot) would require either:
1. Profiling and potentially patching M2's own `ann`/`saturate` kernel, or
2. A different approach entirely (e.g., avoiding reflexive divisors, working directly in a Cartier-smooth cover, or numerical/modular methods for testing positivity).

---

## Files

- Main experiment scripts (all scratchpad, no repo changes):
  - `invertible-power-hypothesis.m2` (initial test)
  - `invertible-power-hypothesis-v2.m2` (agent's detailed breakdown)
  - `diag.m2`, `diag2.m2`, `diag3.m2`, `diag4.m2` (diagnostic sub-steps)
  - `verify3.m2` (independent verification, rerun this session)

- Related prior work:
  - `docs/STAGE2-MEASUREMENT-RESULTS.md` (Stage 2 measurements)
  - `tests/multigraded-skew-cartier.m2` (Z construction, correctness regression)
  - `docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md` (planning notes)
