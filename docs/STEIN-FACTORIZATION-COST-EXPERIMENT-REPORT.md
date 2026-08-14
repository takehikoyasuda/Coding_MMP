# Stein Factorization Cost on a Genuine Divisorial Multigraded Contraction: Experimental Report

**Status**: Completed, negative result (new bottleneck located and root-caused to `res(nn,LengthLimit=>d1+d2+1)`; not fixed)
**Date**: 2026-08-14
**Work location**: Scratchpad only (no repo changes, no commits)
**Branch**: `feature/multigraded-stage1` (unchanged)

---

## Executive Summary

`docs/STAGE1-MEASUREMENT-RESULTS.md` measured `Bl_p(P3)` and Segre `P1 x P2` as
cheap (under 5 seconds each, full nef-through-contraction chain), multigraded
throughout. Both measurements used a polarization `w` that made the threshold
divisor either exactly zero (`Bl_p(P3)`, `w=O(1,1)=-K/2`, contracting straight
to a point and skipping Stein factorization entirely) or gave a small target
(`Segre`, `targetVariableCount=2`). Neither exercised Stein factorization on a
target with more than two variables.

This experiment deliberately chose a different, still-ample `w` on the same
`Bl_p(P3)` ring, designed by hand to hit the *other* boundary ray of the nef
cone -- the genuine divisorial contraction `E -> point` (blow-down to `P3`,
target dimension 3), instead of the degenerate apex-of-nef-cone point
contraction Stage 1 happened to land on. The nef test, threshold search, and
complete-linear-system graph construction all remained cheap, confirming the
hand computation exactly. But the next step -- Stein factorization itself,
specifically `steinHomData` -- did not complete in 30+ minutes on a graph with
29 variables and a 265-generator ideal, on a **smooth** ring with Cartier `K`,
with no reflexive-hull machinery involved at all. Root-caused (see "Root
cause" below): `steinHomData` must compute a free resolution up to
homological degree `d1+d2+1`, where `d1,d2` are one less than the source and
target variable counts -- i.e. a length that scales with **total variable
count**, not with the geometry of the contraction. On this input that length
is 28 in a 29-variable ring, essentially the maximum the Hilbert syzygy
theorem allows, and the resolution computation itself (not the subsequent
truncation/`Hom` step) is confirmed to already be catastrophic by homological
degree 4 -- far short of the 28 actually needed.

**This is a third, independent bottleneck**, distinct from both:
- the singular-target base-point-free/reflexive-hull bottleneck
  (`docs/STAGE2-MEASUREMENT-RESULTS.md`, [[bpf-construction-dominates-assessment]]);
- the monograded-flattening bottleneck (`docs/BOTTLENECKS-AND-MULTIGRADING.md`).

It hits precisely the case most wanted for a nontrivial multi-step smooth MMP
demonstration: a divisorial contraction whose target has more than a couple
of embedding coordinates.

---

## Setup

Exactly `docs/STAGE1-MEASUREMENT-RESULTS.md` section 1's `Bl_p(P3)` ring:

```m2
S = QQ[x0,x1,x2,x3,u0,u1,u2,
    Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
R = S/minors(2, matrix{{x1,x2,x3},{u0,u1,u2}});
```

`Bl_p(P3)` has Picard rank 2, nef cone the first quadrant in the `O(a,b)`
basis, bounded by `O(1,0)` (pullback of `O_{P3}(1)`, defines the blow-down
`E -> point`) and `O(0,1)` (defines the `P^2`-bundle structure map). Since
`K = -O(2,2)` (Fano index 2, as Stage 1 found), for `w=O(a,b)` the threshold
divisor `K+t*w` is nef exactly when `t >= max(2/a,2/b)`. Stage 1's choice
`a=b=1` hits both rays simultaneously (the apex), giving `K+2w=0` -- a trivial
target. Choosing `a != b` instead lands on exactly one ray. This experiment
used:

```m2
H = 2*divisor(x0) + divisor(u0);   -- w = O(2,1), a=2, b=1
```

predicting threshold `t* = max(2/2, 2/1) = 2`, with `K+2H` proportional to
`O(1,0)` (the blow-down ray), i.e. a genuine divisorial contraction with
3-dimensional target, exercising Stein factorization for real.

---

## Measurements

All cpu times from `cpuTime()`, single M2 1.26.06 process, Darwin arm64, same
machine as the Stage 1/2 reports.

| Stage | cpu time | Key output |
| --- | --- | --- |
| `canonicalNefData(R,1,H)` | 1.06s | `nef=false` (matches Stage 1's `w=(1,1)` figure almost exactly) |
| `canonicalNefThresholdData(R,1,H)` | 10.7s | `threshold=2`, matching the hand computation exactly |
| `isBasePointFreeDivisor(m*L)`, `L=K+2H`, `m=1..6` | 0.066s, 0.147s, 0.30s, 0.83s, 2.57s, 7.75s (≈12s total) | `bpf=true` already at `m=1` -- the internal multiplier-search loop exits immediately |
| `weilDivisorToModule(L)` alone | 0.0025s | trivially cheap; `L` has only 4 Weil-divisor terms |
| `diagonalSubalgebraData(R,H)` (the pre-Stein flattening) | 0.085s | 19 flattening variables (vs Stage 1's 9 for `w=(1,1)`) |
| `mapToProjectiveSpace(L)` (sections of the threshold divisor) | 0.040s | 10 sections (matches `h^0(O_{P3}(2))=10`: `L` restricts to the quadric Veronese of `P3`) |
| `completeLinearSystemGraphDataMultigraded(L,H)` | 0.53s | `sourceVariableCount=19`, `targetVariableCount=10`, `productRing` 29 variables, `graphIdeal` 265 generators |
| `steinHomData(productRing, graphIdeal)` | **did not complete**; killed after 30+ minutes cpu time, memory climbing to 7.5GB | no output |
| `steinCoordinateAlgebra`, `directSteinGraph` | **not reached** | blocked on `steinHomData` |
| `canonicalContractionData(R,1,H)` (the full pipeline, run first, before decomposing) | **did not complete**; killed after ~19 minutes cpu time (~18-19 min elapsed), memory ~6-7.7GB, non-monotonic (consistent with active computation, not a deadlock) | confirmed reproducing the same stall as the isolated `steinHomData` call |

Every stage up to and including complete-linear-system graph construction is
cheap -- comparable to or only modestly more expensive than Stage 1's
already-measured examples. `steinHomData` alone accounts for the entire
multi-minute-to-unbounded stall.

### A methodological note: M2 `--script` output buffering

The first run of the full pipeline appeared to hang with **zero** output for
over an hour, which briefly looked like it might itself be the finding. It
was not: M2's `--script` mode block-buffers `stdio` when redirected to a
file (confirmed directly with a busy-loop test: a `print` issued before a
`2*10^9`-iteration loop does not appear in the redirected output file until
the process exits or `flush stdio` is called explicitly after the `print`).
Every timing in this report was obtained only after inserting `flush stdio`
after each `print`, which is why the per-stage breakdown above was possible
at all. Any future timing experiment redirecting M2 `--script` output to a
file should insert `flush stdio` after each progress `print`, or the absence
of output cannot be distinguished from a genuine stall.

---

## Root cause: the resolution length needed to certify the truncation bound

`steinHomData`'s own source
([SteinFactorization.m2:156-192](../third_party/SteinFactorizationM2/SteinFactorization.m2#L156-L192))
shows the mechanism precisely. It computes a free resolution up to a
homological degree fixed by the ambient ring's block sizes, uses that
resolution to certify a bigraded truncation bound (`bigradedTruncationBound`,
the paper's Corollary 4.3), then truncates and takes `Hom`:

```m2
bd := blockDegreeData ambient;              -- (d1,d2,c1,c2)
maxHomologicalDegree := d1+d2+1;            -- NOT a free choice
ff := res(nn,LengthLimit=>maxHomologicalDegree);
bound := bigradedTruncationBound(ff,d1,d2,c1,c2);
truncation := truncate(bound,rr^1);
rawHomModule := Hom(truncation,rr^1,MinimalGenerators=>true);
```

`d1 = sourceVariableCount-1`, `d2 = targetVariableCount-1`, so
`maxHomologicalDegree` grows linearly with the **total variable count** of
the product ring, not with anything about the geometry of the contraction
itself. Measured directly on this experiment's graph
(`sourceVariableCount=19`, `targetVariableCount=10`, 29 variables total):

| Quantity | Value |
| --- | --- |
| `blockDegreeData` | `d1=18, d2=9, c1=19, c2=10` |
| `maxHomologicalDegree` (`d1+d2+1`) | **28**, in a **29-variable** ring |

By the Hilbert syzygy theorem, projective dimension over a 29-variable
polynomial ring is at most 29 -- so `steinHomData` is asking, on this input,
for a free resolution of nearly maximal possible length before it can even
state the truncation bound it needs. Compare Stage 1's Segre example
(`sourceVariableCount=6`, `targetVariableCount=2`, 8 variables total):
`d1=5, d2=1, maxHomologicalDegree=7` -- a resolution well short of that
ring's own 8-variable syzygy ceiling, which is exactly why it was cheap
(0.062s total for Stein factorization there).

Isolating the resolution call itself confirms the growth is not gradual:

| `res(nn, LengthLimit=>k)` | cpu time |
| --- | --- |
| `k=2` | 1.94s |
| `k=4` | **did not complete**; killed after 34 min elapsed / 93 min cpu time (multi-threaded), memory 8.7GB |

So the blowup is not a slow climb toward `k=28` -- it is already
catastrophic by `k=4`, a small fraction of the way to the `28` that
`steinHomData` actually needs. The truncation bound's *value* was never
reached or measured; the free resolution required to *certify* it is what
fails first, and it fails at a homological degree far below the nominal
target. This directly confirms the diagnosis: the cost is driven by the
resolution-length parameter `d1+d2+1` scaling with total variable count, on
a 265-generator ideal that is evidently not sparse/structured enough for
Macaulay2's resolution algorithm to stay cheap anywhere near that length.

---

## Interpretation

`steinHomData` computes the paper's bigraded global Hom (`B tensor C^[k] ->
R_gamma`, see `README.md`'s "Stein graph status" and
`docs/IMPLEMENTATION-STATUS.md`'s paper-to-code map). Stage 1's two measured
inputs never genuinely exercised this construction at a nontrivial size:
`Bl_p(P3)` with `w=(1,1)` skipped it outright (`targetVariableCount=1`, the
"trivial point target" shortcut in `canonicalContractionAtThresholdDataCore`,
[MMPComputation.m2:1004-1017](../MMPComputation.m2#L1004-L1017)); Segre
`P1xP2` reached it but with a much smaller graph (`targetVariableCount=2`,
hence a much smaller `productRing`/`graphIdeal` than this experiment's 29
variables / 265 generators). This experiment is the first measurement of
`steinHomData`'s cost on a graph of realistic size for a genuine multi-section
divisorial contraction, and it is severe: unresolved after 30+ minutes, on a
**smooth** input with `K` Cartier at index 1, with no reflexive hull or
singular-variety machinery involved anywhere in the chain up to this point.

This means the multigraded-first design's own remaining-bottlenecks list in
`docs/MULTIGRADED-DESIGN.md` ("relative canonical models via Rees algebras,
ring growth after flips...") was, if anything, optimistic: ring growth at the
Stein-factorization interface is already a live problem *before* any flip or
relative model is involved, as soon as the target of a divisorial contraction
has more than a couple of embedding coordinates. Both of Stage 1's example
inputs avoided this by construction (one trivially, one by having a small
target), not because the underlying construction is generically cheap.

## What this does and does not establish

**Establishes:**

- A third, independent bottleneck site, distinct from the singular-target
  reflexive-hull cost ([[bpf-construction-dominates-assessment]]) and from
  monograded flattening (`docs/BOTTLENECKS-AND-MULTIGRADING.md`): the
  bigraded global Hom construction (`steinHomData`) itself, on a smooth,
  Cartier-index-1 input, once the contraction's target has enough embedding
  coordinates (here 10 sections, 29-variable product ring, 265-generator
  graph ideal).
- That every stage up to and including graph construction remains cheap
  (well under a second to ~12 seconds) for this input, so the stall is
  narrowly localized to `steinHomData`, not to the nef/threshold/bpf/
  flattening machinery Stage 1 already validated.
- That the hand computation predicting the threshold (`t*=max(2/a,2/b)=2`
  for `w=O(2,1)`) was exactly confirmed, and that the resulting divisor is
  genuinely base-point-free at multiplier 1 with 10 sections restricting to
  the quadric Veronese of `P3` -- i.e., the intended geometric target (a real
  divisorial contraction, not a degenerate point) was correctly reached at
  the algebra level; only the subsequent Stein-factorization step is
  unresolved.

- *Why* `steinHomData` scales this badly with variable count, localized to
  the specific mechanism: `maxHomologicalDegree = d1+d2+1` grows linearly
  with total product-ring variable count (source + target), asking for a
  free resolution approaching the Hilbert-syzygy ceiling of that ring
  (28 out of a possible 29 here); and the resolution computation itself,
  not the subsequent truncate/Hom step, is confirmed as the actual site of
  the blowup, already catastrophic by homological degree `k=4` (34+ minutes
  elapsed, killed) versus `k=2`'s 1.94s. Segre's cheap case
  (`maxHomologicalDegree=7` in an 8-variable ring) never approached its own
  ring's syzygy ceiling, which is why it stayed cheap.

**Does not establish:**

- Why the resolution itself grows so sharply between `k=2` and `k=4` in
  Macaulay2's implementation terms (which Betti numbers explode, or whether
  a different resolution strategy/algorithm choice would fare better) --
  that would require profiling Macaulay2's `res` internals themselves, not
  just this package's use of them, and was not attempted.
- Whether a different choice of `w` closer to the `O(1,0)` boundary (e.g.
  larger tilt ratios) would give a threshold divisor with *fewer* sections
  and a correspondingly cheaper `steinHomData` call, or whether the generator
  count is essentially forced by the geometry (10 sections is exactly
  `h^0(O_{P3}(2))`, the smallest very ample multiple of the pullback
  polarization reachable at this threshold; a smaller number of sections may
  not be achievable at *any* `w` giving this particular contraction).
- Whether this cost is specific to `Bl_p(P3)` and this particular `w`, or is
  a general property of `steinHomData` whenever the target embedding needs
  more than a handful of coordinates. No second example was tested.

## Suggested next steps (not attempted here)

- Localized further than originally planned: the site is confirmed to be
  `res(nn,LengthLimit=>k)` itself, already catastrophic by `k=4` of the 28
  `steinHomData` asks for. Profiling Macaulay2's own resolution algorithm on
  this specific 265-generator/29-variable ideal (which Betti numbers are
  large, whether a different strategy such as `FastNonminimal` or computing
  over a smaller residue field helps) is the natural continuation, distinct
  from (and more specific than) generically "profiling `steinHomData`".
- Since `maxHomologicalDegree = d1+d2+1` scales with **total product-ring
  variable count** (`sourceVariableCount+targetVariableCount`), reducing
  either side would directly lower the resolution length demanded, not just
  the generator count of the graph ideal. `sourceVariableCount` comes from
  `diagonalSubalgebraData`'s flattening of `w` (19 here, vs Stage 1's 9 for
  `w=(1,1)`) and `targetVariableCount` from the number of sections of the
  threshold divisor (10 here, `h^0(O_{P3}(2))`). Whether a `w` exists that
  reaches a genuine (non-point, non-tiny) divisorial contraction with a
  smaller combined variable count was not investigated.
- For a near-term "prove the program works on a nontrivial smooth example"
  goal, prefer examples that stay Picard-rank-one (single contraction to a
  point, never exercising Stein factorization on a nontrivial target) over
  further multi-step smooth blow-up/blow-down chains, until this bottleneck
  is either fixed or better characterized.
