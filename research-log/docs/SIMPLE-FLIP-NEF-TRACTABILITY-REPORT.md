# Does Singular BPF/Nef Testing Stay Tractable for the Simplest Flip Singularities?

**Status**: Confirmed, positive but partial: nef testing completes (~530s) on flip targets with only one simple (index-2) singular point, unlike the previously measured rank-2 canonical-index-2 example (never completed after 20+ minutes). Four candidates tried in total: two gave genuine, comparably cheap flips both landing on `nef=false` at near-identical cost (529.75s and 509.4s), one was accidentally Gorenstein (no flip to study), one had an expensive flip computation itself (killed after 10+ minutes). No candidate reached `nef=true`; a "one flip, then minimal model" example was not found within this one 4-ray-circuit family, suggesting the compactification method itself, not just the ray choice, needs rethinking.
**Date**: 2026-08-14
**Work location**: Scratchpad only (no repo changes to `MMPComputation.m2`/`FlipComputation`); reuses `tests/relative-model.m2`'s existing toric-circuit construction verbatim
**Branch**: `feature/multigraded-stage1` (unchanged)

---

## Executive Summary

`STAGE2-MEASUREMENT-RESULTS.md` found that `canonicalNefData` on a singular,
rank-2 multigraded, canonical-index-2 toric flip target did **not** complete
after 20+ minutes, with individual base-point-free tests already costing
multiple seconds at low degree. That example was a genuine but not
necessarily minimal worked case (built via `computeFlip` on a specific
non-Q-Gorenstein toric base with several complicating factors: rank-2
grading, a "skew" fibre structure requiring careful `IrrelevantIdeal`
threading).

This experiment asks a narrower, sharper question: is the underlying cost
already bad for the *theoretically simplest possible* case a threefold
flip can present, or is Stage 2's severity specific to that more
complicated setup? Mori-theoretic background motivates a precise notion of
"simplest": a genuine (non-crepant, `K`-negative) 3-fold flip requires
non-Gorenstein singularities (index >= 2) on at least one side -- Gorenstein
terminal singularities admit only *flops* (crepant small resolutions), not
flips, so the historically first and simplest known example (Francia's
flip) has index-2 (`1/2(1,1,1)`-type) points.

**Finding**: `tests/relative-model.m2`'s existing toric-circuit example
(`rayList = {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}}`), already used there purely
to test `computeFlip`/`relativeCanonicalModelFromBaseData` in isolation,
turns out by direct chamber-determinant computation to have exactly this
"simplest possible" shape: the pre-flip side is entirely smooth, and the
flip target has a single simple singular point. Running the **full**
`canonicalNefData` search (not tested in the existing test file, which
only exercises the flip computation itself) on the flip target completes in
**529.75 seconds** (~8.8 minutes), reporting `nef=false` -- a real,
definitive result, categorically different from Stage 2's never-terminating
20+-minute stall on its own more complex example.

**What this does not yet give**: `nef=false` means this particular flip
target is not itself a minimal model. A complete "one flip, then minimal
model" demonstration needs a *different* (but comparably simple) example
where the post-flip `nef` test succeeds. That search is the natural next
step (see "Suggested next steps").

---

## Background: why index-2 is the simplest possible genuine flip

A **flip** replaces a `K`-negative small extremal contraction `X -> W`
(where `W` is not Q-factorial) with a *different* small contraction
`X^+ -> W` such that `K_{X^+}` is relatively ample. A **flop** is the
special (`K`-trivial) case where the contracted curve has `K.C = 0`, e.g.
the classical Atiyah flop of an ordinary double point (already touched, at
the level of a bare small-resolution smallness check, by
[tests/contraction.m2](../tests/contraction.m2)'s `ODP` example).

A standard fact in Mori theory: a small contraction centered at a
**Gorenstein** (index-1) terminal point automatically has `K.C = 0` on the
contracted curve -- i.e. Gorenstein small contractions are always flops,
never genuine flips. A *genuine* flip therefore requires a non-Gorenstein
(index >= 2) point on at least one side. The historically first known
example, **Francia's flip**, realizes the minimal case: index-2
(`1/2(1,1,1)`-type) quotient singularities. This project already measured
this exact singularity type once before, in a different context
([[section-oracle-design-refuted]] / `CYCLIC-QUOTIENT-CHARACTER-EXPERIMENT-REPORT.md`):
the relevant reflexive-hull correction term grows only *cubically* in the
tested multiple there, far milder than whatever drove Stage 2's example to
never terminate -- motivating the hope that a flip built from only this
mild singularity type might stay computationally tractable end to end.

## Setup: the existing toric circuit, reinterpreted

`tests/relative-model.m2` already builds and verifies (at the level of
`computeFlip`/`relativeCanonicalModelFromBaseData` alone, not through the
top-level nef/threshold machinery) the flip of a toric circuit with four
rays:

```m2
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
```

These four rays in a rank-3 lattice admit exactly one relation,
`2*v3 + v4 = v1 + v2`, giving two possible triangulations ("chambers") of
the cone they span:

- **Chamber A** (ridge `{v3,v4}`): maximal cones `{v1,v3,v4}`, `{v2,v3,v4}`.
- **Chamber B** (ridge `{v1,v2}`): maximal cones `{v1,v2,v3}`, `{v1,v2,v4}`.

Direct computation of each maximal cone's determinant (its index as a
cyclic quotient singularity, `|det|=1` meaning smooth):

| Cone | `det` | Singularity |
| --- | --- | --- |
| Chamber A: `{v1,v3,v4}` | `-1` | smooth |
| Chamber A: `{v2,v3,v4}` | `1` | smooth |
| Chamber B: `{v1,v2,v3}` | `1` | smooth |
| Chamber B: `{v1,v2,v4}` | `-2` | **index 2** |

So Chamber A is **entirely smooth**, and Chamber B has exactly **one**
simple index-2 quotient-singular point (the other cone in Chamber B stays
smooth). `relativeCanonicalModelFromBaseData` computes the flip (the
`K`-relatively-ample side) from the common non-Q-Gorenstein base `W`
(the affine cone over all four rays); this is exactly Chamber B, confirmed
directly (see Measurements). This is precisely the "one side smooth, other
side has only a simple singularity" shape asked for -- not by construction
of a new example, but recognized in one this project had already built and
partially tested for a different purpose.

## Measurements

All cpu times from `cpuTime()`, single M2 1.26.06 process, Darwin arm64,
same machine as the Stage 1/2 reports.

### Building the flip target

```m2
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");

rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
S = QQ[y_1 .. y_(#HB),w];
W = S/sub(I0,S);
flipModel = relativeCanonicalModelFromBaseData(W,RelativeCanonicalMultipliers=>{1});
Xplus = flipModel#"relativeModelRing";
```

| Quantity | Value |
| --- | --- |
| `relativeCanonicalModelFromBaseData` cost | 0.22s |
| `dim Xplus` | 4 (projective threefold) |
| `degreeLength Xplus` | 1 (**monograded** -- no multigraded machinery needed at all) |
| `numgens Xplus` | 12 |
| `canonicalDivisor` cost | 0.80s |
| canonical index found | **`a=1`** (`K` itself is already Cartier -- simpler even than the index-2 local picture might suggest, presumably because the ambient presentation absorbs the local index into a Cartier combination globally) |

### Individual base-point-free tests at increasing multiples of `K`

Mirroring the Stage 1/2 measurement style:

| `n` | cpu time | `bpf` |
| --- | --- | --- |
| 1 | 0.42s | false |
| 2 | 0.75s | false |
| 3 | 1.39s | false |
| 4 | 2.40s | false |
| 5 | 3.90s | false |
| 6 | 6.08s | false |
| 7 | 9.92s | false |
| 8 | 14.77s | false |

Growth is geometric, ratio roughly 1.5-1.85x per step -- comparable in
*character* to Stage 2's own per-step growth (which was also roughly
geometric), and **not obviously milder in absolute terms**: at `n=6` this
example costs 6.08s versus Stage 2's 3.44s at the same `n` -- slightly
*worse*, not better, degree for degree. The "simple singularity" hope is
not confirmed at the level of individual-test cost; the difference shows
up elsewhere (see next result).

### The full nef search

```m2
nefData = canonicalNefData(Xplus,1);
```

| Metric | Value |
| --- | --- |
| cpu time | **529.75s** (~8.8 minutes) |
| memory | grew to ~2.1GB during the run, did not run away further |
| result | `nef = false` |

This **completed**, categorically unlike Stage 2's own full-search attempt
(`canonicalNefData(Z,2,H,...)`, killed after ~20 minutes with no result at
all). Despite individual-test costs being comparable or slightly worse
degree-for-degree, the *aggregate* search here stayed within a bounded,
completable envelope -- plausibly because this input's canonical index is
1 (not 2), a single grading (`degreeLength=1`, no multigraded
`IrrelevantIdeal`-threading overhead or "wrong `B`" risk at all, per
[[stein-factorization-cost-bottleneck]]'s and Stage 2's own findings about
multigraded complications), and/or because the alternating search here
happened to need fewer or smaller-degree candidates before concluding
`nef=false` than Stage 2's search needed before being killed still
inconclusive.

---

## Interpretation

**The tractability hypothesis is confirmed, with a caveat.** A flip target
built from the theoretically simplest possible non-Gorenstein singularity
configuration (one index-2 point, otherwise smooth, monograded
presentation) lets the full `canonicalNefData` search **complete** in well
under 10 minutes -- a categorically different outcome from the previously
measured rank-2, canonical-index-2, "skew"-multigraded example that never
completed after 20+ minutes. This is genuine evidence that singularity
*complexity* (multigraded rank, canonical index, "skew" fibre structure),
not merely "being singular at all," is what drives the earlier
never-terminating behavior.

**The caveat**: this specific flip target is not itself a minimal model
(`nef=false`). It demonstrates computational tractability, not yet a
complete "one flip, then minimal model" MMP example. Individual
base-point-free test costs were *not* dramatically better than Stage 2's
(same order of magnitude, same qualitative geometric growth) -- what
changed was that the *aggregate* alternating search terminated at all,
which is the property that actually matters for the top-level driver.

## What this does and does not establish

**Establishes:**

- A concrete, already-existing-in-this-repo example (`tests/relative-model.m2`'s
  toric circuit) has, by direct chamber-determinant computation, exactly
  the "one side smooth, other side one simple singular point" shape
  motivated by Mori-theoretic first principles (Gorenstein points only
  give flops; the simplest genuine flip needs index >= 2).
- On this example's flip target, the full `canonicalNefData` search
  completes (529.75s), unlike the previously measured, more complex
  singular example (20+ minutes, never completed).
- Individual base-point-free test costs at low degree are *not* obviously
  better on this simpler input -- the improvement is in the aggregate
  search terminating, not in per-test cost.

**Does not establish:**

- A complete "one flip, then minimal model" MMP example -- this flip
  target has `nef=false`, so further MMP steps would be needed from here,
  not just this one flip.
- *Why* the aggregate search here terminates while Stage 2's did not,
  precisely -- plausible contributing factors (canonical index 1 vs 2,
  monograded vs multigraded-with-skew-fibres) are named but not isolated
  by a controlled comparison.
- Whether this specific toric family (or a close relative, e.g. a
  different ray configuration with the same "one smooth side, one
  simple-singular side" shape) can be tuned to reach `nef=true` after the
  flip, giving the complete example originally wanted. This is the natural
  next experiment.
- Whether the pre-flip side (Chamber A, entirely smooth) can be connected
  to this flip target through the top-level driver automatically (as was
  done for `Bl_p(P3)` in the Stein-factorization capstone), rather than only
  exercising the flip computation and post-flip nef test in isolation as
  done here.

---

## A search for a `nef=true` variant: two more candidates tried, neither conclusive

Immediately after the result above, two further ray configurations
(varying only `v4`, keeping `v1,v2,v3` as the standard basis) were tried,
looking for a comparably simple circuit whose flip target reaches
`nef=true`. Neither succeeded, for two different, informative reasons.

### A useful diagnostic found along the way: a one-line Gorenstein test

For `v1=e1,v2=e2,v3=e3` and `v4=(p,q,r)`, the cone over all four rays is
Gorenstein (index 1, hence -- per the "Background" section above -- giving
at best a *flop*, or even a fully trivial relative model, never a genuine
flip) **exactly when `p+q+r=1`**: Gorenstein-ness needs a single integral
linear functional `m` with `m.v_i` constant across all four rays, and for
the standard-basis `v1,v2,v3` this forces `m=(c,c,c)`, giving
`m.v4=c(p+q+r)`, equal to `c` (the same constant) iff `p+q+r=1`. This is a
free, instant sanity check before spending any real computation on a
candidate.

### Candidate 2: `v4=(1,2,-2)` -- accidentally Gorenstein, no flip at all

Chamber determinants: `{v1,v3,v4}=-2` (index 2), `{v2,v3,v4}=1` (smooth);
`{v1,v2,v3}=1` (smooth), `{v1,v2,v4}=-2` (index 2) -- by the local
combinatorics alone this looked like an even *more* symmetric version of
the working example (one simple singular point on **each** side, matching
Francia's flip's classical symmetric shape). But `p+q+r=1+2-2=1`: this
configuration is Gorenstein. Confirmed directly:
`relativeCanonicalModelFromBaseData` returned `relativeModelType="identity"`
in 0.0028s, `numgens Xplus=5` (versus 12 for the working example) -- no
genuine flip is needed at all here; the relative canonical model is
trivial. This is a clean illustration of the Background section's
theorem in action: simple local singularity data is not sufficient on its
own, the *global* Gorenstein-defect of the full 4-ray cone must also be
nonzero, or there is no flip to study.

### Candidate 3: `v4=(1,2,-3)` -- non-Gorenstein, but the flip computation itself did not finish

Chamber determinants: `{v1,v3,v4}=-2` (index 2), `{v2,v3,v4}=1` (smooth);
`{v1,v2,v3}=1` (smooth), `{v1,v2,v4}=-3` (index 3) -- non-Gorenstein
(`p+q+r=1+2-3=0 != 1`), one simple singular point on each side (index 2 and
index 3 respectively), asymmetric but still individually simple. Unlike
the working example (whose entire `relativeCanonicalModelFromBaseData` call
cost 0.22s) or candidate 2's instant identity verdict, this one did not
complete: killed after 10+ minutes elapsed (~7.5 minutes cpu, memory
climbing to ~800MB, still rising) with only the Hilbert-basis computation
(size 6, versus size 4 for candidate 2 and an unrecorded but evidently
larger basis for the working example) having printed -- the flip
computation itself, not even the subsequent nef search, was the bottleneck
here. Not profiled further; this is a genuine, if unexplained, cost
increase from swapping one `v4` coordinate (`-2` to `-3`), not a
resolution-length-style mechanism identified the way `steinHomData`'s was.

### Where this leaves the search

Two data points is not enough to characterize what makes
`relativeCanonicalModelFromBaseData`/`computeFlip` itself expensive on an
otherwise-simple-looking circuit (candidate 3 versus the cheap working
example and candidate 1), nor to find a `nef=true` case. The Gorenstein
one-line check at least rules out an entire class of degenerate
non-candidates (like candidate 2) for free, before spending any real
computation.

### Candidate 4: `v4=(2,1,-1)`, the mirror of the working example -- also `nef=false`, essentially identical cost

Chamber determinants: `{v1,v3,v4}=-1` (smooth), `{v2,v3,v4}=2` (index-2);
`{v1,v2,v3}=1` (smooth), `{v1,v2,v4}=-1` (smooth); `p+q+r=2+1-1=2 != 1`
(non-Gorenstein) -- structurally the same shape as the working example
(one side entirely smooth, the other with exactly one index-2 point), with
the singular chamber swapped. This one *did* behave comparably cheaply:
`relativeCanonicalModelFromBaseData` in 0.23s (`relativeModelType=
"computed"`, a genuine flip), `numgens Xplus=12`, monograded, canonical
index `a=1` -- essentially identical shape to the working example.

The full `canonicalNefData(Xplus,1)` completed in **509.4s**, reporting
**`nef=false`** -- again, not a minimal model. The near-identical cost
(509.4s vs. the working example's 529.75s, a ~4% difference) across two
independently chosen, only-mirror-related configurations is itself a
notable, if negative, finding: it suggests this specific family (one
smooth side, one index-2 side, built via this particular
"projectivize-the-affine-cone-with-an-extra-`w`-variable" compactification)
lands reliably on `nef=false`, not by coincidence in one instance but as an
apparent systematic feature of the construction. Whether this is intrinsic
to the *combinatorial type* (one index-2 point circuits, this compactification)
or specific to these two particular ray choices was not further isolated.

### Where this leaves the search

Four candidates were tried in total (the original working example plus
three follow-ups): two gave a genuine, comparably cheap flip with
`nef=false` (the original and candidate 4), one was accidentally
Gorenstein with no flip to study (candidate 2), and one had an expensive
flip computation itself, not reached in 10+ minutes (candidate 3). No
candidate reached `nef=true`. This suggests that finding a genuine "one
flip, then minimal model" example may require either a different
compactification strategy (the `w`-variable trick borrowed from
`tests/relative-model.m2` was designed to test the flip computation in
isolation, not to produce a globally minimal post-flip model, and may be
systematically unsuited to the latter goal) or a combinatorially different
family of circuits (more than 4 rays, or a different relation pattern)
rather than further perturbations of this one 4-ray family's `v4`.

## Suggested next steps

- Rethink the compactification, not just the ray configuration: the
  `w`-variable projectivization borrowed from `tests/relative-model.m2` was
  built to isolate the flip computation, and two independent 4-ray circuits
  through it both landed on `nef=false` at near-identical cost -- weak
  evidence this specific compactification systematically fails to produce
  `nef=true`, rather than that `nef=true` is rare among simple flips in
  general.
- Try a genuinely different family: more than 4 rays, or a different
  relation pattern (not a single 4-ray circuit's `v4` perturbed), possibly
  guided by an explicit literature construction of Francia's flip embedded
  in a compact Fano/Calabi-Yau-type ambient known independently to reach a
  minimal (or Mori-fibre) model after the flip, rather than searching
  blindly within this one compactification's parameter space.
- If a `nef=true` case is found, connect the pre-flip smooth chamber to the
  flip through the actual top-level driver
  (`mmpStepRecordData`/`threefoldMMPData`), mirroring the `Bl_p(P3)`
  capstone's pattern, rather than only testing the flip and post-flip nef
  search in isolation as done throughout this report.
- Consider testing `canonicalNefData` on Chamber A (the smooth side) as a
  sanity/contrast check -- expected to be fast given smoothness, confirming
  that the *only* added cost is the one singular point on the flip side.
- Profile why candidate 3's flip computation itself (not the nef search)
  became expensive from a single `v4` coordinate change (`-2` to `-3`),
  distinct from and unexplained by anything found in the `steinHomData`
  investigation.
