# Stage 2 measurement plan: singular targets and the canonical index search

Work order written on 2026-08-13, on branch `feature/stage2-singular-planning`
(forked from `feature/multigraded-stage1` after T1-T5 landed and were
measured; see `docs/STAGE1-MEASUREMENT-RESULTS.md`).  It is self-contained:
everything needed to carry it out is stated here or in the files it names.

This is a **planning and investigation document only**.  No package code was
changed to produce it.  Every fact below marked "verified" was checked by an
actual, timed Macaulay2 run on this checkout; every M2 run used to produce a
number in this document was made through `needsPackage`/`loadPackage` calls
against the unmodified `MMPComputation.m2`, `FlipComputation`, and
`WeilDivisors`, never by editing them.

## 0. One-paragraph summary

Stage 1 made the multigraded nef/threshold/contraction chain cheap on two
**smooth** examples with `K` Cartier at index 1, and its own results document
says plainly that nothing was measured on a singular variety.  This plan
investigates what changes once the target is genuinely singular: `K` is only
Q-Cartier, of index greater than one, and the existing `canonicalIndexData`
must actually search for that index rather than being handed a Cartier
divisor by the caller.  The central, unanticipated finding is that this is
**not only a cost question**: probing a genuinely singular, rank-2 (bigraded)
flip target that arises naturally from this repository's own worked examples
turned up two concrete defects, one already suspected (`canonicalIndexData`
uses the unfixed, monograded-only `isCartier` and so cannot terminate
correctly on a multigraded ring) and one not previously found (Stage 1's own
`multigradedBlockData`, on a *skew* bigraded ring — one where a fibre variable
carries a nonzero degree component outside its "own" block, which is exactly
what `bigradedReesProjection` produces from a non-equigenerated ideal —
silently computes the *wrong* irrelevant ideal, and the Stage 1 "fixed"
saturated Cartier test then reports a divisor Cartier when it verifiably is
not).  Stage 2's job is therefore corrective before it is a speed-up: fix or
route around this block-classification defect, make `canonicalIndexData`
multigraded-correct, and only then measure whether the chain "index search ->
nef test -> threshold -> contraction" is fast or slow on a genuinely singular
input, using the concrete ring constructed and verified below.

## 1. Goal, scope, non-goals

**Goal.**  On a genuinely singular, non-Gorenstein multigraded presentation,
determine (a) whether the Stage 1 machinery gives *correct* answers at all,
fixing what is found broken with the narrowest possible additive change, and
(b) if correct, how expensive the resulting chain is compared to the
Stage 1 smooth measurements.

**In scope.**

- Locating and verifying, by direct M2 computation, a concrete singular,
  rank-2, canonical-index-`>1` presentation suitable as the Stage 2
  measurement input (section 3).
- Diagnosing, with a verified concrete counterexample, whether
  `multigradedBlockData` and `canonicalIndexData` behave correctly on that
  input (section 2).
- Proposing a narrowly scoped, additive task list for the *future*
  implementation work that would fix what is found broken and then measure
  the chain (section 5) — **not implementing it**.
- A measurement protocol for that future work (section 6), mirroring
  `STAGE1-MEASUREMENT-PLAN.md` section 5.

**Explicitly out of scope.  Do not attempt these, now or in the future work
this plan describes, without a fresh work order:**

- Modifying `MMPComputation.m2`, `third_party/`, or `references/`.  This
  document is analysis only.
- Redesigning `FlipComputation`'s `bigradedReesIdeal`/`bigradedReesProjection`
  or its skew-fibre handling (`b2mDiagonalData`).  That package is pinned and
  pull requests against it are a different work order.
- Generalizing `b2mToGraphMorphism`'s forced Segre collapse to more than two
  blocks, or trying to make `relativeCanonicalModelFromBaseData`'s
  `"relativeModelRing"` field itself multigraded.  Section 2.4 explains why
  this is a real limitation, but removing it is `FlipComputation`-owned work,
  exactly as Stage 1 ruled `SteinFactorization`'s two-block limit out of
  scope.
- A general, provably-correct fix for `multigradedBlockData`'s block
  classification on arbitrary skew gradings.  Section 2.3 gives a verified
  counterexample and a plausible narrow fix (prefer a caller-supplied /
  provenance irrelevant ideal over re-deriving one), but a fully general
  repair of the classification heuristic itself is a harder problem and is
  not asked for here.
- Automatic redesign of the canonical-index search algorithm (e.g. smarter
  than linear `i = 1, 2, 3, ...`) unless a future measurement (T3 below)
  actually shows the search *strategy*, as opposed to its predicate, is the
  dominant cost. Do not presume it is; measure first.
- Detecting non-Q-Gorenstein targets (where no multiple of `K` is ever
  Cartier).  `canonicalIndexData` cannot currently distinguish "the search
  limit was reached" from "no index exists"; noting this ambiguity is in
  scope, resolving it is not.
- Any change to `references/AlgoMMP`.
- Running `computeFlip`/`relativeCanonicalModelData` end to end as part of a
  second full MMP step, or touching `threefoldMMPData`.

If the future work this plan describes needs something out of scope to make
progress, it should stop and report that, exactly as Stage 1's plan required.

## 2. Verified facts

All measured on 2026-08-13 with Macaulay2 1.26.06 on this checkout (same
machine as `STAGE1-MEASUREMENT-RESULTS.md`: `Darwin
TYs-MacBook-Air-2024.local 25.6.0 ... arm64`, macOS 26.6.1 build 25G76).
Every ring, timing, and boolean below was produced by a scratch script that
`needsPackage`s the unmodified `MMPComputation.m2` (and, where noted,
`FlipComputation`/`WeilDivisors` directly); none of the package files were
edited.  Unexported helpers (`multigradedBlockData`,
`isCartierSaturatedInternal`, `isBasePointFreeDivisorInternal`) were read via
`value(MMPComputation#"private dictionary"#"<name>")`, the same read-only
technique `MMPComputation.m2` itself uses for `WeilDivisors`' private
`divisorToModule`.

### 2.1 The ordinary double point is a bad candidate for the index search — confirmed, not assumed

`R = QQ[o0,o1,o2,o3,o4]/ideal(o0*o1-o2*o3)` (the ODP of
`third_party/flip-computation/examples/ordinary-double-point.m2` and
`tests/contraction.m2`/`SMALLNESS-CRITERION.md`).  Directly checked:

```text
K_ODP = -3*Div(o4)
isCartier(K, IsGraded=>true) = true          -- index 1, Gorenstein
canonicalIndexData(R) = {conclusive=>true, index=>1}     -- 0.09s
```

So, exactly as the task anticipated, the ODP is Gorenstein: it is singular
(the ordinary double point is not smooth, not even Q-factorial) but `K` is
already Cartier, so it exercises none of the index-search machinery.  It
remains a legitimate, cheap sanity check that singular-but-Cartier inputs
still work, but it is not a Stage 2 measurement input for the index search.

Its natural bigraded presentation, the small resolution
`Y = (bigradedReesProjection ideal(o0,o2))#totalRing` (rank 2, degrees
`{{1,0},{1,0},{0,1},{0,1},{0,1},{0,1},{0,1}}` for `u1,u2,o0..o4`), is also
Gorenstein (`isCartierMultigraded(K_Y) = true`) and, importantly, its fibre
degrees are **not skew** (`u1,u2` both have degree exactly `(1,0)`, because
`ideal(o0,o2)` is equigenerated — its two generators have equal degree).
`multigradedBlockData`'s computed irrelevant ideal agrees exactly (same
radical) with the ground-truth `bigradedReesProjection`-supplied
`irrelevantIdeal` here. This is recorded as a **positive control**: it shows
the Stage 1 machinery agrees with ground truth when the fibre grading is
clean, which sharpens the contrast with section 2.3 below, where it does not.

### 2.2 A genuinely singular, rank-2, canonical-index-2 flip target exists in this codebase's own worked examples, and is cheap to construct

`third_party/flip-computation/examples/toric-flip-index-two.m2` computes,
over an *affine* base, the flip of the toric threefold on rays
`v1=(1,0,0), v2=(0,1,0), v3=(0,0,1), v4=(1,3,-2)`.  Its own comment records
(independently of anything in this package) that the flip target `Z` (the
triangulation `{v1,v2,v3},{v1,v2,v4}`) is singular in one chart, with a
cyclic quotient point of **canonical index 2**: `K_Z` is 2-Cartier but not
Cartier.  I re-derived this independently from the raw toric data as a
cross-check (not merely trusting the comment): solving `M m = -k(1,1,1)`
for `M` the matrix of rows `v1,v2,v4` gives `m = -k(1,1,3/2)`, not integral
for `k=1` but integral for `k=2` — confirming index exactly 2 at that chart,
matching the source comment.

This affine example is not directly usable: `computeFlip(...,
BaseIsProjective=>false)` gives an *ungraded* (`degreeLength ambient = 1`,
standard) presentation with no interesting rank. Following the same
compactification idea `examples/toric-flip-projective.m2` uses for the
*other* (smooth-flip) example — add one extra homogeneous coordinate `w` to
the same toric ideal — but choosing the forced grading `l=(1,1,1)` (forced by
`v1,v2,v3`; interior to the dual cone since `l.v4=2>0` too) instead of the
special `l=(1,1,-1)` the original example uses (which does not apply here,
since `v4=(1,3,-2)` does not pair to a uniform constant under it), gives a
weighted-projective compactification:

```m2
loadPackage("FlipComputation",
    FileName=>"third_party/flip-computation/FlipComputation.m2", Reload=>true);
needsPackage "Polyhedra";  needsPackage "WeilDivisors";

rayList = {{1,0,0},{0,1,0},{0,0,1},{1,3,-2}};
sigma = coneFromVData transpose matrix rayList;
HB = apply(hilbertBasis dualCone sigma, v -> flatten entries v);
   -- HB = {{0,1,0},{0,1,1},{0,2,3},{1,0,0},{1,1,2},{2,0,1}}, 6 elements
L = QQ[t1,t2,t3];
S0 = QQ[y_1..y_(#HB)];
I0 = ker map(L,S0, apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
wdegs = apply(HB, h -> sum apply(3,k -> h#k*{1,1,1}#k));  -- {1,2,5,1,4,3}
S = QQ[y_1..y_(#HB), w, Degrees => wdegs | {1}];
Xproj = S/sub(I0,S);
```

Verified: `dim Xproj = 4` (a weighted-projective **threefold**, `dim R-1=3`),
`isNormal Xproj = true`, and its singular locus is exactly the vertex
`(y_1,...,y_6)` (radical match confirmed), i.e. the same single point the
affine picture already has, with no new singularity introduced by the
compactification. Construction cost (Hilbert basis through the ring): under
0.05s.

Running the existing, **unmodified** `computeFlip` on this ring:

```m2
P = computeFlip(Xproj, BaseIsProjective=>true, Multipliers=>{1,2});
```

reproduces the source comment's own claim mechanically: `m=1` is rejected
(exceptional locus contains a divisor), `m=2` succeeds. Total time **0.30s**.
`P` is a genuine `B2MProjection`: `P#totalRing` (call it `Z`) has
`degreeLength ambient Z = 2` (bigraded, rank 2!), degrees
`{{1,0},{1,1},{0,1},{0,2},{0,5},{0,1},{0,4},{0,3},{0,1}}` for
`u_1,u_2,y_1,...,y_6,w`, `dim Z = 5`, geometric dimension `dim Z - 2 = 3`
(matching `coneCorrection` for a projective base).

**Directly confirmed singular** (not merely inherited from the source
comment): setting `u_2=1` in `P#definingIdeal` on `P#ambientRing` gives a
4-dimensional chart whose `singularLocus` is nonempty
(`dim singularLocus Q =!= -1`); setting `u_1=1` gives a smooth chart. This
matches the two-chart toric picture in the source example exactly (one
smooth cone, one singular cone of determinant `\pm 2`).

This is, as far as I found by searching `third_party/` and this repository's
own tests and examples, the **only already-known-geometry, genuinely
singular, rank-2 presentation available without new geometric derivation.**
It required one small, mechanical adaptation (the compactifying weight `l`),
not a new example invented from scratch, and every geometric claim about it
(dimension, normality, singular locus, chart smoothness, canonical index) was
independently checked by M2, not merely asserted by the source comment.

### 2.3 A previously unknown defect: `multigradedBlockData` silently misclassifies this ring's blocks, and the Stage 1 "fixed" Cartier test gives a false positive as a result

This is the most important finding of this plan, and it was not anticipated
by any of the background documents.

`multigradedBlockData Z` **succeeds** (no error, rank 2 reported, cost
0.0002s), so by the narrow criterion Stage 1 tested against — "does the
admissibility check accept a ring produced by `bigradedReesProjection`" — it
looks fine, exactly as `STAGE1-MEASUREMENT-RESULTS.md` section 7 reported for
its own (different, non-singular) `bigradedReesProjection` test case. But its
*block assignment* is:

```text
blockAssignment = {1, 2, 2, 2, 2, 2, 2, 2, 2}
blockVariables  = {{u_1}, {u_2, y_1, ..., y_6, w}}
B (computed)    = ideal(u_1*u_2, u_1*y_1, ..., u_1*w)
                = ideal(u_1) * ideal(u_2, y_1, ..., y_6, w)
```

This is **wrong**. `u_1` and `u_2` are the two homogeneous coordinates of a
single `P^1` fibre (`P#fiberVariables`); they belong in the *same* block.
`FlipComputation` itself knows the correct partition — it is the
`irrelevantIdeal` field the `B2MProjection` already carries
(`bigradedIrrelevantIdeal(P#fiberVariables, P#baseVariables)`):

```text
B (true, from P#irrelevantIdeal) = ideal(u_1*y_1,...,u_1*w, u_2*y_1,...,u_2*w)
```

These two ideals have **different radicals** (confirmed: `radical Bmine ==
radical Btrue` is `false`). The root cause is that `u_2` has degree `(1,1)`
— nonzero in *both* grading components — because the ideal being blown up
(`canonicalIdeal Xproj`, degrees 2 and 3) is **not equigenerated**; this is
exactly `bigradedReesIdeal`'s `deg(u_i) = (1, d_i-d_0)` construction
(`rees.m2:36`), which is *skew* whenever the generator degrees differ, and is
exactly what that file's own comments call a case needing special handling
(`b2mDiagonalData`'s "diagonal slope", used only at the Segre-collapse step,
section 2.4 below). `multigradedBlockData`'s admissibility rule — "block `s`
is the last nonzero degree component, and it must be positive" — is a
*correct* implementation of the block-lower-triangular condition literally
as stated in `MULTIGRADED-DESIGN.md` ("degree zero in every component `>
s`"), but on this ring that condition genuinely fails for the *intended*
grouping (`u_2`'s component-2 entry is `1`, not `0`, so `u_2` cannot be
in the same block as `u_1` under that definition), and the algorithm falls
back to a *different*, technically-admissible grouping that does not match
the ring's actual fibre/base structure. **The mechanical admissibility check
passing does not certify that the resulting block partition, and hence the
irrelevant ideal `B`, is geometrically correct — only that a syntactically
valid one was found somewhere.** This is a real gap: Stage 1 never checked
its `B` against independently known ground truth on a *skew* input; its two
actual measurement inputs (`Bl_p(P3)`, Segre) both used a clean, non-skew
presentation with `Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}`,
and the one `bigradedReesProjection` ring it did check (`STAGE1-RESULTS.md`
section 7) was only tested for admissibility, never carried through a
Cartier or nef test, and (verified here) is itself equigenerated, hence not
skew.

The consequence is concrete and was directly measured, not inferred:

```text
K = canonicalDivisor(Z, IsGraded=>true)
isCartier(K, IsGraded=>true)             = false   -- the OLD monograded test (also wrong, differently)
isCartierMultigraded(K)  [Stage 1's fix, using multigradedBlockData's WRONG B]
                                          = true    -- FALSE POSITIVE
isCartierSaturatedInternal(K, Btrue)      = false   -- CORRECT, using P#irrelevantIdeal
isCartierSaturatedInternal(2K, Btrue)     = true    -- CORRECT: index is 2, exactly as derived in 2.2
isCartierSaturatedInternal(3K, Btrue)     = false
isCartierSaturatedInternal(4K, Btrue)     = true
```

(Full per-multiple timings: `i=1`: 0.17s, `i=2`: 0.29s, `i=3`: 0.47s, `i=4`:
0.75s using `Btrue`; `isCartierMultigraded` with the wrong `B` returned
`true` uniformly for `i=1..6`, costing 0.17-2.86s, growing with `i` — so the
defect is not merely wrong, it is also not obviously cheaper.) The mechanism
was traced concretely: `nonCartierLocus(K,IsGraded=>true)` (unsaturated) is
genuinely nonempty (codimension 3), and one of its components lies on
`u_1=0` with `u_2\ne 0` — an honest point of the exceptional `P^1` fibre, at
the toric singular point. Saturating against the WRONG `B` kills this
component (because `V(u_1)` alone, not `V(u_1,u_2)`, is one of the wrong
`B`'s two factors, so `u_1=0` alone already counts as "irrelevant"); saturating
against the TRUE `B` correctly leaves a nonempty, codimension-3 residual
locus, so the correct predicate reports non-Cartier, as it must.

**This means the corrected multigraded Cartier test built in Stage 1 is not
safe to use as-is on a ring reachable from a genuine flip computation, and
the failure is silent** — no error, no warning, just a wrong boolean. Any
Stage 2 work must treat fixing or routing around this before trusting a
"Cartier" answer on a singular multigraded target.

### 2.4 `canonicalIndexData` cannot currently work multigraded, confirmed by direct measurement, and the fix in 2.3 also fixes it

`canonicalIndexData` (unmodified, exported) uses `isCartier(i*K,
IsGraded=>true)` — the plain monograded predicate — with no multigraded
overload, unlike `canonicalNefData`. Run directly on `Z`:

```text
canonicalIndexData(Z, CanonicalIndexSearchLimit=>6)
  => conclusive = false, index = null            -- 5.41s (i=1..6, all "false")
```

It never terminates within the limit, because the monograded `isCartier`
test is known-wrong on multigraded rings (`STAGE1-MEASUREMENT-PLAN.md`
section 3.2), here consistently returning `false` even at `i=2`, where the
divisor genuinely is Cartier. So the concern the task background raised —
"`canonicalIndexData`'s search for the Cartier index becomes load-bearing" —
is confirmed exactly: as shipped, it cannot find the index of a genuinely
singular multigraded target at all, it just burns through the search limit.
Re-running the same loop with the *corrected* predicate
(`isCartierSaturatedInternal(i*K, Btrue)` from 2.3) finds `index=2` cleanly
within the same six iterations, at comparable cost (\~1.7s for `i=1..4`).
So the fix needed for `canonicalIndexData` is the same fix needed for
`isCartierMultigraded` generally: a correct `B`, not a new algorithm.

### 2.5 The flip pipeline's public output ring is always monograded; the bigraded ring is available only one layer underneath

`relativeCanonicalModelFromBaseData` (unmodified) returns
`"relativeModelRing" => modelGraph#sourceRing`, and `b2mToGraphMorphism`
(`FlipComputation/segre.m2:80`) *always* Segre-collapses its `B2MProjection`
input to a single grading via a Hilbert-basis diagonal, regardless of
whether the input was clean or skew — this is the same two-block limit
already flagged for `SteinFactorization` in `MULTIGRADED-DESIGN.md`, just at
a different call site. **So the flip target this package currently returns
to a caller is never rank 2, even when the honest flip target manifestly is**
(section 2.2/2.3's `Z` is rank 2 before this collapse). The bigraded ring is
not lost, though: `relativeCanonicalModelFromBaseData`'s own result hash
table already carries it, unused, as
`(result#"relativeModelProjection")#totalRing` — this is exactly `P#totalRing`
from section 2.2, obtained without any new code, since
`relativeCanonicalModelFromBaseData` calls `computeFlip` internally with
`ReturnGraph=>false` and keeps the resulting `B2MProjection` in that field.
So a Stage 2 measurement does not need to re-derive `Z`; it is already one
field away from the existing public API, just not exercised there today.

### 2.6 What was not found

- No genuinely singular rank-`\ge 2` example with canonical index `> 1` was
  found *already sitting in `tests/` or `examples/` and returned as such by
  the existing public API* — every existing regression that uses a singular
  ring (`ODP`, the two `tests/relative-model.m2` flip targets) either has
  index 1 (ODP) or is monograded by construction (the flip targets, because
  of 2.5). Section 2.2's ring is a **one-step adaptation** of an existing
  worked example (a change of compactifying weight, no new geometry
  invented), not something already used as-is elsewhere in this repository.
- `P(1,1,1,2)` (`tests/nefness.m2`) is a genuine, already-passing rank-1,
  canonical-index-2 example. It is not a new Stage 2 deliverable — it is
  already covered — but is worth naming here as the simplest possible
  positive control for a *monograded* singular index search, if one is
  wanted before attempting the rank-2 case: `canonicalIndexData` on
  `QQ[z0,z1,z2,z3,Degrees=>{1,1,1,2}]` was **not** explicitly re-run here
  (out of scope: not a new fact, already exercised via
  `weightedAmpleDivisorData` in the existing test), but would be a cheap,
  low-risk warm-up for whoever implements Stage 2.
- No attempt was made to construct a rank-`\ge 2` example from a *product* or
  *complete intersection* in a singular ambient weighted-projective tower
  (as opposed to a flip output); the flip-output route (2.2) was more direct
  once found, and pursuing a second, independent construction was judged
  not to add enough to justify the time, per the effort-boundedness this
  plan operates under. If the flip-output ring turns out to have some
  idiosyncrasy that a future implementer wants to rule out, a weighted
  product/hypersurface construction is the natural second example to build,
  and is flagged here as a legitimate follow-up, not attempted.

## 3. Concrete input for the eventual Stage 2 measurement

The primary input is the ring `Z` of section 2.2/2.3, obtained by:

```m2
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
loadPackage("FlipComputation",
    FileName=>"third_party/flip-computation/FlipComputation.m2", Reload=>true);
needsPackage "Polyhedra";
needsPackage "WeilDivisors";

rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,3,-2}};
sigma = coneFromVData transpose matrix rayList;
HB = apply(hilbertBasis dualCone sigma, v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
wdegs = apply(HB, h -> sum apply(3, k -> h#k*{1,1,1}#k));  -- {1,2,5,1,4,3}
S = QQ[y_1..y_(#HB), w, Degrees => wdegs | {1}];
Xproj = S/sub(I0,S);

P = computeFlip(Xproj, BaseIsProjective=>true, Multipliers=>{1,2});
Z = P#totalRing;                          -- the Stage 2 measurement input
Btrue = sub(P#irrelevantIdeal, Z);        -- the CORRECT irrelevant ideal; do
                                           -- NOT use multigradedBlockData's own
                                           -- B on this ring (section 2.3)
```

Verified properties, all confirmed above: `degreeLength ambient Z = 2`,
`dim Z = 5`, geometric dimension `3`, singular (one chart non-smooth),
canonical index `2` (confirmed both by independent toric hand computation
and by `isCartierSaturatedInternal(2*K, Btrue)`), and `multigradedBlockData
Z` **succeeds but returns the wrong `B`** — this last point must not be
forgotten by whoever picks up T1 below, since it is silent.

Total setup cost through `computeFlip`: **0.30s**; `multigradedBlockData Z`:
0.0002s (wrong answer); `canonicalDivisor(Z,IsGraded=>true)`: 0.72s; one
Cartier test at the correct `B`: 0.17-0.75s depending on `i`.

Secondary input (sanity checks, both already fully confirmed in section 2.1,
not requiring further measurement): the ODP ring and its bigraded small
resolution, as a positive control that the machinery agrees with ground
truth when the fibre grading is not skew.

## 4. Why this is a good, and a limited, Stage 2 input

Good: it is rank 2 (exercises Stage 1's multigraded machinery, not just the
already-covered monograded `P(1,1,1,2)` case), genuinely singular with index
`>1` (exercises the index search), produced by the existing, unmodified
`computeFlip`/`bigradedReesProjection` machinery rather than hand-built
toy geometry, and every geometric claim about it was independently checked.

Limited: it is a *flip target*, i.e. downstream of a birational contraction,
not itself the output of a first MMP step the way Stage 1's two inputs were;
a full Stage 2 measurement of "index search -> nef test -> threshold ->
contraction" on `Z` needs a caller-supplied ample Cartier class on `Z` (per
`STAGE1-MEASUREMENT-PLAN.md` section 3.5's standing rule that the ample class
is always an input, never derived), and no such class was constructed or
verified here — identifying one is part of the future work (T4 below), not
something this plan resolves. Also, as section 2.6 notes, this is the one
rank-`\ge 2` singular-index-`>1` example located; if it turns out to have an
idiosyncrasy (e.g., something special about being a Rees-algebra Proj
specifically, as opposed to a general singular multigraded variety), a second,
independently constructed example would be valuable and was not attempted
here.

## 5. Staged task list for the eventual implementation work

None of these were implemented. Each is meant to be as narrow and additive as
a Stage 1 task, re-running `make test-core`/`make test-upstreams` after each.

### T1. Give the Cartier/base-point-free predicates a way to accept a known-correct irrelevant ideal, instead of only ever re-deriving one

This is the highest-priority item — it is a correctness fix, not an
optimization. Add a way for `isCartierSaturatedInternal`,
`isBasePointFreeDivisorInternal`, and their callers to accept a
caller-supplied `B` (or a `B2MProjection`/`GraphMorphism` to read it from),
bypassing `multigradedBlockData`'s own re-derivation when a better source is
available. `STAGE1-MEASUREMENT-PLAN.md`'s own T1 already anticipated this
("for a `GraphMorphism` or `B2MProjection` in hand, prefer its existing
`irrelevantIdeal` field over recomputing") but no current call path does so.
Keep `multigradedBlockData`'s existing behavior and callers unchanged for
rings with no such provenance (do not touch the r=1 or the Stage-1-measured
r=2 clean cases; both are unaffected by this defect, per section 2.1/2.3).
Do **not** attempt to fix the general block-classification heuristic itself
to detect skewness automatically — that is the out-of-scope item in section 1.

### T2. A multigraded `canonicalIndexData`

Add an overload analogous to `canonicalNefData`'s `(Ring,ZZ,BasicDivisor)`
pattern: `canonicalIndexData` taking a caller-supplied `B` (or object to read
one from, per T1), using `isCartierSaturatedInternal` instead of `isCartier`.
Keep the existing `canonicalIndexData(Ring)` unchanged and behavior-preserving
for `r=1` (confirm by test, not by assumption, exactly as Stage 1's T2 did
for the base-point-free predicate). Verify against section 3's `Z`: expect
`index=2`.

### T3. Measure the index search itself on a singular multigraded ring

Once T1/T2 land, time the loop `i=1,2,3,...` on `Z` with the corrected
predicate: cost per iteration, cost of `canonicalDivisor` (computed once, not
per iteration — confirm the implementation doesn't recompute it), and whether
cost grows with `i` in a way that matters before `MaxSteps`-scale multiples
are reached. Section 2.4 gives preliminary numbers (\~1.7s for `i=1..4`
here) but a real T3 should also try a harder ring (higher index, or a genuine
non-equigenerated ideal with more Rees generators) to see whether the growth
pattern holds up.

### T4. Measure the nef/threshold/contraction chain on a singular multigraded ring at its true index

This is the actual question the background documents left open: does the
Stage 1 speed-up survive once reflexive powers of a non-invertible `K` are
genuinely needed? Requires a caller-supplied ample Cartier class on `Z` (not
derived — identifying and certifying one is part of this task, following
section 3.5 of the Stage 1 plan) and then timing
`canonicalNefData(Z,2,H)` through `canonicalContractionData`, exactly
mirroring `STAGE1-MEASUREMENT-PLAN.md` section 5.2's eight stages. Expect
`OO(m*(K+tH))` computations to be genuinely more expensive here than in
Stage 1's smooth examples, since `weilDivisorToModule` on a non-Cartier `K`
must build an honest reflexive hull rather than a line bundle; the open
question is by how much, not whether.

### T5. Decide, do not yet implement, how to keep working multigraded through the Stein/Segre interface for a singular flip target

Section 2.5 shows the bigraded `Z` is available (as
`(relativeCanonicalModelFromBaseData result)#"relativeModelProjection"#totalRing`)
one field away from where the pipeline currently discards it. Before writing
any code, decide whether a Stage 2+ implementation should (a) add its own
additive entry point that consumes this field directly for a second MMP step,
staying multigraded past the flip, or (b) explicitly accept the forced
monograded collapse here too, exactly as Stage 1's T5 did at the Stein
interface, and just measure its cost. This is a design decision, not
executable work, and this plan does not resolve it — whoever implements
Stage 2 should pick one deliberately and say which, rather than defaulting
into it.

## 6. Measurement protocol (for the eventual T3/T4 work)

Mirrors `STAGE1-MEASUREMENT-PLAN.md` section 5.2. Use a scratch directory,
not `tests/`, until/unless a result becomes a regression. Record, per stage:
stage name, cpu seconds, key outputs. Stages, extending Stage 1's list with
the index search at the front:

0. build `Xproj`, run `computeFlip`, obtain `Z` and `Btrue` (section 3)
1. block structure: report *both* `multigradedBlockData Z`'s `B` and
   `Btrue`, and flag the mismatch explicitly in the output — do not silently
   use the wrong one (section 2.3)
2. canonical divisor of `Z`
3. Cartier index search, `i=1,2,...` with the corrected predicate — record
   per-`i` cost and the index found
4. nefness at the found index (needs a supplied ample class, T4)
5. threshold search
6. flattening to the diagonal subalgebra (this is a *second* flattening,
   distinct from `b2mToGraphMorphism`'s forced one at the Stein interface —
   name which is which in the report)
7. complete-linear-system graph
8. Stein factorization
9. contraction type and dimensions

As in Stage 1: if a stage does not return within 20 minutes, kill it, record
"did not complete" with the last printed line, and treat that as a
successful, informative outcome of the measurement, not a failed work order.

## 7. Success criteria

1. T1/T2's changes are additive: `make test-core` and `make test-upstreams`
   pass unchanged, and every existing monograded assertion is unaffected.
2. T2's corrected `canonicalIndexData` finds `index=2` on `Z` (section 3),
   matching the independently-derived toric value (section 2.2).
3. T1's fix (or routing) makes `isCartierSaturatedInternal(K,\cdot)` on `Z`
   agree with the toric ground truth (`false` at `i=1`, `true` at `i=2`) when
   given the correct `B`, and this is exercised by an actual regression
   comparing against `P#irrelevantIdeal`, not merely against
   `multigradedBlockData`'s own (unverified) output — section 2.3's defect
   would not have been caught by a test that only checks internal
   consistency.
4. T3 produces real timing numbers for the index search on a genuinely
   singular ring, replacing this plan's preliminary ones.
5. T4 reaches at least the nef test on `Z` at the correct index with a
   supplied ample class, with recorded timings — reaching further (threshold,
   contraction) is desirable but, as in Stage 1, not required; a stall that
   is recorded and located is a successful outcome.
6. A results document analogous to `STAGE1-MEASUREMENT-RESULTS.md` exists for
   whichever of T3/T4 is carried out, including a "what this does and does
   not establish" section.

## 8. Pitfalls

- **Do not trust `multigradedBlockData`'s output on a skew ring just because
  it returns without error.** Section 2.3 is the load-bearing warning of this
  entire plan: admissibility succeeding is not the same as the block
  partition being geometrically correct. Cross-check against a
  provenance-supplied irrelevant ideal (a `B2MProjection`'s or
  `GraphMorphism`'s own field) whenever one is available, and be suspicious
  when it is not.
- **Do not assume `canonicalIndexData`'s current failure mode is merely
  "slow".** It is wrong: it will run to its search limit and report
  inconclusive on a ring where the true index is well within that limit,
  because its underlying predicate is wrong, not merely because the search
  needs more iterations.
- **A "Cartier: true" answer from any predicate on a multigraded ring is not
  self-certifying.** Section 2.3's false positive produced no error and no
  unusual output; it looked identical to a correct answer. Any future
  regression for T1/T2 must check against an independently derived fact
  (toric hand computation, or a provenance-carrying object's own field), not
  merely check that the code runs.
- **Skewness is not rare or contrived.** It arises directly from
  `bigradedReesProjection` whenever the ideal being blown up is not
  equigenerated (unequal generator degrees) — exactly the generic case for a
  canonical ideal of index `>1`, and already flagged, for a different reason
  (the Segre-collapse diagonal), by `FlipComputation`'s own
  `b2mDiagonalData`. Do not treat section 2.3's ring as a corner case.
- **The flip pipeline's public `"relativeModelRing"` is always monograded**
  (section 2.5); do not expect to find a rank-2 singular ring by calling
  `relativeCanonicalModelFromBaseData` and reading its headline field. Read
  `"relativeModelProjection"#totalRing` instead if a bigraded presentation is
  wanted.
- **`canonicalIndexData` cannot currently tell "no Cartier multiple exists"
  from "search limit reached"** — both return the same
  `conclusive=>false` shape. Do not read a `false` as proof of
  non-Q-Gorenstein-ness; it is only proof that the tested multiples failed.
- **Do not reuse this plan's `Z` across T3 and T4 without re-deriving
  `Btrue`** — it is a `sub` of `P#irrelevantIdeal` into `Z`'s own ring and
  must be recomputed if `Z` is rebuilt (e.g. in a fresh M2 session), since
  ideals do not survive a session boundary.
- As in Stage 1: report negative results plainly. Section 2.6 records what
  was not found; that is a legitimate deliverable of this plan, not a gap in
  it.

## 9. Deliverable

This document, `docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md`, committed alone on
`feature/stage2-singular-planning`. No package code, tests, or third-party
sources were changed. The scratch scripts used to produce the numbers above
were run from a temporary directory outside the repository and were not
committed, exactly as `STAGE1-MEASUREMENT-RESULTS.md` records for its own
measurement scripts.
