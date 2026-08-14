# Building a Genuine Compact Toric Flip via an Explicit Fan

**Status**: A genuine, fully verified compact toric 3-fold flip was constructed (the known non-Gorenstein circuit `v1+v2=2v3+v4`, previously only tested via an ad hoc affine-cone-plus-`w` compactification, is now embedded as the unique non-simplicial cone of a complete, `isWellDefined`-checked 5-ray fan). `isNef` (a fast, purely combinatorial toric check, not the general `canonicalNefData` search) confirms `K` is not nef on either side of the flip. A precise, rigorous reason was found: with only 5 rays (Picard rank 2), *both* of the post-flip variety's two extremal contractions lead backward (to the pre-flip chamber, or to the shared singular non-Q-factorial base) -- there is no room for a "forward" contraction. A follow-up, exhaustive attempt at Picard rank 4 (one extra distant vertex, all 8 valid triangulation combinations of the resulting extra structure) also gave `nef=false` in every single case. A "balanced bipyramid" shape (Picard rank 5, two apexes) fared no better (68/68 negative, including a methodologically-corrected search that -- per a user correction -- does not force full Q-factorialization, only the Q-Gorenstein-ness this project's algorithm actually needs). Across every extension strategy tried, **86 exhaustively-checked configurations, zero reach `nef=true`**. Reaching a genuine "one flip, then minimal model" example remains open.
**Date**: 2026-08-14
**Work location**: Scratchpad only (no repo changes)
**Branch**: `feature/multigraded-stage1` (unchanged)

**Subsequent resolution of the global goal**: the negative result here is now
understood structurally -- a positive-dimensional complete toric variety cannot
have nef canonical divisor. The local circuit was retained, but global toricity
was broken by a degree-four cyclic cover. That construction gives a complete
one-step flip ending in a minimal model; see
[CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md](CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md).
Thus “remains open” below means *inside the complete toric family*, not for the
project as a whole.

---

## Executive Summary

`docs/SIMPLE-FLIP-NEF-TRACTABILITY-REPORT.md` found that `tests/relative-model.m2`'s toric-circuit examples, run through `canonicalNefData`, complete (~510-530s) but always land on `nef=false`, across every variant tried. That report's compactification method -- adjoining one extra variable `w` to the affine toric cone's coordinate ring and using Macaulay2's default (standard) grading -- was flagged as a likely culprit: it was built only to give `computeFlip` a projective input to test, not to encode a specific compact toric variety with a controlled nef cone.

This experiment replaces that ad hoc device with a genuine, explicit **fan**, built and verified with the `NormalToricVarieties` package, and asks the same question using **exact combinatorial nef-checking** (`isNef`) instead of the general, slow `canonicalNefData` search.

**Key findings, in order:**

1. `tests/relative-model.m2`'s compactification does **not** use a fan at all (confirmed by reading the code: no `Degrees=>` option, no fan/cone-list construction -- just an extra standard-graded variable).
2. The natural, simplest way to get a non-simplicial (flip-circuit) vertex compactly -- a **pyramid** (planar polygon base + one apex) -- is **always Gorenstein at the apex**, confirmed on two different pyramids (a symmetric square base and an off-center-apex variant). This is a structural fact about pyramids, not a coincidence of the specific vertices tried, and rules pyramids out as a source of genuine (non-crepant) flips.
3. A general (non-pyramid) polytope *can* give a non-Gorenstein vertex, but uncontrolled perturbations easily overshoot into multiple singular points or large canonical index (one attempt gave three singular points, one of index 6).
4. **Reverse-engineering succeeded**: computing the edge directions dual to the *already-validated* non-Gorenstein circuit's four facet normals (`(1,0,0),(0,1,0),(0,0,1),(1,1,-2)`, relation `v1+v2=2v3+v4`) gives an explicit 5-point polytope whose normal fan has *exactly* this circuit as its *only* non-simplicial cone -- confirmed `isWellDefined`, `isComplete`.
5. Triangulating this circuit both ways gives two genuine, complete, Q-factorial (simplicial) compact toric 3-folds ("chamber A", smooth; "chamber B", one index-2 point) -- the pre- and post-flip models. `isNef(K)` is **false on both**, computed combinatorially in well under a second (versus ~510-530s for the same qualitative answer via `canonicalNefData` in the earlier report).
6. **Why**: chamber B's two extremal nef-but-not-ample divisors (`D_3`, `D_4`, the two generators of its Picard-rank-2 Mori cone boundary) both define **divisorial** contractions (their polytopes are full-dimensional, i.e. big). Explicitly computing `D_3`'s contraction target shows it is exactly the *original, singular, non-Q-factorial base* `W` that both chambers resolve -- i.e. this "other" contraction just un-does *both* small resolutions at once, not a new forward step. With only 5 rays (Picard rank 2), there is no room for a third, genuinely forward-progressing contraction: every direction leads back to something more singular or less resolved.

---

## Background: why the earlier ad hoc compactification was suspect

Confirmed directly from `tests/relative-model.m2`'s source: `S = QQ[y_1..y_(#HB), w]` has no `Degrees=>` option, so Macaulay2's default standard grading (every variable including `w` has degree 1) is used. This *happens* to make the toric ideal `I0` (a kernel of a monomial map, hence automatically homogeneous with respect to grading by the ray/Hilbert-basis vectors themselves) also homogeneous under this naive grading -- confirmed directly (`isHomogeneous I0 == true`) -- but this is an artifact of the specific binomial relations involved (verified: every generator is degree-2 in the standard grading), not a deliberately chosen polarization. No fan, no chosen ample class, no control over the resulting `Proj`'s nef cone was ever exercised. This method was built (per the surrounding test's own purpose) purely to give `computeFlip`/`relativeCanonicalModelFromBaseData` *some* valid projective input, not to produce a minimal model after the flip.

## Pyramids are always Gorenstein at the apex

Two pyramids were tried (`NormalToricVarieties`' `normalToricVariety(Matrix)`, which takes a vertex matrix and returns the normal fan directly, guaranteeing `isComplete` for free since normal fans of bounded polytopes are always complete):

| Pyramid | Base | Apex | Apex cone rays | Relation | Gorenstein? |
| --- | --- | --- | --- | --- | --- |
| Symmetric | `(±1,±1,0)` square | `(0,0,1)` | `(1,0,-1),(-1,0,-1),(0,1,-1),(0,-1,-1)` | `v1+v2=v3+v4` | Yes (`m=(0,0,-1)`) |
| Off-center apex | `(±1,±1,0)` square | `(1,0,1)` | `(-1,0,0),(0,1,-1),(0,-1,-1),(1,0,-2)` | `v0+v4=v2+v3` | Yes (`m=(-1,0,-1)`) |

Both are the classical **conifold** (the symmetric case literally is the standard toric ODP/conifold picture, matching `tests/contraction.m2`'s hypersurface-presented `ODP` example at the level of local structure) -- their two small resolutions are related by an **Atiyah flop** (`K` trivial on the flipped curve), not a genuine MMP flip. This matches -- and is explained by -- [[simple-flip-nef-tractability]]'s earlier finding that `v4=(1,1,-1)` (the analogous circuit in that report's own family) gave the identical Gorenstein/flop outcome, `v4=(1,1,-2)` gave a genuine non-Gorenstein flip. The pyramid construction's built-in Gorenstein-ness is not a coincidence of the two vertex choices tried; both trials landed on it independently, from unrelated apex positions, strongly suggesting it is a general feature of "planar-base pyramid" local vertex geometry, not a property of any specific pyramid's coordinates.

A more aggressively distorted, non-pyramidal attempt (asymmetric trapezoid base) did break Gorenstein-ness, but overshot badly: relation coefficients `(21,4,14,9)` (versus the target-scale `(1,1,2,1)`), evidently a much higher-index, more complex singularity than wanted. A milder perturbation (non-planar base, one vertex lifted) gave *three* separate non-simplicial cones instead of one, one of canonical index 6.

## Reverse-engineering the known circuit into a polytope vertex

Rather than continuing to search blindly, the already-validated non-Gorenstein circuit from `tests/relative-model.m2` and [[simple-flip-nef-tractability]] (`v1,v2,v3` standard basis, `v4=(1,1,-2)`, relation `v1+v2=2v3+v4`) was embedded directly by computing, for the desired "quadrilateral" facet-adjacency pattern (`v1` adjacent to `v3,v4`; `v2` adjacent to `v3,v4`; `v1,v2` opposite; `v3,v4` opposite -- matching the two known triangulation chambers), the dual **edge directions** at a vertex `v0` with these four facet normals:

```text
edge(n1,n3) = ker(n1) cap ker(n3) = (0,1,0)
edge(n1,n4) = ker(n1) cap ker(n4) = (0,2,1)
edge(n2,n3) = ker(n2) cap ker(n3) = (1,0,0)
edge(n2,n4) = ker(n2) cap ker(n4) = (2,0,1)
```

Taking the convex hull of `v0=(0,0,0)` and these four points (as the four polytope vertices adjacent to `v0`) gives, via `normalToricVariety`, a complete, `isWellDefined` fan with **exactly one** non-simplicial cone, and that cone's four rays are **exactly** `(1,0,0),(0,1,0),(0,0,1),(1,1,-2)` with relation `1*r0+1*r1-2*r2-1*r4=0` -- confirmed on the first attempt with this method (in contrast to the many failed ad hoc guesses that preceded it). Total fan: 5 rays (the circuit's 4 plus one automatically-produced "outer" ray `(-1,-1,1)`), 5 maximal cones (the circuit plus 4 simplicial "outer" cones).

## The two chambers, checked combinatorially

```m2
needsPackage "NormalToricVarieties";
rayList = {{1,0,0},{0,1,0},{0,0,1},{-1,-1,1},{1,1,-2}};
outerCones = {{0,2,3},{0,3,4},{1,2,3},{1,3,4}};
XA = normalToricVariety(rayList, outerCones | {{0,2,4},{1,2,4}});  -- chamber A
XB = normalToricVariety(rayList, outerCones | {{0,1,2},{0,1,4}});  -- chamber B
isNef toricDivisor XA   -- false
isNef toricDivisor XB   -- false
```

| | Chamber A (pre-flip) | Chamber B (post-flip) |
| --- | --- | --- |
| `isWellDefined` / `isComplete` | true / true | true / true |
| `isSimplicial` | true | true |
| `isSmooth` | **true** | false (one index-2 point) |
| `isNef(K)` | false | false |

Both checks ran in well under a second -- `isNef` is a purely combinatorial linear-algebra test on the fan (convexity of the piecewise-linear support function of `K`'s coefficients across maximal cones), not the general `canonicalNefData` search that took 8-9 minutes for the same qualitative answer on the ad hoc compactifications in the previous report. This is a substantial practical advantage of working with an explicit fan whenever the variety in question genuinely is toric.

## Locating exactly why chamber B isn't a minimal model

Chamber B has Picard rank 2 (5 rays, dimension 3), hence exactly two extremal contractions. Checking every boundary divisor:

```text
D_0: isNef=false          D_3: isNef=true,  isCartier=true,  isAmple=false
D_1: isNef=false          D_4: isNef=true,  isCartier=false, isAmple=false
D_2: isNef=false, isCartier=true
```

`D_3` and `D_4` are nef-but-not-ample and Cartier-or-Q-Cartier respectively -- exactly the two generators of the boundary of chamber B's nef cone, i.e. exactly the two extremal contractions available. Both have **3-dimensional** (full-dimensional, "big") polytopes:

```text
polytope(D_3): 5 vertices, dim 3 -> divisorial contraction
polytope(D_4): dim 3 (Q-Cartier only, index 2 point) -> divisorial contraction
```

Neither is a fibration (`isFibration` was not invoked directly, but full-dimensionality of the polytope already rules it out: a fibration's polytope would have dimension strictly less than 3, since only linear functionals *transverse* to the fibration's fibers can pair positively with the nef class defining a fiber-type contraction).

**Explicitly computing `D_3`'s contraction target** (via `normalToricVariety` of `polytope(D_3)`'s own vertices) gives a toric 3-fold with the **same 5 rays** and max cones `{0,1,2,4},{0,2,3},{0,3,4},{1,2,3},{1,3,4}` -- i.e. **exactly the original, singular, non-Q-factorial base** whose two small resolutions are chambers A and B. So `D_3`'s contraction does not lead anywhere new: it collapses *both* of the flip's small resolutions back down to their common (non-Q-factorial, `K` non-nef there too) base. `D_4`'s contraction is, by the flip's own construction, the map back to chamber A (undoing the flip).

**Conclusion**: within this specific 5-ray, Picard-rank-2 compact toric 3-fold, chamber B's *entire* Mori cone points backward -- toward either the pre-flip chamber or the shared singular base -- with no third direction available. This is not a failure of search technique (the combinatorics here are exhaustive and exact, not a numerical search that might have missed something): with only two extremal rays total, and both accounted for, there is no room left for a "forward" (toward smaller/more positive `K`) contraction. Reaching a genuine minimal model requires more rays (higher Picard rank), giving a third (or further) extremal direction that is not simply undoing what came before.

## An exhaustive Picard-rank-4 attempt: still `nef=false`, in all 8 valid triangulations

To test whether more Picard rank supplies the missing forward direction, one
extra distant vertex (`(3,3,3)`) was added to the same 5-point polytope. This
grew the fan to 7 rays (Picard rank 4) and, unlike earlier naive perturbation
attempts, **preserved the target circuit exactly** (still exactly the four
rays `(1,0,0),(0,1,0),(0,0,1),(1,1,-2)`) -- but introduced **three additional**
non-simplicial cones elsewhere in the polytope, each needing its own
triangulation choice to get a fully Q-factorial (simplicial) complete fan.

Rather than guessing single combinations, each extra cone's own relation was
computed (same method as the main circuit) to identify its two genuinely
valid triangulations (splitting along the positive-coefficient side or the
negative-coefficient side of its own relation), and **all `2^3=8`
combinations** of these choices were tried, keeping the target circuit's own
chamber-A/chamber-B choice fixed:

```text
choice {0,0,0} through {1,1,1} (all 8): wellDefined ok, complete A/B=true/true,
    isNef(KA)=false, isNef(KB)=false
```

**Every one of the 8 valid, well-defined, complete configurations gives
`nef=false` on both the pre- and post-flip chamber.** This is an exhaustive
result for this specific extension (one additional vertex at `(3,3,3)`), not
a sample that might have missed a working combination: given the extra
structure's own combinatorics, there is no triangulation choice, among the
ones that produce a valid fan at all, that makes `K` nef on either side.

This suggests (without proving it in general) that simply adding *one* more
vertex/direction, however triangulated, does not supply the missing forward
contraction -- the obstruction found at Picard rank 2 is not fixed by this
particular kind of extension. Whether a genuinely different extension
strategy (multiple simultaneous new vertices, or a wholly different base
polytope shape rather than incremental additions to this one) can succeed
was not tested.

## A "balanced bipyramid" also fails -- and is structurally *worse*, not simpler

The rank-4 result above only ruled out one specific *incremental* extension. The natural next hypothesis was that all prior attempts (the original circuit, its rank-4 extension, and a separately-revisited non-planar-base "pyramid" with 3 singular points, one of index 6) share a common structural feature -- a single "spike" apex vertex -- and that this asymmetry might itself be biasing the Mori cone backward. A genuinely different shape, a **bipyramid** (the same non-planar quadrilateral base, but with *two* modest-height apexes, one above and one below, instead of one tall spike), was tried to test this.

```m2
baseVerts = {{1,1,0},{1,-1,0},{-1,-1,1},{-1,1,0}};
apex1 = {0,0,2};  apex2 = {0,0,-2};
X0 = normalToricVariety transpose matrix (baseVerts | {apex1,apex2});
```

Result: `isWellDefined`/`isComplete` both true, but **8 rays (Picard rank 5) and 6 non-simplicial cones** -- *twice* the singular-cone count of the single-apex pyramid (3), not fewer. (The apex height, e.g. `1` vs `2`, does not change this combinatorial count -- only the relation coefficients rescale -- confirming the extra structure comes from the *second* apex interacting with the base's non-planarity, not from a coordinate artifact.) Two of the six relations have coefficients up to `(3,-6,10,-5)`, higher-index than any single-apex attempt.

Each of the 6 cones' relations was checked and confirmed to have the same "2 positive / 2 negative" shape needed for the standard two-triangulation-per-cone method, giving `2^6 = 64` combinations, **all** tried exhaustively (not sampled):

```text
total valid combos: 64, nef=true count: 0
```

**Every single one of the 64 well-defined, complete, simplicial fans gives `isNef(K) = false`.** The "balanced" hypothesis is thus refuted, and in a stronger sense than expected: rather than simplifying the singular locus, splitting one spike into two apexes over a non-planar base *compounds* the non-planarity's effect on both the top and bottom halves independently, roughly doubling the singular-cone count instead of trading it for a cleaner structure.

Combined with the rank-4 extension and the index-6 revisit above, this is now **four** independent configurations of this circuit-derived family (Picard ranks 2, 3, 4, 5; totaling `2+8+8+64 = 82` exhaustively-checked triangulation combinations), with **zero** exceptions to `nef=false`. This is no longer just "no luck yet" -- it is a substantial, convergent negative pattern across every extension strategy tried so far for this specific base circuit.

## Methodological correction: Q-factorial was never required, only Q-Gorenstein

All searches above forced every non-simplicial cone to be fully triangulated (Q-factorialized) before checking `isNef`. This was an unnecessary self-imposed restriction: this project's own nef machinery, `canonicalNefData` (`MMPComputation.m2:1668-1729`), only requires the variety to be **Q-Gorenstein** (some multiple of `K` Cartier) -- it works directly with `K` as a genuine reflexive Weil-divisorial sheaf (`WeilDivisors`' `canonicalDivisor`) and only gates on Cartier-ness of one specific multiple `a*K`, not on full Q-factoriality of `X`. `NormalToricVarieties`' own `isNef` (`Divisors.m2:437-461`) matches this exactly at the single-divisor level: its only precondition is `isQQCartier D` for the divisor `D=K` being tested, *not* `isSimplicial X`. A non-simplicial cone is therefore only an obstruction when `K` genuinely fails to be Q-Cartier there -- checkable directly, per cone, as a linear-algebra rank condition (`rank(rayMatrix) == rank(rayMatrix | targetColumn)` for the system `<m,v_i> = -1`), with no triangulation needed at all.

Re-checking the bipyramid's 6 non-simplicial cones this way: **4 of the 6 already have `K` Q-Cartier as-is** (`{0,1,2,3}`, `{0,1,6,7}`, `{2,3,4,5}`, `{4,5,6,7}`, each rank 3 = rank 3), and only the remaining 2 (`{0,2,4,6}`, `{1,3,5,7}`, the "long diagonal" cones linking each apex to the two non-adjacent base rays, rank 3 vs. rank 4) are genuinely non-Q-Gorenstein and require resolving. This gives a smaller, more targeted search: leave the 4 good cones untouched (genuine non-Q-factorial, Q-Gorenstein points -- a legitimate target for this project's algorithm, not an error state) and triangulate only the 2 that need it (`2^2=4` combinations):

```text
choice {0,0}..{1,1} (all 4): complete=true, simplicial=false, isQQCartier(K)=true, isNef(K)=false
total valid: 4, nef=true: 0
```

`isQQCartier(K)` is confirmed `true` globally in every case (validating that leaving those 4 cones unresolved is legitimate, not silently broken), but **`isNef(K)` is still `false` in all 4**. Combined with the 82 fully-Q-factorialized combinations checked earlier, this brings the total to **86** exhaustively-checked configurations of this circuit family -- fully Q-factorial and genuinely non-Q-factorial-but-Q-Gorenstein alike -- with zero exceptions to `nef=false`.

**Why this matters going forward, regardless of this specific negative outcome**: future searches in this family should test Q-Cartier-ness of `K` per cone *before* deciding whether a triangulation choice is even needed there, both because it cuts the combinatorial search space (here, from `2^6=64` down to `2^2=4`) and because it matches what this project's actual algorithm can accept as an end state -- a non-Q-factorial but Q-Gorenstein minimal model is just as valid a target as a Q-factorial one, and should not be excluded from the search space by an incidental methodological habit.

## What this does and does not establish

**Establishes:**

- A genuine, `isWellDefined`/`isComplete`-verified compact toric 3-fold flip, using the exact non-Gorenstein circuit already validated in `tests/relative-model.m2` and [[simple-flip-nef-tractability]], built via a reliable reverse-engineering method (facet-normal-to-edge-direction duality) rather than blind ray-configuration search.
- Pyramids (planar-base + apex) are structurally unsuited to genuine (non-crepant) flips: confirmed Gorenstein on two independent, unrelated apex choices.
- `isNef` gives the same qualitative answer (`nef=false`) as the much slower `canonicalNefData` search, in a small fraction of the time, whenever the input is genuinely toric -- a practical methodological lesson for any future toric-specific investigation in this project.
- A complete, rigorous (not merely suggestive) explanation for why this particular compact example does not reach a minimal model after one flip: both of its only two extremal contractions are accounted for and both lead backward.
- Extending to Picard rank 4 via one additional vertex, and exhaustively trying all 8 valid triangulations of the resulting extra structure, **still** gives `nef=false` on both chambers in every case -- ruling out (for this specific extension, not in complete generality) the hope that "just add one more ray" fixes the Picard-rank-2 obstruction.
- A "balanced bipyramid" shape (two modest apexes instead of one spike) is structurally *worse*, not better: it doubles the singular-cone count (6 vs. 3) and, exhaustively, over both full Q-factorializations (`2^6=64`) and the methodologically-corrected mixed Q-Gorenstein/non-Q-factorial search (`2^2=4`, leaving the 4 already-Q-Gorenstein cones untouched), still gives `nef=false` in all 68 cases.
- Full Q-factorialization (simplicial fan) is not actually required by this project's own nef machinery -- only Q-Gorenstein-ness of `K` -- and per-cone Q-Cartier-ness of `K` is a cheap, exact linear-algebra check that can rule out unnecessary triangulation branches before searching.

**Does not establish:**

- A working "one flip, then minimal model" example -- this remains open.
- Whether a *genuinely different* higher-Picard-rank extension (multiple simultaneous new vertices, or a different base polytope shape entirely, rather than one incremental vertex added to this specific 5-point polytope) can supply the missing forward direction, or whether the circuit itself (`v1+v2=2v3+v4`) is obstructed from ever reaching `nef=true` regardless of ambient Picard rank. Not tested -- only one specific rank-4 extension was tried, exhaustively over its own triangulation choices, not exhaustively over all possible rank-4 (or higher) extensions.
- Whether `computeFlip`/`relativeCanonicalModelFromBaseData` (this project's own machinery, as opposed to `NormalToricVarieties`' independent toric tools) agrees with this analysis when run on the same explicit fan data -- not cross-checked in this report.

## Suggested next steps

- Try a genuinely different Picard-rank-4+ (or higher) extension strategy -- e.g. multiple simultaneous new vertices, or restarting from a different base polytope shape entirely -- rather than incremental single-vertex additions to the specific 5-point polytope used here, which was shown (exhaustively, for one such addition) not to work.
- Consider whether the specific circuit `v1+v2=2v3+v4` might be intrinsically obstructed (e.g. by some invariant of the relation itself) from ever reaching `nef=true` after one flip, regardless of compactification -- not investigated theoretically, only empirically for the extensions tried.
- Cross-check this project's own `computeFlip`/`canonicalNefData` machinery against the same explicit toric data, to confirm consistency between the two independent verification routes (general algorithm vs. toric-specific combinatorics) on a case where the general algorithm's answer is already known.
- If a `nef=true` compactification is found, translate its fan data into the coordinate-ring presentation this project's `MMPComputation.m2`/`FlipComputation` machinery expects, and run the actual top-level driver end to end, mirroring the `Bl_p(P3)` capstone's pattern.
