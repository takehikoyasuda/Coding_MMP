# Multigraded implementation design

Design note for preserving multigraded presentations inside the implementation,
recorded on 2026-08-13.

## Relation to the paper

The paper does **not** adopt this direction.  `REVISION-PLAN.md` item C-5,
decided on 2026-08-11, keeps the morphism data type as a graph morphism and
keeps `monograded` in the output specification; the only change that entered
the manuscript is that flattening is written as the diagonal subalgebra
`(+)_s S_{sw}` for an ample class `w` rather than as a Segre product.  The
supporting discussion is recorded in the paper's internal development notes,
which are not part of this repository.

This note therefore describes an **implementation-only** change: the package
may keep a multigraded presentation internally, while the paper continues to
specify rank two with flattening at the end of each birational step.  Section 4
of that discussion supplies the data type, and its section 4.6 names the one
construction that does not carry over for free.

The two are consistent because flattening is a device for bounding the rank of
the grading, not a requirement for correctness: ideal-theoretic computations
(Gröbner bases, saturation, primary decomposition, double duals) do not care
about the rank of the grading.

## Measurements

### The threshold search is still linear (paper section 2.1)

`canonicalNefThresholdData` brackets the threshold dyadically, then scans the
finite candidate list **linearly** ([MMPComputation.m2:367](../MMPComputation.m2#L367)).
Measured on `P3`:

| index multiple `a` | numerator bound | #candidates | tests run | cpu |
| --- | --- | --- | --- | --- |
| 1 | 4 | 2 | 6 | 0.25 s |
| 3 | 12 | 12 | 16 | 0.63 s |
| 6 | 24 | 45 | 49 | 2.18 s |

The threshold is `4` in all three, which is the *last* candidate, so the linear
scan pays its worst case.  Every non-nef candidate with `N >= 2` runs the full
multiplier list `{1,...,6}` before concluding.

The predicate is a genuine decision procedure in dimension three: with
`guaranteedMultiplier <= 8` the code sets `trialBound = guaranteedMultiplier`
and tests every multiple up to it, so `nef` holds exactly when `K+tH` is nef,
and the property is monotone in `t`.  Binary search over the candidate list is
therefore valid and would cut 45 tests to about 6.

### The multiplier schedule is already fixed (paper section 2.2)

`multiplierSchedule` runs over **every divisor of `MaxSteps!` in increasing
order**, not over `1!, 2!, 3!, ...`
([flip.m2:25](../third_party/flip-computation/FlipComputation/flip.m2#L25)),
with recorded timings for the gap-filling argument.  The proposed reuse of
`I^(m-1) * I` is moot: `divisorialIdeal` already avoids `SymbolicPowers` and
builds `O_X(-mE)` from ordinary powers and a reflexive hull, which the source
comment measures at about 0.006 s and "essentially flat in `m`"
([divisors.m2:93](../third_party/flip-computation/FlipComputation/divisors.m2#L93)).

So of the two items the discussion ranked above multigrading, one is done and
one (binary search) is outstanding but cheap.

### Multigrading versus flattening on the Segre threefold

`X = P1 x P2`, `D = 2K+H`, computing the sections of `m*D` that the nef test
needs.  Monograded presentation `Q[y0..y5]/I_2(...)`, `H = O(1)`:

| `m` | `OO(m*D)` | `basis(0,-)` |
| --- | --- | --- |
| 1 | 0.013 s | 0.001 s |
| 2 | 0.112 s | 0.041 s |
| 3 | 0.787 s | 0.003 s |
| 4 | 3.94 s | 0.006 s |
| 5 | 14.9 s | 0.011 s |
| 6 | 47.7 s | 0.018 s |

All six have no sections.  The cost is entirely in building the reflexive
module `OO(m*D)`, and it grows by a factor of three to four per step; one
candidate `t` costs about 67 s.

Bigraded presentation `Q[s,t,u,v,w]` with degrees `(1,0),(1,0),(0,1),(0,1),(0,1)`,
`K = O(-2,-3)`, `H = O(1,1)`, sections as multidegree strands:

- the same six tests: **0.0029 s**;
- a full sweep of all 45 candidates in the bracket `(2,4]` with numerators up
  to 24, each running multipliers `1..6`: **0.146 s**, returning the correct
  threshold `lambda = 3`, which agrees with `K+3H = O(1,0)` as recorded in
  [BOTTLENECKS-AND-MULTIGRADING.md](../research-log/docs/BOTTLENECKS-AND-MULTIGRADING.md).

This confirms the diagnosis in that note: the obstruction is the cost of
recovering degree information through Weil-divisor module computations after
flattening, not the size of the effective multiplier.

## A latent correctness problem, not only a cost problem

`isBasePointFreeDivisor` is

```m2
trim baseLocus D == ideal 1_R
```

([MMPComputation.m2:103](../MMPComputation.m2#L103)).  `baseLocus` returns an
ideal of the affine cone.  In the monograded case comparing with the unit ideal
is right, because the irrelevant ideal is the maximal ideal.  In the
multigraded case it is **wrong**, not merely slow.  On `P1 x P2`:

```text
baseLocus(Div s)  = ideal(s,t)      -- but O(1,0) is base-point-free
baseLocus(-K)     = ideal(s,t)^2    -- but -K is base-point-free
```

Both base loci lie in the irrelevant locus.  The correct predicate is

```m2
trim saturate(baseLocus D, B) == ideal 1_R,   B = B_1 * ... * B_r
```

which is the form the tower already uses: the irrelevant ideal of a tower of
weighted projective space bundles is generated by the monomials taking one
variable from each block, i.e. `B = B_1 ... B_r`.

The problem is currently latent: no multigraded ring reaches this predicate,
because `weightedAmpleDivisorData` rejects `degreeLength != 1` first.  A
regression on `P3` confirms the saturated predicate agrees with the existing
one on the monograded path (`m*H` base-point-free for `m = 1..5`, `m*(K+3H)`
not, for `m = 1..3`).

## Where the monograded assumption lives

| Site | Assumption | Action |
| --- | --- | --- |
| [`weightedAmpleDivisorData`](../MMPComputation.m2#L63) | hard error on `degreeLength != 1`; takes `l = lcm(weights)` and `O_X(l)` | **replace** — this is the mathematical gate, section 4.6 below |
| [`isBasePointFreeDivisor`](../MMPComputation.m2#L103) | compares the cone base locus with the unit ideal | generalize by saturating against `B` |
| [`negativeBaseLocusCurveData`](../MMPComputation.m2#L119) | guard returns `null` unless `degreeLength == 1` with standard degrees | leave; it is only a shortcut for high-dimensional fallback bounds |
| [`canonicalScaledNefDataInternal`](../MMPComputation.m2#L211) | none of its own; it consumes `K`, `H` and the predicate | works once `H` and the predicate generalize |
| [`completeLinearSystemGraphData`](../MMPComputation.m2#L420) | hard error on `degreeLength != 1`; collapses source degrees to `{(degree q)#0, 0}` at [line 435](../MMPComputation.m2#L435) | generalize: keep `r` source components and append one target component, giving rank `r+1` |
| [`contractionGraphSmallnessInternal`](../MMPComputation.m2#L762) | already saturates by the product of the two irrelevant ideals | no change expected |

Two things are already in place and reduce the work considerably.

- **`WeilDivisors` is multigraded-capable.**  On `Q[s,t,u,v,w]` with the
  bigraded degrees, `canonicalDivisor(R,IsGraded=>true)` returns
  `-3 Div(u) - 2 Div(s)`, `isCartier` answers `true`, and `basis(deg, OO K)`
  works per multidegree.  Only the base-locus comparison above is wrong.
- **`FlipComputation` already produces degrees with a nonzero lower component.**
  `bigradedReesProjection` builds `Degrees => {{1,-d0}} | udegs | xdegs`, which
  is the `deg x_i = (a_i, c_i)` generalization, and `GraphMorphism` already
  carries an `irrelevantIdeal` field.

`SteinFactorization` is the exception: `blockDegreeData` requires exactly two
blocks with every variable of degree `(positive,0)` or `(0,positive)`, i.e.
block *diagonal* rather than block lower triangular.  Its generalization is the
`r`-variable global Hom of discussion section 4.5.

## The data-type condition

A presentation is admissible when the degree matrix is **block lower triangular
with positive diagonal**: the variables of block `s` have degree zero in every
component `> s` and positive degree in component `s`.  This is mechanically
checkable and the current rank two is the case `r = 2`.  The triangularity is
what makes the existing constructions carry over: the fan definition is
unchanged, and the explicit choices in the surjectivity and injectivity
arguments become back substitution, each block depending only on the previous
ones.

Nothing produced by the algorithm leaves this class: a Rees algebra adds one
block, a product adds a block with zero lower components, and Stein
factorization inherits the rank of its input.  General simplicial toric
varieties are not needed.

## Staged plan

All five stages below were implemented and measured; see
[STAGE1-MEASUREMENT-RESULTS.md](../research-log/docs/STAGE1-MEASUREMENT-RESULTS.md) for the full
stage-by-stage tables.  What follows replaces this section's earlier
(unmeasured) description with what was actually built and the numbers from
running it on `Bl_p(P3)` and Segre `P1 x P2`, both rank `r = 2`.

1. **Admissibility predicate and irrelevant ideal** (`multigradedBlockData`,
   unexported).  Checks block lower triangularity with positive diagonal by
   searching permutations of the degree components, recovers the block
   decomposition, and returns `B = B_1 ... B_r` and the geometric dimension
   `dim R - r`.  Verified against a ring genuinely produced by
   `bigradedReesProjection` on a non-equigenerated ideal (not just a
   hand-written example): the identity permutation already witnesses
   admissibility there, so no reversal of degree components is needed in
   practice, correcting a concern raised while planning this work.  Measured
   cost: 0.0002-0.0007s on both example inputs -- confirmed mechanical.
2. **Generalized the base-point-free predicate** to saturate against `B`,
   with the monograded case as the `r = 1` specialization (confirmed by
   test to reproduce the existing predicate exactly).  A second, independent
   defect was found beyond the one originally diagnosed here: `WeilDivisors`'
   `baseLocus` computes `basis(0,-)` with a bare integer, which does not
   reliably select the degree `(0,...,0)` piece on a ring with
   `degreeLength > 1`; saturating its raw output, as originally planned, is
   not sufficient on its own.  The predicate actually used builds the
   evaluation cokernel directly with an explicit full-length zero-degree
   vector instead of calling `baseLocus` at all.  See section 6 of the
   results document for the concrete failing case this was tested against.
   Measured cost: 0.05-0.39s for the canonical-divisor Cartier/base-point-
   free check on both inputs.
3. **Multigraded ample Cartier class**: the caller supplies it, exactly as
   planned; the open mathematical gate below remains open and was not
   addressed (out of scope for this work order).
4. **Multigraded nef and threshold tests.**  `canonicalScaledNefDataInternal`
   needed only the geometric dimension fix (stage 1) to work multigraded, as
   expected; its base-point-free test was already multigraded-correct via
   stage 2.  The linear candidate scan was replaced by binary search, sharing
   `testCache` with the dyadic bracket phase.  Measured: on `P3` (monograded,
   for direct comparison against previously recorded linear-scan counts),
   `a = 1/3/6` now cost `6/8/10` tests instead of `6/16/49` -- an exact match
   against the previously recorded "before" figures, confirming both the fix
   and its saving.  On the two multigraded inputs, the whole nefness-through-
   threshold chain (stages 1-4) costs 3.68s for `Bl_p(P3)` and 0.40s for
   Segre, and returns the correct thresholds (`lambda = 2` and `lambda = 3`
   respectively).
5. **Flattening at the Stein interface.**  The original plan for this stage
   (keep the source blocks and append the target block, producing rank
   `r + 1`) turned out not to be viable: `SteinFactorization`'s
   `blockDegreeData` requires exactly two blocks, block *diagonal* (every
   variable `(positive,0)` or `(0,positive)`), and generalizing it is
   explicitly out of scope.  What was built instead, matching the later,
   more specific instruction in `research-log/docs/STAGE1-MEASUREMENT-PLAN.md` section 4.5:
   flatten the *source* ring to the diagonal subalgebra of the caller-
   supplied ample class `w` (`diagonalSubalgebraData`, built by reusing
   `WeilDivisors`' `mapToProjectiveSpace(w)` rather than re-deriving it), and
   feed that monograded ring to the existing (unmodified) graph/Stein
   machinery.  Measured cost: 0.041-0.054s for both inputs -- cheap here,
   though this relies on `w` being very ample, true for both measurement
   inputs (it is literally the polarization each was built from) but not
   checked by the code and not tested for `w` merely ample.

Stages 1, 2 and 4 are mechanical, confirmed by measurement (well under a
second each on both example inputs).  Stage 5's interface with Stein
factorization was resolved by flattening at that boundary, also confirmed
cheap here; whichever of the two example inputs reaches a non-trivial Stein
factorization (Segre, contracting to `P1`) exercises it for 0.06s, while
`Bl_p(P3)` with `w = O(1,1)` contracts to a point in one step and skips it
entirely, as anticipated.

## The open mathematical gate

The current ample Cartier divisor comes from the presentation as a subvariety
of a weighted projective space: take `l = lcm` of the weights, use that
`O_X(l)` is invertible and ample, and take a monomial section
(`weightedAmpleDivisorData`, Lemma 3.6 of the paper).  This argument depends
entirely on being embedded in a *singly graded* weighted projective space.

The multigraded replacement chooses a class `w` from the ample cone and needs
two things the monograded argument gets for free:

- that `w` is Cartier, i.e. lies in the Picard group and not merely in
  `Cl (x) Q`;
- that `O(w)` is the honest divisor class, since `O(w)` is a round-down and
  can differ when the weights are not well formed.

Then a section of that multidegree gives the effective divisor.  Discussion
section 4.6 records this as the only construction requiring a fresh write-up
rather than a transcription, and section 7 leaves open how to write the ample
cone inequalities for a general stage of the tower, and how to choose `w`
(minimizing the number of generators, or minimizing the denominator of the next
threshold).

For the implementation this can be staged: accept a caller-supplied `w` with a
checked Cartier certificate first, and add an automatic choice once the cone
description is settled.

## Remaining bottlenecks

Preserving multigrading does not address the items already listed in
[BOTTLENECKS-AND-MULTIGRADING.md](../research-log/docs/BOTTLENECKS-AND-MULTIGRADING.md): relative
canonical models via Rees algebras, ring growth after flips and relative Proj
constructions, the `t=0` pluricanonical search, canonical Cartier index
searches for singular targets, and support-empty tests for general multigraded
modules.  The measurements above only establish that the first nef test, which
is where the current examples stall, becomes cheap.

A follow-up measurement found a further bottleneck neither of this note's two
example inputs exercised: **Stein factorization's own bigraded global Hom
construction (`steinHomData`)**, on a smooth, Cartier-index-1 input, once a
divisorial contraction's target needs more than a couple of embedding
coordinates. Both inputs above avoided this by construction -- `Bl_p(P3)` with
`w=(1,1)` collapsed to a point-target contraction that skips Stein
factorization entirely, and Segre's target had only 2 variables -- not
because the construction is generically cheap. A practical workaround was
then found and confirmed on that same input: the package's existing
guessed-bound entry point (`steinHomDataAtBound`), checked against
independently known target geometry rather than the internal certificate
(a pattern already precedented in
`third_party/SteinFactorizationM2/tests/blowup-twisted-cubic.m2`), turned a
30+ minute unresolved stall into a 1.45-second computation. See
[STEIN-FACTORIZATION-COST-EXPERIMENT-REPORT.md](../research-log/docs/STEIN-FACTORIZATION-COST-EXPERIMENT-REPORT.md).
