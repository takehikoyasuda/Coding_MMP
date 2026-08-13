# Multigraded implementation design

Design note for preserving multigraded presentations inside the implementation,
recorded on 2026-08-13.

## Relation to the paper

The paper does **not** adopt this direction.  `REVISION-PLAN.md` item C-5,
decided on 2026-08-11, keeps the morphism data type as a graph morphism and
keeps `monograded` in the output specification; the only change that entered
the manuscript is that flattening is written as the diagonal subalgebra
`(+)_s S_{sw}` for an ample class `w` rather than as a Segre product.  The
supporting discussion is `references/AlgoMMP/multigrading-vs-flattening.md`.

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
  [BOTTLENECKS-AND-MULTIGRADING.md](BOTTLENECKS-AND-MULTIGRADING.md).

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

1. **Admissibility predicate and irrelevant ideal.**  A function that checks
   block lower triangularity with positive diagonal, recovers the block
   decomposition, and returns `B = B_1 ... B_r`.  Pure bookkeeping, testable
   against the existing bigraded rings from `FlipComputation` and
   `SteinFactorization`.
2. **Generalize the base-point-free predicate** to saturate against `B`, with
   the monograded case as the `r = 1` specialization.  Regressions must show
   agreement with the current predicate on `P3` and the weighted `P(1,1,1,2)`
   case, and correctness on `P1 x P2` where the current predicate is wrong.
3. **Multigraded ample Cartier class.**  The gate; see below.  Until it is
   solved, allow the class to be supplied by the caller so that stages 4 and 5
   can be tested independently.
4. **Multigraded nef and threshold tests.**  `canonicalScaledNefDataInternal`
   should need no change once `H` and the predicate generalize.  Add the binary
   search over the candidate list at the same time, since it is independent and
   free.
5. **Multigraded linear-system graph.**  Keep the source blocks and append the
   target block, producing rank `r+1`.  Pass to a diagonal subalgebra only at
   interfaces that genuinely require a monograded `GraphMorphism`, and record
   which chosen class `w` was used, since the choice determines the weights of
   the next iteration.

Stages 1, 2 and 4 are mechanical.  Stage 5 is where the interface with Stein
factorization has to be decided, and it can be deferred by flattening at that
boundary while the earlier stages are validated.

## The open mathematical gate

The current ample Cartier divisor comes from the presentation as a subvariety
of a weighted projective space: take `l = lcm` of the weights, use that
`O_X(l)` is invertible and ample, and take a monomial section
(`weightedAmpleDivisorData`, Lemma 3.5 of the paper).  This argument depends
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
[BOTTLENECKS-AND-MULTIGRADING.md](BOTTLENECKS-AND-MULTIGRADING.md): relative
canonical models via Rees algebras, ring growth after flips and relative Proj
constructions, the `t=0` pluricanonical search, canonical Cartier index
searches for singular targets, and support-empty tests for general multigraded
modules.  The measurements above only establish that the first nef test, which
is where the current examples stall, becomes cheap.
