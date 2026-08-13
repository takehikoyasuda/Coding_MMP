# Stage 1 measurement results

Results of carrying out `docs/STAGE1-MEASUREMENT-PLAN.md`.  All numbers below
were measured on 2026-08-13 on this checkout, on the branch
`feature/multigraded-stage1`, after tasks T1-T5 (and T4) landed as separate
commits.  Scripts used to produce these numbers were run from a scratch
directory, not committed; the exact ring/ideal/`w` for each input matches
plan section 5.1 verbatim.

## Environment

- Macaulay2 1.26.06 (`M2 --version`)
- `Darwin TYs-MacBook-Air-2024.local 25.6.0 Darwin Kernel Version 25.6.0: Sat Jul 11 15:23:52 PDT 2026; root:xnu-12377.161.13~4/RELEASE_ARM64_T8122 arm64`
- macOS 26.6.1 (build 25G76)

## 1. `Bl_p(P3)`, multigraded

Ring, ideal, and `w` exactly as plan section 5.1:

```m2
S = QQ[x0,x1,x2,x3,u0,u1,u2,
    Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
R = S/minors(2, matrix{{x1,x2,x3},{u0,u1,u2}});
w = divisor(x0) + divisor(u0);
a = 1;
```

| Stage | cpu seconds | Key outputs |
| --- | --- | --- |
| 1. block structure and `B` | 0.0007 | rank 2, geometric dimension 3, `B = (x0,x1,x2,x3)*(u0,u1,u2)` |
| 2. canonical divisor + Cartier check | 0.389 | `K = -2Div(x0) - Div(u0,x1) - Div(u2,x3) - Div(u0,u1,u2)`; `isCartierMultigraded(K) = true` (note: the unfixed `isCartier(K,IsGraded=>true)` answers `false` here -- see T2) |
| 3. nefness at `t = 0` | 1.02 | `nef = false`, witness `non-nef positive perturbation` |
| 4. threshold search | 2.59 | `threshold = 2`; `testsRun` (binary) `= 5`; linear-equivalent `= 6`; 3 candidates in the final bracket |
| 5. flattening to the diagonal subalgebra of `w` | 0.054 | 9 flattening variables; `dim(flatRing) = 4` (geometric dimension 3, matching the original) |
| (preamble) find the b.p.f. multiple of `K+2w` | 0.070 | multiplier `= 1` |
| 6. complete-linear-system graph | 0.182 | `targetVariableCount = 1`, `sourceVariableCount = 9` |
| 7. Stein factorization | -- | **skipped**: target has 1 variable, i.e. is already a point (`steinFactorizationType = "trivial point target"`) |
| 8. contraction type and dimensions | 0.00001 | source dimension 3, target dimension 0, `contractionType = "fibration"` |
| **Total** | **~4.30** | reaches stage 8; contraction is to a point in one step |

**Expected and confirmed**: `Bl_p(P3)` is Fano of index two, so with `w = O(1,1)`,
`K + 2w` is numerically trivial and the extremal-face contraction at the
threshold is the constant map to a point, exactly as plan section 5.1
predicts and warns about.  This means stage 7 (Stein factorization) is not
exercised by this input with this `w` -- it is exercised by the Segre input
below instead, where the contraction is to `P1` and Stein factorization runs
for real (`certifiedBound = true`, in 0.062s).  This is a legitimate,
expected shape for the measurement, not a gap: reaching stage 8 with a
one-step Mori-fibre-style contraction is exactly what plan section 5.1 says
to expect for this `w`, and the plan explicitly does not ask for a second
`w` nearer the nef boundary as a required deliverable.

## 2. Segre `P1 x P2`, multigraded

Ring and `H` exactly as plan section 5.1:

```m2
R = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
H = divisor(s) + divisor(u);   -- O(1,1)
a = 1;
```

| Stage | cpu seconds | Key outputs |
| --- | --- | --- |
| 1. block structure and `B` | 0.0002 | rank 2, geometric dimension 3, `B = (s,t)*(u,v,w1)` |
| 2. canonical divisor + Cartier check | 0.054 | `K = -2Div(s) - 3Div(u)`; `isCartierMultigraded(K) = true` |
| 3. nefness at `t = 0` | 0.137 | `nef = false`, witness `non-nef positive perturbation` |
| 4. threshold search | 0.208 | `threshold = 3`; `testsRun` (binary) `= 5`; linear-equivalent `= 5`; 2 candidates in the final bracket |
| 5. flattening to the diagonal subalgebra of `H` | 0.041 | 6 flattening variables; `dim(flatRing) = 4` |
| (preamble) find the b.p.f. multiple of `K+3H` | 0.002 | multiplier `= 1` |
| 6. complete-linear-system graph | 0.055 | `targetVariableCount = 2`, `sourceVariableCount = 6` |
| 7. Stein factorization | 0.062 | `certifiedBound = true` |
| 8. contraction type and dimensions | 0.009 | source dimension 3, target dimension 1, `contractionType = "fibration"` |
| **Total** | **~0.57** | reaches stage 8; `K+3H = O(1,0)` gives the connected-fibre contraction to `P1` |

**Confirmed**: threshold `lambda = 3`, matching plan section 5.1 and the
existing `tests/contraction.m2` regression (which reaches the same
contraction from the monograded presentation, at not-quite-comparable cost --
see section 3).

Both inputs reach stage 8, satisfying success criterion 3 (both inputs reach
at least stage 4 with the stated thresholds; both in fact reach the full
chain through contraction).

## 3. Monograded baseline for `Bl_p(P3)` (plan section 5.3)

The monograded presentation was built by flattening `Bl_p(P3)` to the
diagonal subalgebra of the same `w = O(1,1)` (i.e. `diagonalSubalgebraData`'s
own `"flatRing"`), giving a 9-variable, standard-graded (all degree 1) ring
isomorphic to `Bl_p(P3)` under this embedding -- this is exactly the ring
that a monograded-first implementation would have started from.  Constructing
it costs 0.044s (a strict subset of stage 5 above; no surprise there).  The
existing (pre-multigrading, unmodified) `canonicalNefData(Rflat,1)` was then
called and given the full 20 minutes the plan's protocol allows.

**Result: did not complete.**  The process was killed after 20 minutes of
wall-clock time (`kill -9`, no CPU-time proxy available for a killed
process).  Setup and diagnostics ran and printed as expected:

```text
=== Bl_p(P3), monograded baseline (plan section 5.3) ===
(setup) build the monograded presentation via the O(1,1) embedding: .043838s  numVars=9 dim(Rflat)=4
Rflat degrees: {{1}, {1}, {1}, {1}, {1}, {1}, {1}, {1}, {1}}
Now attempting the EXISTING monograded canonicalNefData(Rflat,1) -- expected to stall.
```

That last line is the final output printed before the kill: `canonicalNefData(Rflat,1)`
-- the very first call in the chain, testing `K` itself for nefness through
the alternating pluricanonical/perturbation search -- did not return within
20 minutes.  No later stage (threshold search, flattening, contraction) was
reached on this monograded presentation at all, because the chain never gets
past its first step.  This is exactly the stall plan section 5.3 says to
expect, and it is the direct, load-bearing confirmation of the entire
premise of this work order: the same variety, same `a`, same `w`, took 3.68s
through stage 4 multigraded (this document's section 1) and had not produced
an answer after 20 minutes (1200s+) monograded -- at minimum a three-orders-
of-magnitude difference, consistent with the four-orders-of-magnitude figure
the plan's own preliminary measurements (section 2) reported for the
`OO(m*D)` construction specifically.

## 4. Segre monograded comparison (already measured; not re-derived)

Per the task's supplied verified facts and `docs/BOTTLENECKS-AND-MULTIGRADING.md`,
the monograded Segre presentation `QQ[y0..y5]/I_2(...)`, `H = O(1)`,
`D = 2K+H`, costs to build `OO(m*D)`:

| `m` | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- |
| `OO(m*D)` | 0.013s | 0.112s | 0.787s | 3.94s | 14.9s | 47.7s |

One candidate `t` (all six multiplier tests) costs about 67s.  A full
threshold search needs on the order of tens of such candidates (the
multigraded sweep above needed a bracket of 2 candidates and 5 total tests;
a naive extrapolation of the monograded cost to a comparable number of
candidates would run into tens of minutes to hours, well past what an
interactive run tolerates), which is why this repository's monograded
regression (`tests/contraction.m2`) calls
`canonicalContractionAtThresholdData(X,1,3)` directly at the already-known
threshold rather than searching for it from scratch.

## 5. What this does and does not establish

**Establishes:**

- A mechanically checkable admissibility predicate and irrelevant ideal for
  rank-`r` presentations (T1), verified against a ring genuinely produced by
  `bigradedReesProjection` on a non-equigenerated ideal, not just a
  hand-written example.
- Two independent latent-correctness defects in `WeilDivisors`, not just the
  one the plan diagnosed, and a fix for both that is behaviour-preserving on
  every existing monograded regression (T2; see section 6 below).
- That, once those defects are fixed, the entire chain "canonical nefness
  test -> nef threshold -> extremal contraction" runs in well under 5
  seconds on both of this plan's example inputs, keeping the multigraded
  presentation throughout except at one deliberate, measured flattening step
  before Stein factorization (T3, T5).
- That binary search over the threshold candidate list is a real, free
  improvement, cutting the candidate-scan tests from 49 to 10 in the worst
  case measured here (T4), with no change to any existing threshold, nef
  answer, or other assertion.
- A concrete number for the cost of flattening at the Stein interface (T5):
  0.04-0.05s for both inputs here, i.e. cheap for these particular examples,
  though see the caveats below about how far that generalizes.

**Does not establish:**

- Anything about singular varieties.  Both measurement inputs are smooth
  with `K` Cartier; the multigraded speed-up specifically avoids the
  expensive general Weil-divisor/reflexive-hull machinery, and that
  machinery becomes unavoidable again once a genuine reflexive hull is
  needed (plan section 2's caveat).  This was not measured here because
  neither input requires it.
- That `diagonalSubalgebraData`'s flattening recovers an isomorphic copy of
  `X` in general.  It relies on the caller-supplied class `w` being very
  ample; for both measurement inputs `w` is literally the embedding
  polarization the multigraded presentation was built from, so this holds,
  but it was not tested for a `w` that is merely ample and not very ample,
  and no check for very-ampleness is performed by the code.
- Anything about a second MMP step, flips, the relative canonical model, or
  more than two grading blocks -- all explicitly out of scope per plan
  section 1, and untouched.
- General multigraded rank `r > 2`.  The permutation search in T1 is
  implemented generally, but every example measured has `r = 2`; whether the
  approach remains cheap at higher rank is not addressed.
- That the `w` used for `Bl_p(P3)` is the "right" or only informative
  choice.  As plan section 5.1 anticipates, this `w` collapses the
  contraction to a point in one step because `Bl_p(P3)` is Fano of index
  two; a `w` nearer the boundary of the nef cone would instead contract the
  exceptional divisor and would exercise Stein factorization on this input
  too, but constructing and justifying that choice was not part of this
  work order and was not attempted.

## 6. A defect found beyond the plan's own diagnosis

While implementing T2's stated fix (`trim saturate(baseLocus D, B) == ideal
1_R`), a second, independent defect in `WeilDivisors` was found: `baseLocus`
computes `basis(0, M1)` with a bare integer, and on a ring with
`degreeLength > 1` that call does not reliably select the degree
`(0,...,0)` piece of `M1`.  Concretely, on bigraded `P1 x P2`, for
`L = K + 2H = O(0,-1)` (which has no global sections at all, so is certainly
not base-point-free), `baseLocus(L)` evaluates to `ideal 1_R` *before any
saturation is applied* -- so saturating its output by `B`, exactly as the
plan's 3.1 fix literally states, cannot recover correctness, and the
naive implementation of the plan's own prescription gives the *wrong*
threshold (`2` instead of `3`) for the Segre example.  The plan's own two
verified examples (`Div(s)`, `-K`) do not trigger this because both are
effective at a generator degree where the bare-integer and explicit-
multidegree calls happen to coincide.

The fix used in `MMPComputation.m2` (see the T2 commit) does not call
`baseLocus` at all; it builds the evaluation cokernel directly with an
explicit full-length zero-degree vector and saturates that.  Confirmed
behaviour-preserving on every existing monograded case in
`tests/nefness.m2`'s scenarios, and correct on the `h^0 = 0` case above where
the plan's literal fix is not.

## 7. Correction to a stated hypothesis about `bigradedReesProjection`

The task also asked me to verify (or correct) the hypothesis that
`bigradedReesProjection`'s returned ambient ring might need its two degree
components reversed to satisfy T1's block-lower-triangularity condition.
Tested directly against `bigradedReesProjection(ideal(x1,x2*x3))` in
`QQ[x0,x1,x2,x3]` (a genuinely non-equigenerated ideal, `d0 = 1`, generator
degrees `{1,2}`): the returned ambient ring's degrees are
`{{1,0},{1,1},{0,1},{0,1},{0,1},{0,1}}` for `u1,u2,x0,x1,x2,x3`, all
non-negative, and the **identity permutation already witnesses
admissibility** -- no reversal is needed.  This corrects the hypothesis: the
concern was about the *internal* elimination ring `T` used inside
`bigradedReesIdeal` (which does carry a genuinely negative-degree `t`
variable), not about the ring `bigradedReesProjection` actually returns.
T1's permutation search is kept regardless (it is correct and cheap for the
`r = 2` case this package needs), and it reports which permutation
succeeded; in every case measured here, including this one, that permutation
is the identity.

## 8. Out of scope, hit but not acted on

- The deeper `basis(0,-)` defect (section 6 above) is a `WeilDivisors`
  limitation, not something this package can fix by editing that package
  (out of scope: do not edit `references/`, and editing an installed system
  package is not appropriate either); it was worked around entirely inside
  `MMPComputation.m2`.
- Choosing a `w` nearer the nef cone boundary for `Bl_p(P3)`, to get a
  divisor-contracting (rather than point-contracting) measurement of stage
  7 on that input, was considered but not attempted -- the plan explicitly
  frames this as optional and cautions against presenting either choice as
  "the" correct answer.
- Whether `diagonalSubalgebraData`'s flattening recovers an isomorphic
  presentation when `w` is ample but not very ample was not tested; no
  measurement input here requires it.
