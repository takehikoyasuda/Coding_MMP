# Stage 1 measurement plan: the first MMP step on a multigraded presentation

Work order written on 2026-08-13.  It is self-contained: everything needed to
carry it out is stated here or in the files it names.

## 0. One-paragraph summary

Several geometrically interesting threefolds currently stall in the very first
`canonicalNefData` call because their natural presentation is multigraded and
the package flattens it to a single grading, after which global sections have to
be recovered through expensive Weil-divisor module computations.  Measurements
(section 2) show that keeping the multigraded presentation makes exactly that
computation about four orders of magnitude cheaper.  This work order asks you to
make the minimum set of changes that lets **one full MMP step** run on a
multigraded input, and to measure it.  It is a measurement exercise: the point
is to replace an estimate with a number.

## 1. Goal, scope, non-goals

**Goal.**  On a multigraded presentation, run and time the chain

```text
canonical nefness test  ->  nef threshold  ->  extremal contraction
```

for two inputs that currently do not complete, and record per-stage timings.

**In scope.**

- A block-structure predicate and the irrelevant ideal `B` for multigraded rings.
- Saturated versions of the three `WeilDivisors` predicates listed in section 3.
- The geometric-dimension fix of section 3.4.
- Timing harness and a results table.

**Explicitly out of scope.  Do not attempt these.**

- Choosing the ample class automatically.  The caller supplies it; see 3.5.
- Generalizing `SteinFactorization` to more than two blocks.  Flatten at that
  interface instead; see 4.5.
- The relative canonical model, flips, `mmpStepRecordData`, or the second MMP
  step.
- Any change to `references/AlgoMMP`.  The paper deliberately keeps rank two
  (decision C-5 in its `REVISION-PLAN.md`); this is an implementation-only
  experiment.  Do not edit the paper submodule.
- Rewriting `threefoldMMPData`.

If you find yourself needing something out of scope to make progress, stop and
report it rather than expanding the change.

## 2. Verified facts — do not re-derive these

All measured on 2026-08-13 with Macaulay2 1.26.06 on this checkout.

**The flattened path is the bottleneck.**  Segre threefold `P1 x P2` presented
monograded as `QQ[y0..y5]/I_2(...)`, `H = O(1)`, `D = 2K+H`; cost of building
`OO(m*D)`, whose sections the nef test needs:

| `m` | 1 | 2 | 3 | 4 | 5 | 6 |
| --- | --- | --- | --- | --- | --- | --- |
| `OO(m*D)` | 0.013 s | 0.112 s | 0.787 s | 3.94 s | 14.9 s | 47.7 s |

`basis` itself is never more than 0.041 s.  One candidate `t` costs about 67 s.

**The multigraded path is cheap.**  Same variety as `QQ[s,t,u,v,w]` with degrees
`(1,0),(1,0),(0,1),(0,1),(0,1)`, `K = O(-2,-3)`, `H = O(1,1)`, sections as
multidegree strands: the same six tests cost **0.0029 s**, and a sweep of all 45
candidates in the bracket `(2,4]` costs **0.146 s** and returns the correct
threshold `lambda = 3`.

**It stays cheap for a subvariety, not just for a product.**  Flag threefold,
the `(1,1)` hypersurface in `P2 x P2`: `OO(m*D)` costs 0.032 s at `m=1` and under
0.001 s for `m = 2..6`.

**Caveat you must respect.**  Both are smooth with `K` Cartier.  Nothing has been
measured on a singular variety, where a genuine reflexive hull is unavoidable
even multigraded.  Do not claim the win extends there; measure it if your inputs
happen to be singular.

**The threshold search is a linear scan.**  `canonicalNefThresholdData` brackets
dyadically and then scans candidates linearly
([MMPComputation.m2:367](../MMPComputation.m2#L367)).  On `P3` it runs 6 / 16 /
49 tests for `a = 1 / 3 / 6` against 2 / 12 / 45 candidates.  Binary search is
valid — see 4.4 — but is a **secondary** task here.

## 3. Four known defects, with verified diagnoses

Three of these are the same defect: a `WeilDivisors` predicate compares an ideal
of the affine cone with the unit ideal.  That is correct when the irrelevant
ideal is the maximal ideal, i.e. only in the monograded case.  Multigraded, the
cone ideal must first be **saturated against the irrelevant ideal**

```text
B = B_1 * B_2 * ... * B_r,   B_s = ideal of the block-s variables.
```

Each diagnosis below was confirmed by running it.

### 3.1 Base-point-freeness

[`isBasePointFreeDivisor`](../MMPComputation.m2#L103) is
`trim baseLocus D == ideal 1_R`.  On the bigraded `P1 x P2`:

```text
baseLocus(Div s)  = ideal(s,t)      -- but O(1,0) IS base-point-free
baseLocus(-K)     = ideal(s,t)^2    -- but -K IS base-point-free
```

Both lie in the irrelevant locus.  Fix: `trim saturate(baseLocus D, B) == ideal 1_R`.

### 3.2 The Cartier test

`isCartier(a*K, IsGraded=>true)` gates every entry point
([MMPComputation.m2:280](../MMPComputation.m2#L280),
[:299](../MMPComputation.m2#L299), [:499](../MMPComputation.m2#L499),
[:904](../MMPComputation.m2#L904), [:1053](../MMPComputation.m2#L1053)).  On the
bigraded `Bl_p(P3)` of section 5.1 — a **smooth** variety, so `K` is certainly
Cartier — it returns `false`, and the multigraded path would die at the gate with
"a*K_X is not Cartier".  The cause is the same:

```text
nonCartierLocus(K)                  = ideal(u2,u1,u0,x3,x2,x1)
trim saturate(nonCartierLocus K, B) = ideal 1
```

Fix: test `trim saturate(nonCartierLocus(D, IsGraded=>true), B) == ideal 1_R`
instead of `isCartier`.  Note `nonCartierLocus` is a `WeilDivisors` export with
only a `WeilDivisor` method, so convert `BasicDivisor` inputs accordingly.

### 3.3 Base locus of the negative-curve shortcut

[`negativeBaseLocusCurveData`](../MMPComputation.m2#L119) already guards on
`degreeLength == 1` and returns `null` otherwise.  **Leave it alone.**  It is
only a shortcut for high-dimensional fallback bounds and is not used in
dimension three, where `guaranteedMultiplier <= 8`.

### 3.4 Geometric dimension

`d := dim R - 1` at [MMPComputation.m2:216](../MMPComputation.m2#L216) and
[:303](../MMPComputation.m2#L303) is wrong for rank `r`: the geometric dimension
is `dim R - r`.  On the flag threefold `dim R - 1` gives 4 where the answer is 3.
This `d` feeds `effectiveNefMultiplier(d,N)` and the numerator bound `a*(d+1)`,
so the error is silent and gives the wrong guaranteed multiplier.  Verified:
`dim R - r` gives 3 for `P1 x P2`, the flag threefold, and `Bl_p(P3)`, and 3 for
`P3` with `r = 1`.

`FlipComputation` has a `geometricDimension` method but only for
`B2MProjection` ([basics.m2:30](../third_party/flip-computation/FlipComputation/basics.m2#L30)),
so you need a ring-level version; do not try to reuse that one.

### 3.5 The ample class is an input, not a computation

[`weightedAmpleDivisorData`](../MMPComputation.m2#L63) errors on
`degreeLength != 1` and takes `l = lcm(weights)` with `O_X(l)`.  That argument
depends entirely on being embedded in a *singly graded* weighted projective
space and does not generalize; constructing the multigraded replacement is an
open mathematical question (see [MULTIGRADED-DESIGN.md](MULTIGRADED-DESIGN.md)
section "The open mathematical gate").

**Therefore: the caller supplies the class.**  Accept an ample Cartier class,
verify it with the saturated Cartier test of 3.2 and the saturated
base-point-freeness test of 3.1, and proceed.  Do not attempt to derive it.

## 4. Implementation tasks

Work in `MMPComputation.m2` unless stated otherwise.  Keep every new entry point
additive: **the existing monograded code paths and their outputs must not
change.**  Re-run `make test-core` after each task.

### T1. Block structure and irrelevant ideal

Add an unexported helper returning, for a ring `R`:

- `r = degreeLength ambient R`;
- the partition of the variables into blocks;
- `B = B_1 * ... * B_r`;
- the geometric dimension `dim R - r`.

Admissibility is that the degree matrix is **block lower triangular with
positive diagonal**: the variables of block `s` have degree zero in every
component `> s` and positive degree in component `s`.  Construct the blocks as
"variables whose last nonzero degree component is `s`", then check that
component is positive.

**Watch out:** the block order need not match the variable order, and the
component order may need reversing.  `bigradedReesProjection` builds
`Degrees => {{1,-d0}} | udegs | xdegs`
([rees.m2:71](../third_party/flip-computation/FlipComputation/rees.m2#L71)),
where the fibre variables carry a *negative* base component; that ring is block
lower triangular only after reversing the two degree components.  So search over
permutations of the degree components (for `r = 2` there are two) and accept the
ring if any permutation works, reporting which.  Verify your helper against a
ring actually produced by `bigradedReesProjection`, not against a hand-written
example.

`r = 1` must be admissible and reproduce the current behaviour: `B = ideal vars R`,
geometric dimension `dim R - 1`.

For a `GraphMorphism` or `B2MProjection` in hand, prefer its existing
`irrelevantIdeal` field over recomputing.

### T2. Saturated predicates

Add multigraded-correct versions of 3.1 and 3.2 that take `B` (or derive it via
T1).  Keep `isBasePointFreeDivisor` exported and behaviour-compatible for `r = 1`;
the cleanest route is to make it delegate to the saturated version with `B`
computed by T1, since for `r = 1` saturating against `ideal vars R` is a no-op on
an already-saturated base locus.  **Confirm that claim by test, do not assume it.**

### T3. Multigraded nef and scaled nef tests

Give `canonicalScaledNefDataInternal` and its callers the geometric dimension
from T1 instead of `dim R - 1`, and let them take the ample class as an argument
rather than calling `weightedAmpleDivisorData`.  Add entry points that accept a
multigraded ring plus a caller-supplied ample Cartier divisor.  The internal
logic should not otherwise need changing.

Keep the result hash-table keys identical to the existing ones so the harness and
any later code can read both.

### T4. Threshold search (secondary — do T5 first if time is short)

`canonicalNefThresholdData` should work once T3 lands.  Additionally, replace the
linear candidate scan at [MMPComputation.m2:367](../MMPComputation.m2#L367) with
binary search.

Validity, which you may rely on: in dimension three `guaranteedMultiplier <= 8`,
so `trialBound = guaranteedMultiplier` and every multiple up to it is tested;
`nef` therefore holds exactly when `K+tH` is nef, and nefness is monotone in `t`.
The candidate list is sorted and contains the threshold, so the first candidate
that tests nef is the threshold.  Keep `testCache` so the bracket's tests are
reused.  Record `testsRun` both ways in the report.

If binary search changes any existing expected value, stop — that indicates the
monotonicity assumption fails somewhere and is worth reporting rather than
patching.

### T5. Contraction, flattening at the Stein interface

[`completeLinearSystemGraphData`](../MMPComputation.m2#L420) errors on
`degreeLength != 1` and collapses source degrees to `{(degree q)#0, 0}` at
[line 435](../MMPComputation.m2#L435).

`SteinFactorization` cannot help you here: `blockDegreeData` requires **exactly
two blocks** with every variable of degree `(positive,0)` or `(0,positive)`.  A
multigraded source of rank `r` would give a graph of rank `r+1`.

**So flatten at this interface, deliberately and visibly.**  Pass to the diagonal
subalgebra for the supplied ample class `w` — take the subring generated by the
degree-`w` strand — and hand the resulting singly graded ring to the existing
contraction code.  Record the flattening as its own timed stage in the results.
Do not try to avoid it; measuring its cost is one of the deliverables.

## 5. Measurement protocol

Put scripts under `tests/` only if they become regressions; otherwise use a
scratch directory and do not commit them.

### 5.1 Inputs

**`Bl_p(P3)`**, the graph closure in `P3 x P2`.  Verified to work:

```m2
S = QQ[x0,x1,x2,x3,u0,u1,u2,
    Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
R = S/minors(2, matrix{{x1,x2,x3},{u0,u1,u2}});
B = ideal(x0,x1,x2,x3) * ideal(u0,u1,u2);
w = divisor(x0) + divisor(u0);          -- the class O(1,1), ample and Cartier
```

Verified properties: `degreeLength = 2`, `dim R = 5`, geometric dimension 3,
`w` is Cartier, `w` is base-point-free under the saturated test and **not** under
the current unsaturated one.  Scaled nef tests, saturated, cost 0.2–0.5 s each
and give

| `t` | `h0(m*(K+t*w))`, `m = 1..6` | nef |
| --- | --- | --- |
| 1 | `0,0,0,0,0,0` | false |
| 2 | `1,1,1,1,1,1` | true |
| 3 | `9,31,74,145,251,399` | true |

so the threshold is `lambda = 2`.

**Expect and report this:** `K + 2w` is numerically trivial — `h0(m*(K+2w)) = 1`
for all `m`, and `-K = 2w` since `h0(-K) = h0(O(2,2)) = 31`.  `Bl_p(P3)` is Fano
of index two, so with this `w` the contraction at the threshold is the map to a
point in **one** step.  That is a *legitimate* output of this algorithm, not a
bug: the paper does not compute the Picard number or the Mori cone, allows
contracting a face of dimension at least two, and calls the final map a
`K`-negative fibration rather than a Mori fibre space (`AlgoMMP.tex`, the
paragraphs near lines 383 and 489).  It does mean the choice of `w` decides how
informative the run is.  If you want a step that contracts the exceptional
divisor instead, try a `w` nearer the boundary of the nef cone, report which you
used, and do not present either as the "correct" answer.

**Segre `P1 x P2`**, the second input:

```m2
R = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
B = ideal(s,t) * ideal(u,v,w1);
```

with the ample Cartier class `O(1,1)`.  Threshold `lambda = 3`,
`K + 3H = O(1,0)`, and the connected-fibre contraction goes to `P1`.

### 5.2 What to record

For each input, one row per stage: **stage name, cpu seconds, and the key
outputs** (threshold, tests run, candidate count, contraction source/target
dimensions, contraction type).  Stages:

1. block structure and `B`
2. canonical divisor and the Cartier check
3. nefness at `t = 0`
4. threshold search — report `testsRun` for both linear and binary scan
5. flattening to the diagonal subalgebra
6. complete-linear-system graph
7. Stein factorization
8. contraction type and dimensions

Use `cpuTime()` differences and flush after each line so a stall leaves a
partial record.  **If a stage does not return within 20 minutes, kill it and
record it as "did not complete", with the last line printed.**  A stall that is
recorded and located is a successful outcome of this work order; an unrecorded
one is not.

### 5.3 Comparison baseline

For `Bl_p(P3)` also attempt the current monograded route so the table has a
before-and-after.  It is expected to stall; give it 20 minutes and record where.

## 6. Success criteria

1. `make test-core` and `make test-upstreams` pass unchanged.
2. The saturated predicates agree with the current ones on every monograded case
   in `tests/nefness.m2`.
3. Both inputs reach at least stage 4 (threshold) with recorded timings, and the
   thresholds are `lambda = 2` for `Bl_p(P3)` with `w = O(1,1)` and `lambda = 3`
   for Segre.
4. A results table exists for every stage, including any that did not complete.
5. `docs/MULTIGRADED-DESIGN.md` is updated with the measured numbers, replacing
   the estimates in its "Staged plan" section.

Criterion 3 is the measurement this work order exists for.  Reaching stage 8 is
desirable but not required — if the contraction stalls after flattening, that
result is itself the answer to the question being asked.

## 7. Pitfalls

- **Do not compare a cone ideal with `ideal 1_R` without saturating.**  This is
  the root cause of two of the four defects; assume any other such comparison you
  find is also wrong multigraded.
- **Do not use `dim R - 1`.**  See 3.4.
- **Do not assume `isCartier` is right.**  See 3.2.
- **Do not derive the ample class.**  See 3.5.
- **Do not change the monograded outputs.**  Every existing regression asserts
  specific values; if one moves, that is a defect in your change, not in the test.
- **Do not extend `SteinFactorization` to three blocks.**  See T5.
- The paper submodule is pinned and read-only for this task.
- Report negative results plainly.  If multigrading does not help one of the
  stages, say so with the number; that is the deliverable, not a failure.

## 8. Deliverable

1. The code changes, each task a separate commit on a branch (do not commit to
   `main`).
2. A results file `docs/STAGE1-MEASUREMENT-RESULTS.md` containing the tables of
   5.2 and 5.3, the environment (M2 version, machine), and a short section
   "what this does and does not establish".
3. The update to `docs/MULTIGRADED-DESIGN.md` required by criterion 5.
4. A list of anything you hit that was out of scope, without acting on it.

Do not commit or push unless asked.
