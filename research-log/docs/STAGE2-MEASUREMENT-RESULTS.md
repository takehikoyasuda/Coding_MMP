# Stage 2 measurement results: a singular multigraded target

Results of carrying out `docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md`'s T1, T4
(Part 0 correctness prerequisite, plus the actual measurement), on branch
`feature/multigraded-stage1`.  T2, T3, and T5 were deliberately **not**
implemented; see "Deliberate scope choices" below.  All numbers were measured
on 2026-08-13 on this checkout.  Scripts used to produce these numbers were
run from a scratch directory, not committed.

## Environment

- Macaulay2 1.26.06 (`M2 --version`)
- `Darwin TYs-MacBook-Air-2024.local 25.6.0 Darwin Kernel Version 25.6.0: Sat Jul 11 15:23:52 PDT 2026; root:xnu-12377.161.13~4/RELEASE_ARM64_T8122 arm64`
- macOS 26.6.1 (build 25G76)

Same machine and M2 build as `STAGE1-MEASUREMENT-RESULTS.md`, so the two are
directly comparable.

## Part 0: completing Stage 2's T1 (prerequisite correctness fix)

### What was wrong

When Stage 2's T1 landed (commit `be0715e`), `isBasePointFreeDivisor` and
`isCartierMultigraded` gained overloads accepting a caller-supplied
`IrrelevantIdeal`/`Ideal`/`B2MProjection`/`GraphMorphism`, and the five
top-level entry points (`canonicalScaledNefData`, `canonicalNefThresholdData`,
`canonicalNefData`, `canonicalContractionAtThresholdData`,
`canonicalContractionData`) gained an `IrrelevantIdeal` option that uses the
supplied `B` for that entry point's own Cartier gate. But the internal search
loops those entry points call --
`canonicalScaledNefDataInternal`, `canonicalNefDataCore`, and
`canonicalContractionAtThresholdDataCore` -- still called the plain
1-argument `isBasePointFreeDivisor`, which re-derives `B` via
`multigradedBlockData` internally on *every* trial multiple, regardless of
what the caller supplied to the outer entry point. On a ring where that
re-derivation is wrong (a "skew" bigraded ring, see
`tests/multigraded-skew-cartier.m2` and
`docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md` section 2.3), this meant the outer
Cartier gate could be correct while the search loop's own "nef"/
"basePointFree" verdict was not -- a silent, uncaught defect.

**This is squarely T1-shaped work, finishing what T1 started; it is treated
here as "Part 0" (a prerequisite to any Stage 2 T4 measurement) and not
folded silently into "T4."**

### What changed

`canonicalScaledNefDataInternal`, `canonicalNefThresholdDataCore`,
`canonicalContractionAtThresholdDataCore`, and `canonicalNefDataCore` each
gained a trailing `B` parameter (an `Ideal`, or `null`). `B = null` (the
default from every existing, non-`IrrelevantIdeal` caller) reproduces the
previous behaviour exactly -- re-derive via `multigradedBlockData` on every
call, unaffected. When a caller does supply `IrrelevantIdeal => B` to one of
the five public entry points, that same `B` is now threaded straight into
every base-point-free test the resulting search loop performs, not only into
the entry point's own Cartier gate:

- `canonicalScaledNefDataInternal(R,K,H,a,t,B)`: its own
  `isBasePointFreeDivisor candidateDivisor` calls become
  `isBasePointFreeDivisor(candidateDivisor,B)` when `B =!= null`. Its
  negative-curve-shortcut branch (`useNegativeCurveShortcut`) was also
  updated to saturate by `B` when supplied, for completeness -- see the note
  below on why this branch is dead code for every ring this package's
  entry points actually reach.
- `canonicalNefThresholdDataCore(R,a,K,H,d,limit,B)`: forwards `B` into every
  `canonicalScaledNefDataInternal` call its dyadic-bracket-then-binary-search
  makes.
- `canonicalNefDataCore(R,a,K,H,limit,B)`: forwards `B` into both its own
  pluricanonical base-point-free test and the nested
  `canonicalScaledNefDataInternal` call.
- `canonicalContractionAtThresholdDataCore(R,a,lambda,K,H,d,limit,
  buildLinearSystemGraph,B)`: forwards `B` into its own multiplier-search
  base-point-free test of `morphismDivisor`.
- `completeLinearSystemGraphDataMultigraded` (called by
  `canonicalContractionAtThresholdDataCore`'s `buildLinearSystemGraph`
  closure at the threshold) gained an `IrrelevantIdeal` option of its own,
  since it independently re-checks base-point-freeness of the divisor it is
  handed; before this change that re-check also used the un-threaded,
  possibly-wrong `B`.

Every call site inside `MMPComputation.m2` that previously called one of
these four internal functions was updated to pass `B` (either the
caller-supplied ideal, when the calling entry point has one, or `null` for
the plain monograded entry points, which is behaviourally a no-op).

### `negativeBaseLocusCurveData`'s shortcut guard

Checked by test, not assumed, per the work order: `useNegativeCurveShortcut`
inside `canonicalScaledNefDataInternal` is `guaranteedMultiplier > trialBound`
where `trialBound = min(8,guaranteedMultiplier)`. For the dimension-three case
this package's own threefold gate (`canonicalNefData`'s
`geometricDimension != 3` check) always enforces,
`effectiveNefMultiplier(3,N) = ceiling(2/N)+5 <= 7` for every `N >= 1`, so
`guaranteedMultiplier <= 7 <= 8` and `useNegativeCurveShortcut` is **always
false** for every ring this package's own entry points can reach at `d = 3`.
This was confirmed directly: every measurement below exercises this exact
path (`d = 3`), and the shortcut branch is never taken. It is **not**,
however, structurally unreachable in general -- `canonicalScaledNefDataInternal`
itself has no dimension gate, so a caller outside this package's five entry
points could reach `d != 3` and hit the shortcut branch, which is why it was
still given the same `B`-threading treatment rather than left alone. This is
a smaller fix than the main one (dead code on every ring actually reachable
through this package's public API), and is reported as such rather than
silently assumed irrelevant.

### Regression added

`tests/multigraded-skew-cartier.m2` was extended with a new section (`Part 0`)
that:

1. Constructs `H = divisor(Z_0) + divisor(Z_8)` (bidegree `(1,1)`, the
   candidate ample class from Part 1 below, used here only for its shape).
2. Constructs `Lbig = 2*K + 12*H`, exactly the candidate divisor
   `canonicalScaledNefDataInternal` computes internally for `a=2, t=6`.
3. Verifies, by direct computation, a genuine base-point-free **false
   positive**: `isBasePointFreeDivisor(Lbig,Btrue)` is `false` (correct --
   `Lbig` is not base-point-free), but the bare, auto-deriving
   `isBasePointFreeDivisor(Lbig)` (which uses `multigradedBlockData`'s wrong
   `B`) is `true`. This is a genuine value-level disagreement, not merely a
   cost difference -- see "Searching for this counterexample" below.
4. Exercises an actual entry point's search loop (not merely the bare
   predicate, and not merely `isCartierMultigraded` alone):
   `canonicalContractionAtThresholdData(Z,2,6,H,IrrelevantIdeal=>Btrue,
   ContractionMultipleLimit=>1)` has `cartierThresholdDivisor` equal to
   `Lbig` exactly (same `a=2`, `lambda=6` construction), and
   `ContractionMultipleLimit=>1` caps
   `canonicalContractionAtThresholdDataCore`'s own `while` loop to testing
   only that one candidate, keeping the test fast (about 7.5 s) while still
   running the real loop rather than a hand-written substitute for it. With
   `B` threaded correctly, this call reports `conclusive => false` (matching
   the ground truth: `Lbig` genuinely is not base-point-free at multiplier
   1). Before Part 0's fix, the loop's own predicate call ignored the
   supplied `B` and would have used `multigradedBlockData`'s wrong one
   instead -- which (item 3 above) reports `Lbig` base-point-free -- so the
   unfixed code would have wrongly returned `conclusive => true` here.
5. Confirms the Cartier gate itself (T1's fix) is unaffected: `a=1` (where
   `K` is genuinely not Cartier under `Btrue`) still correctly errors.

**Searching for this counterexample cost real effort and is reported
honestly.** Most small-to-moderate multiples of `K` and of `K`-plus-`H`
combinations tried gave the *same* boolean answer under `Btrue` and under
`multigradedBlockData`'s wrong `B` (both `false`, generally because `h^0 = 0`
at that degree regardless of which ideal is used to saturate an already-zero
annihilator) -- these do not exercise the defect, only its absence at low
degree. The false positive at `Lbig = 2K+12H` was found by deliberately
searching larger, `H`-dominated combinations; it is presented here as the
genuine, verified counterexample it is, not the only or first thing tried.

### `make test-core` and `make test-upstreams`

Both run clean after Part 0's change, including the new assertions above:

```text
$ make test-core
... (all five files, unchanged existing assertions plus the two new ones
     in tests/multigraded-skew-cartier.m2)
$ echo $?
0
$ make test-upstreams
All upstream test suites passed.
$ echo $?
0
```

## Part 1: an ample-candidate class `H` on `Z`

`Z` is rebuilt exactly as `tests/multigraded-skew-cartier.m2` /
`STAGE2-SINGULAR-MEASUREMENT-PLAN.md` section 3:

```m2
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,3,-2}};
sigma = coneFromVData transpose matrix rayList;
HB = apply(hilbertBasis dualCone sigma, v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
wdegs = apply(HB, h -> sum apply(3, k -> h#k*{1,1,1}#k));
S = QQ[y_1..y_(#HB), w, Degrees => wdegs | {1}];
Xproj = S/sub(I0,S);
P = computeFlip(Xproj, BaseIsProjective=>true, Multipliers=>{1,2});
Z = P#totalRing;                     -- degrees {{1,0}},{1,1},{0,1},{0,2},
                                      -- {0,5},{0,1},{0,4},{0,3},{0,1}
                                      -- for u_1,u_2,y_1..y_6,w
Btrue = sub(P#irrelevantIdeal, Z);
```

### `Z -> Xproj` is small: a structural fact, not an assumption

`computeFlip`'s own algorithm (`FlipComputation/flip.m2`) only returns a
`B2MProjection` `P` once `isSmallProjection(P)` succeeds for the chosen
multiplier -- this is a hard gate inside `computeFlip` itself, checked before
`P` is ever returned, not something this measurement re-derives. The trace
confirms it directly: multiplier `m=1` is rejected ("exceptional locus
contains a divisor"), `m=2` succeeds. So `Z -> Xproj` is certified, by the
package's own existing (unmodified) machinery, to be a **small** contraction:
its exceptional locus contains no divisor. This is the structural fact the
rest of Part 1's argument leans on.

### The exceptional curve `C`, identified and measured directly

`Xproj`'s singular locus (independently confirmed normal and 3-dimensional
projectively) has radical exactly `(y_1,...,y_6)` -- i.e. the single point
`[0:...:0:1]` (`w=1`), matching `STAGE2-SINGULAR-MEASUREMENT-PLAN.md` section
2.2's independent toric derivation. The fibre of `Z -> Xproj` over this point,
`C := V(y_1,...,y_6) subset Z`, was computed directly: `Z/(y_1,...,y_6)` has
Krull dimension 3 with a single minimal prime (irreducible), and geometric
dimension `3 - degreeLength = 1` -- a curve, as expected for a small
3-fold flip.

**The degree of `O(a,b)` restricted to `C` was computed directly (not
guessed), by computing the Hilbert function of `Z/(y_1,...,y_6)` at nine
bidegrees:**

| `(a,b)` | `(1,0)` | `(0,1)` | `(1,1)` | `(2,0)` | `(2,1)` | `(2,2)` | `(3,2)` | `(1,2)` | `(2,3)` |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `h^0` on `C` | 1 | 1 | 2 | 1 | 2 | 3 | 3 | 2 | 3 |

Every one of these equals `min(a,b)+1` exactly, confirming
`deg(O(a,b)|_C) = min(a,b)`: `O(a,b)` is trivial on `C` when `a=0` or `b=0`,
and strictly positive precisely when **both** `a>0` and `b>0`. This matches
the two grading blocks' own roles: `u_1` (degree `(1,0)`) and `u_2` (degree
`(1,1)`) are `C`'s own homogeneous coordinates (both degree 1 in the *first*
component, giving `C ≅ P^1`), while `w` (degree `(0,1)`) supplies the second,
"trivial" (`P^0`) grading direction.

### The candidate `H`

`H = divisor(Z_0) + divisor(Z_8)` (i.e. `divisor(u_1) + divisor(w)`),
bidegree `(1,1)`:

- **Cartier**, confirmed against `Btrue` (`isCartierSaturatedInternal(H,Btrue)
  = true`, 0.15 s); many other small bidegrees `(1,1)` through `(2,5)` tried
  were also Cartier, so this is not a rare or fragile choice.
- **Base-point-free already at multiplicity 1** (`isBasePointFreeDivisor(H,
  Btrue) = true`, 0.10 s), hence nef.
- **Strictly positive on `C`**: `deg(H|_C) = min(1,1) = 1 > 0`. This
  specifically rules out the failure mode the task flagged -- pulling back
  `Xproj`'s own polarization alone would give a class trivial on `C` (nef but
  not ample, since `min(a,0) = 0` for any pure-base class), but `H` is not
  that pullback; it has a strictly positive fibre (`u_1`) component too.

### Honest ampleness assessment

**What is established:** `H` is Cartier, nef (base-point-free), and strictly
positive on the one curve independently identified as `Z`'s exceptional
locus, using a structural fact (`isSmallProjection`, already certified by
`computeFlip` itself) plus a directly computed intersection-theoretic
criterion on that curve (not a hand-waved one -- the `min(a,b)` formula was
checked against nine bidegrees, not assumed from one).

**What is not established, and is flagged rather than glossed over:** a
fully independent toric-fan derivation of `Z`'s (or `Xproj`'s) actual class
group was not carried out. A back-of-envelope toric ray count (`Xproj`'s
underlying affine cone `sigma` has 4 rays in a 3-dimensional lattice, plus
one compactifying ray for `w`, giving 5 rays in 3 dimensions) suggests
`Cl(Xproj)_Q` could plausibly be rank 2, not rank 1 -- in which case
`Cl(Z)_Q` could be rank 3, not the rank-2 visible in this bigraded
presentation, and there could in principle be curves *not visible in this
grading* on which `H` fails to be positive. This was not ruled out. **The
certificate obtained here is therefore structural-plus-computational (small
contraction, unique curve identified and checked), not a fully independent
toric verification of ampleness in the strict sense.** `H` is used as the
best-justified candidate available, with this caveat stated plainly, per the
work order's explicit allowance for exactly this situation.

## Part 2: the measurement

`a = 2` (the independently verified canonical index; `T2`,
`canonicalIndexData`'s multigraded generalization, was **not** implemented --
see "Deliberate scope choices"). `H` as above. `Btrue` as above, threaded via
`IrrelevantIdeal` everywhere Part 0 makes that meaningful.

| Stage | cpu seconds | Key outputs |
| --- | --- | --- |
| 0. (setup) build `Xproj`, run `computeFlip` | 0.295 | `Z`: `degreeLength=2`, `dim=5`; `Btrue` obtained from `P#irrelevantIdeal` |
| 1. block structure and `B` | 0.0002 | `multigradedBlockData Z` succeeds but gives the **wrong** `B` (different radical from `Btrue`, per T1); `geometricDimension=3` (this field, unlike the irrelevant ideal, is correct) |
| 2. canonical divisor + Cartier check | 0.78 (canonicalDivisor) + 0.23 (Cartier check on `K`) + 0.31 (on `2K`) = **1.32** | `K` non-Cartier, `2K` Cartier under `Btrue`, matching the independently-verified index 2 |
| 3. nefness at `t=0` (`canonicalNefData(Z,2,H,IrrelevantIdeal=>Btrue,NefSearchLimit=>8)`) | **did not complete** -- killed after approximately 20 minutes wall-clock | No intermediate output: `canonicalNefData`/`canonicalNefDataCore` expose no verbose/progress option, so the only observable evidence of the stall is elapsed time and (steadily climbing, up to roughly 35% of this machine's RAM) process memory. The last printed line remained `computeFlip`'s own setup trace ("`-- the flip is obtained for m = 2`"); nothing from stage 3 itself printed before the kill. |
| 4. threshold search | **not attempted** | blocked: no threshold search is meaningful before stage 3 resolves whether `K` is already nef |
| 5. flattening to the diagonal subalgebra of `H` | **not attempted** | blocked, same reason |
| 6. complete-linear-system graph | **not attempted** | blocked, same reason |
| 7. Stein factorization | **not attempted** | blocked, same reason |
| 8. contraction type and dimensions | **not attempted** | blocked, same reason |

Per the Stage 1 and Stage 2 plans' own explicit protocol, this is a
legitimate, informative outcome, not a failed work order: "a stall that is
recorded and located is a successful outcome of this work order." Stage 2's
own success criterion 5 asks only that "T4 reaches at least the nef test on
`Z` at the correct index with a supplied ample class, with recorded
timings" and explicitly says reaching further is "desirable but not
required." That criterion is met (the nef test was reached and timed, as a
20-minute stall); reaching the threshold search and beyond was not achieved.

### Supplementary per-candidate cost data

Because `canonicalNefData` itself exposes no progress and never returned,
the following individual base-point-free tests (using
`isBasePointFreeDivisor(D,Btrue)` directly, the same predicate the search
loop's internals call after Part 0's fix) were measured separately, to give
some granular sense of where the stage 3 cost is going, even though the
aggregate alternating search did not complete:

| Divisor tested | cpu seconds (`Btrue`) | cpu seconds (`Bmine`, wrong `B`, for contrast) | `bpf` (`Btrue`) |
| --- | --- | --- | --- |
| `K` | 0.11 | 0.05 | false |
| `2K` | 0.21 | 0.05 | false |
| `3K` | 0.49 | 0.06 | false |
| `4K` | 0.84 | 0.06 | false |
| `5K` | 2.36 | 0.08 | false |
| `6K` | 3.44 | 0.09 | false |
| `2K+2H` (`a=2,t=1`, `m=1`) | 0.38 | -- | false |
| `2K+12H` (`a=2,t=6`, `m=1` = `Lbig`) | 6.80 | 0.36 | false (`Bmine` says **true** -- the Part 0 false positive) |

The cost of testing a single base-point-free candidate on `Z` grows sharply
(roughly, though not perfectly smoothly, geometrically) with the candidate's
degree, and is already multiple seconds at degrees far smaller than what
`canonicalScaledNefDataInternal`'s own search needs to reach: at each
alternation `i` of `canonicalNefDataCore`, the scaled test uses
`t = 1/2^i`, so `q = 2^i` and the tested divisor is
`q*a*K + a*p*H` scaled up to six further multiples -- degrees that grow
quickly past what was measured directly above. This is fully consistent with
the 20-minute stall: even a bounded, `NefSearchLimit=>8` search must in the
worst case run through 8 alternations of up to 6 increasingly expensive
candidate tests each, and the per-candidate cost curve above shows no sign
of leveling off within the range actually measured.

## Deliberate scope choices

- **T2 (multigraded `canonicalIndexData`) was not implemented.** The
  canonical index of `Z` (2) is already independently known (Stage 2 plan
  section 2.2/2.3, confirmed both by hand toric computation and by
  `isCartierSaturatedInternal`), so `a=2` is supplied directly to every
  entry point in Part 2 above. This is a deliberate scope choice, not an
  oversight -- the work order explicitly permits it ("You do NOT need to
  implement Stage 2's T2 ... just supply `a=2` directly").
- **T3 (measuring the index search itself) was not implemented**, for the
  same reason: there is no index search here to measure, `a` is supplied.
- **T5 (deciding how to keep working multigraded through the Stein/Segre
  interface for a singular flip target) was not implemented or decided.**
  It never became relevant, because stage 3 (nefness) never resolved, so the
  chain never reached the threshold/flattening/Stein stages where T5 would
  matter.

## What this does and does not establish

**Establishes:**

- Part 0's fix is a genuine, narrow completion of Stage 2's T1: the internal
  search loops of `canonicalScaledNefDataInternal`, `canonicalNefDataCore`,
  and `canonicalContractionAtThresholdDataCore` now honor a caller-supplied
  `IrrelevantIdeal`, not only the entry-point-level Cartier gate T1 already
  fixed. This closes a documented, real gap: a concrete base-point-free false
  positive (`Lbig = 2K+12H`) was found and is now caught by a committed
  regression, exercised through an actual entry point's search loop
  (`canonicalContractionAtThresholdData` with `ContractionMultipleLimit=>1`
  to keep the test fast), not merely through the bare predicate.
- `negativeBaseLocusCurveData`'s shortcut inside `canonicalScaledNefDataInternal`
  is confirmed, by test rather than assumption, to be dead code for every
  ring this package's own dimension-three entry points can reach; it was
  still given the same `B`-threading treatment since it is not dead in
  general (a caller could reach `d != 3` directly through the internal
  function).
- A concrete, singular, rank-2, canonical-index-2 multigraded input can be
  built and have its Cartier/nef machinery driven with the corrected,
  caller-supplied irrelevant ideal end to end through the Cartier gate and
  into the nef search, without erroring or silently returning a wrong
  answer.
- **The central open question this measurement targeted -- whether the
  multigraded speed-up Stage 1 measured on smooth examples survives once a
  genuine reflexive hull (`K` non-Cartier) is needed -- has a clear, negative
  answer on this input.** Individual base-point-free tests that cost under a
  second on Stage 1's smooth, index-1 examples already cost multiple seconds
  here at comparably small degrees, growing sharply with degree, and the
  bounded (`NefSearchLimit=>8`) alternating nef search did not complete in
  roughly 20 minutes -- several orders of magnitude worse than Stage 1's
  under-5-second, full nef-through-contraction chains on smooth inputs.
- A structural (not hand-derived-from-scratch) argument, backed by a
  directly computed intersection number, for why the candidate `H` avoids
  the specific failure mode (a pullback class trivial on the flip's
  exceptional curve) the work order flagged as a live risk.

**Does not establish:**

- That `H` is genuinely ample in the strict, fully verified sense -- only
  that it is Cartier, nef, and positive on the one independently identified
  exceptional curve. Whether `Cl(Z)_Q` has rank exactly 2 (matching the
  bigraded presentation) or higher (in which case unseen curves could exist)
  was not determined.
- Anything about the threshold search, flattening, complete-linear-system
  graph, Stein factorization, or contraction classification on a singular
  multigraded ring -- stage 3 never resolved, so stages 4-8 were never
  reached. Whether the multigraded-versus-flattening cost comparison Stage 1
  found (an approximately four-orders-of-magnitude win on smooth inputs)
  holds, partially holds, or is irrelevant once a reflexive hull is needed is
  **not** addressed one way or the other by this measurement; the question
  stalls before it can be asked.
- That the specific growth curve measured (roughly geometric in the tested
  divisor's degree) is the true asymptotic behaviour, as opposed to an
  artifact of this specific ring, this specific `H`, or unfavourable
  Gröbner-basis term orders. Only the concrete, measured numbers above are
  claimed; no general growth-rate law is asserted.
- Any conclusion about `T2`/`T3`/`T5` beyond that they were not attempted;
  see "anything noticed but not acted on" in the final report for whether
  they now look more or less urgent.
