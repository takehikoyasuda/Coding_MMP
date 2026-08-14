# Stein Factorization Cost on a Genuine Divisorial Multigraded Contraction: Experimental Report

**Status**: Bottleneck located and root-caused to `res(nn,LengthLimit=>d1+d2+1)`; a practical workaround (guessed truncation bound `r=1`) found; and, for this birational input, **fully proved correct** (not merely circumstantially verified) via `g` finite and `g∘h=f` holding automatically at any bound plus a direct `isNormal` computation combined with Zariski's Main Theorem. A closing theorem further shows this reduces to an *if-and-only-if*: given the source normal and `f` birational, `h_*O_Y=O_Z` holds exactly when the candidate `Z_r` is normal -- not a sufficient condition among others, the necessary and sufficient one. A follow-up attempt to bypass the bottleneck entirely via BGG/relative-Beilinson-monad methods (`TateOnProducts`'s `directImageComplex`) was tried and, on this input, was not faster -- a negative result, recorded below, not a refutation of the general technique. **Capstone**: the whole workaround was then plugged into the top-level driver, completing a genuine two-step smooth MMP, `Bl_p(P3) -> P3 -> point`, end to end from the pure bigraded input with no manually supplied graph -- see "Capstone" below.
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

**A practical workaround was then found and confirmed** (see "A practical
workaround" below): the package already ships `steinHomDataAtBound` (skip
the resolution, truncate at a caller-supplied bound) and
`steinDataByStabilization` (guess-and-increase with a self-consistency
check), and an existing test (`blowup-twisted-cubic.m2`) already validates
a guessed bound against independently known geometry rather than an internal
certificate. Repeating that pattern here: guessed bounds `r=1` (1.45s) and
`r=2` (8.89s) both reproduce the correct, independently verified answer
(`dim=4, H(1)=10, H(2)=35`, matching the known target `P3` embedded by
`O(2)`) -- turning an unresolved 30+ minute stall into a 1.45-second
computation, on this input.

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

## A practical workaround: guessed bound + independent geometric verification

`SteinFactorization.m2` already ships an escape hatch from the expensive
certified-bound path, in two flavors:

- `steinHomDataAtBound(ambient,igraph,bound)` -- skip the resolution
  entirely and truncate at a caller-supplied `bound`. `"certifiedBound"` is
  `false`: nothing establishes the supplied bound was large enough.
- `steinDataByStabilization(...)` -- automate a guess-and-increase loop:
  try `startBound, startBound+(1,0), startBound+(2,0), ...`, compare a
  "fingerprint" (Krull dimension, Hilbert function values, module degrees)
  across consecutive bounds, and stop once `requiredMatches` consecutive
  bounds agree. Documented explicitly as heuristic evidence, not proof
  (`"finite stabilization is not a proof of the Corollary 4.3 bound"`).

`third_party/SteinFactorizationM2/tests/blowup-twisted-cubic.m2` already
uses exactly this pattern on a harder case than Stage 1 ever measured (a
blow-up of a twisted cubic in `P3`, composed with a squaring map, where "the
full minimal resolution is the bottleneck... >2 minutes"): it supplies
`r=(2,0)` directly to `steinHomDataAtBound`, then validates the result
against **independently known geometry** (the expected target's Krull
dimension and Hilbert function), rather than trusting an internal
certificate.

This experiment repeated that exact pattern on the input that stalled above.
The expected target is independently known here too: the contraction is the
blow-down `E -> point` (`Bl_p(P3) -> P3`), and `morphismDivisor L` is
numerically the pullback of `O_{P3}(2)` (its 10 sections match
`h^0(O_{P3}(2))=10` exactly, confirmed earlier in this report). So the
expected Stein-factorization target ring is the degree-2 Veronese
subalgebra of `P3`'s coordinate ring: Krull dimension 4, Hilbert function
`h^0(O_{P3}(2k)) = binomial(2k+3,3)`, i.e. `H(1)=10, H(2)=35`.

```m2
hd = steinHomDataAtBound(productRing,graphIdeal,{r,0});
cd = steinCoordinateAlgebra(hd,0);
dim(cd#"ring"); hilbertFunction(1,cd#"ring"); hilbertFunction(2,cd#"ring");
```

| Guessed bound `{r,0}` | cpu time | `dim` | `H(1)` | `H(2)` | Matches expected geometry? |
| --- | --- | --- | --- | --- | --- |
| `r=1` | **1.45s** | 4 | 10 | 35 | **yes** |
| `r=2` | 8.89s | 4 | 10 | 35 | **yes** (same answer -- one stabilizing match) |

Both guessed bounds -- vastly smaller than the certified `28` that made the
resolution itself unresolvable at homological degree `4` -- reproduce the
correct, independently verified answer. `r=1` alone resolves the entire
Stein-factorization step in 1.45 seconds, versus 30+ minutes unresolved via
the certified path: a practical fix for this specific input, using machinery
that already existed in the package before this experiment. A follow-up
theoretical check (below, "the map `g` is automatically finite") shows that
half of the Stein-factorization definition -- `g` finite -- holds
unconditionally at *any* bound, certified or not, so the entire remaining
risk in this workaround is concentrated in the other half, `h_*O_Y=O_Z`.

**Caveat, stated plainly**: this verification was only possible because the
expected target geometry (`P3`, Veronese-embedded) was known independently
in advance. For a genuinely unknown contraction, one would fall back to
`steinDataByStabilization`'s weaker self-consistency check (does the answer
stop changing as the bound increases?), which its own documentation
correctly calls evidence, not proof. What this experiment adds beyond that
existing caveat is a second, positive data point: on a real instance where
the certified path is provably infeasible (not merely slow), a small guessed
bound both stabilizes *and* matches ground truth, on the first two bounds
tried. See the next section for a sharper account of exactly what part of
this remains unverified for a guessed bound, and what part does not need
verifying at all.

---

## Theoretical note: the map `g` is automatically finite at any bound; all the risk is in `h`

The Stein factorization of `f: Y -> X` is `Y --h--> Z --g--> X` with
`Z = Spec_X(f_*O_Y)`, `g` finite, and `h` proper with `h_*O_Y = O_Z` (hence
geometrically connected fibres) -- see
[SteinFactorization.m2:563-568](../third_party/SteinFactorizationM2/SteinFactorization.m2#L563-L568)
and `references/AlgoMMP/AlgoMMP.tex`'s Section 5 ("Stein factorization"). A
natural worry about the guessed-bound workaround above is that it only
checked numerical invariants of the candidate ring `C_r`, not either half of
this definition directly. Working through the paper's own Lemma `lem:iota`
(`AlgoMMP.tex:2197`, called Lemma 4.5 by line-order) resolves half of that
worry completely, in general -- not just for this example.

Lemma `lem:iota` proves that the map
`iota: Hom_R(R_{>=r}, R)_{0,>=0} -> R_gamma, psi |-> psi(gamma)/gamma`
(for any nonzero bihomogeneous `gamma in R_{>=r}`) is an **injective**,
degree-preserving ring homomorphism. Crucially, its proof uses only that `R`
is a domain and `gamma` is nonzero -- **it never invokes Corollary 4.3's
bound**. Consequently, for `r_1 <= r_2` (componentwise) sharing a common
`gamma` of high enough degree, the two candidate rings `C_{r_1}` and
`C_{r_2}` embed compatibly into the *same* localization `R_gamma`, with
`C_{r_1} subseteq C_{r_2}`: guessed-bound candidates form a genuine
increasing chain of subrings of `R_gamma`, converging to (and, once `r`
passes the Corollary 4.3 threshold, exactly equal to) the true
`C_infty = direct sum_v H^0(X,(f_*O_Y)(v))`.

`C_infty` is finite over `A` (the target's own homogeneous coordinate ring)
unconditionally -- this is the classical Stein factorization theorem for a
proper morphism (Hartshorne III.11.5, cited at `AlgoMMP.tex:2121`), a
property of `f` alone that does not depend on which `r` one uses to compute
it. Since `A` is Noetherian, **every submodule of a finite `A`-module is
itself finite over `A`** -- and every guessed-bound `C_r` (certified or not,
correct or too small) is, by the previous paragraph, literally a submodule
of `C_infty`. So:

> **`g: Proj(C_r) -> X` is finite for *every* bound `r`, always -- this is
> not something that needs checking, and checking it would carry no
> information about whether `r` was large enough.**

This retracts a suggestion made earlier in this investigation (checking `g`'s
finiteness via `isModuleFinite` on an explicitly constructed `A -> C` map)
as a worthwhile verification step: it is not, because the answer is always
"yes," unconditionally.

What this does **not** resolve (as first written): whether `C_r` actually
*equals* `C_infty`, i.e. whether `h_*O_Y = O_Z` for `Z = Proj(C_r)` --
equivalently, whether the guessed bound had already stabilized rather than
capturing only a proper subring. If `r` is too small, `C_r subsetneq
C_infty` gives a genuinely *coarser* intermediate `Z_r`, with `Y -> Z -> Z_r`
factoring through the true Stein target `Z`; the computed `h_r: Y -> Z_r`
then has fibres that are unions of the true `h`'s fibres, and nothing here
rules out those unions being disconnected. The next two sections resolve
this remaining question completely for a birational `f` (our case), first
by showing a second half of the definition is *also* automatic, then by
proving the one remaining condition is checkable directly and is, in fact,
both necessary and sufficient.

## `g∘h=f` is also automatic at any bound, for the same reason

The same mechanism that makes `g` finite for free also makes the
factorization identity `g∘h=f` hold identically, at any bound -- not merely
approximately, and not only after the bound is large enough.
`AlgoMMP.tex:2328-2340`'s diagram builds `h`'s comorphism via the *same* map
`iota` that builds `g`'s: for `alpha` a homogeneous generator of `A`,
`phi(alpha)` is (by construction) the "multiplication by `alpha`"
endomorphism of `R_{>=r}`, so `iota(phi(alpha)) = alpha(gamma)/gamma = bar
alpha` -- literally the image of `alpha` in `R_gamma` under the ordinary
inclusion `A -> R -> R_gamma` used to define `f` itself. Composing,
`(g∘h)^#(alpha) = h^#(phi(alpha)) = iota(phi(alpha)) = bar alpha =
f^#(alpha)`, an identity of elements of the fixed ring `R_gamma`, true for
*any* `r` for which `C_r` and `phi` are defined at all (the argument never
mentions Corollary 4.3's bound).

The paper's own drafting notes are candid that this buys less than it might
seem: the commented-out proof (`AlgoMMP.tex:2358-2422`) and the following
revision note (`AlgoMMP.tex:2460-2471`) state plainly that showing "the
arrow to `Z` is `iota`" is "**not quite free**" as a *characterization* of
the Stein factorization -- defining `Z` this way "would make it a
definition, at the price of owing a proof that this `Z` is the Stein
factorization: the work moves, it does not go away." In other words: `g∘h=f`
holding is a tautological consequence of how `phi` and `iota` are built from
the *same* ambient localization, true even for a `Z_r` that is only a coarse
sub-approximation of the true `Z` (in the degenerate extreme, `Z_r=X` with
`h=f`, `g=id` also satisfies it trivially). It says nothing about whether
`Z_r` is *the* Stein intermediate. This means the sibling package's own
regression checks that assert `g∘h=f` by substitution
(`third_party/SteinFactorizationM2/tests/basic.m2:166-168`) are, on their
own, tests that the *implementation has no bugs*, not tests that the
computed `Z` is mathematically the Stein factorization -- for those small
examples, that latter fact is established independently (by the same kind
of by-hand computation Stage 1 and this report lean on), not by the
substitution check.

So, combining both retractions: neither `g` finite nor `g∘h=f` carries any
information about whether a guessed bound was large enough. **All of the
content is in `h_*O_Y=O_Z` alone**, exactly as claimed above, now on firmer
footing.

## A complete proof for this input, and a necessary-and-sufficient criterion in general

For a *birational* `f` (our case: the blow-down `E->point` composed with a
projectively-normal Veronese embedding is birational, generic fibre a
single reduced point), the remaining question has a classical answer.
Zariski's Main Theorem (Hartshorne III.11.3-11.4): if `h: Y -> Z` is a
birational proper morphism of Noetherian integral schemes and `Z` is
**normal**, then `h_*O_Y=O_Z` (hence every fibre of `h` is connected).
Since `f=g_r∘h_r` is birational, `deg(g_r)*deg(h_r)=1` forces `h_r` itself
birational too, for *every* candidate `r` (not only the certified one) --
so ZMT applies to `h_r` the moment `Z_r` is known normal.

**This was checked directly, not assumed**, on the `r=1` candidate ring
`C_1` from the workaround above:

```m2
hd = steinHomDataAtBound(productRing,graphIdeal,{1,0});
cd = steinCoordinateAlgebra(hd,0);
isNormal(cd#"ring")
```

| Computation | cpu time | Result |
| --- | --- | --- |
| build `C_1` | 1.42s | `dim=4`, 10 ambient variables (as before) |
| `isNormal(C_1)` | **294.2s** (~4.9 min) | **`true`** |

`isNormal(C_1)=true`, combined with `f` birational, gives -- by ZMT, not by
numerical coincidence -- `h_{1,*}O_Y=O_{Z_1}`. Together with `g_1` finite
and `g_1∘h_1=f` (both automatic, previous section), **`r=1` is proved to be
the actual Stein factorization of this contraction**, not merely a Hilbert-
function match to the expected answer. Cost-wise, 294s for the normality
check is far more than the 1.45s Hilbert-function spot-check, but still
dramatically cheaper than the certified path (unresolved after 34+ minutes
at homological degree 4 of the 28 needed).

**A sharper, if-and-only-if version of the criterion.** Prompted by the
question of whether checking `Z_r` normal is really necessary, or whether a
cheaper direct check of `h_*O_Y=O_Z` exists: it is not just sufficient, it
is *equivalent*, given the source `Y` normal and `f` birational. Since `Y`
is normal and irreducible and `h_r: Y -> Z_r` is dominant, the universal
property of normalization (e.g. Stacks Project, tag 035Q) forces `h_r` to
factor as `Y --(h~_r)--> Z~_r --nu--> Z_r`, where `Z~_r` is the
normalization of `Z_r`. Degrees multiply along both factorizations
(`deg(f)=deg(g_r)deg(h_r)=1` and `deg(h_r)=deg(nu)deg(h~_r)`, with
`deg(nu)=1` since normalization is birational), so `h~_r` is *also*
birational, onto the genuinely normal `Z~_r` -- so ZMT applies unconditionally
to `h~_r`, giving `h~_{r,*}O_Y = O_{Z~_r}` regardless of whether `r` was
large enough. Then

```text
h_{r,*}O_Y = nu_*(h~_{r,*}O_Y) = nu_*O_{Z~_r}
```

and `h_{r,*}O_Y = O_{Z_r}` holds **if and only if** `nu_*O_{Z~_r}=O_{Z_r}`,
i.e. **if and only if `nu` is an isomorphism, i.e. `Z_r` is already
normal.** So, under these hypotheses (source normal, `f` birational --
exactly our setting, and the typical setting for a divisorial MMP
contraction), checking `Z_r`'s normality is not an over-cautious sufficient
condition standing in for something cheaper: **it is exactly, precisely,
the content of `h_*O_Y=O_Z`, no more and no less.** The only room left for a
cheaper computation is algorithmic -- finding a faster way to test
normality of this *specific* ring (e.g. via `integralClosure` directly, or
by exploiting that `Y`'s known normality means only `Y`'s finitely many
exceptional/boundary divisors need checking for extra sections, via Serre's
S2 criterion's codimension-2 Hartogs extension) -- not a different,
logically weaker condition to substitute in its place.

### The general (not necessarily birational) case: normality plus one fibre at an étale point of `g`

The equivalence above used birationality of `f` essentially once: to force
`deg(h_r)=1`, so `h~_r` (onto the normalization) is automatically
birational and ZMT applies to it for free. For a genuinely non-birational
candidate (`deg(g_r)>1`, e.g. a Mori-fibre-space-type contraction), that
step needs a replacement, and the replacement is exactly what's needed to
extend the criterion correctly:

The general (non-birational) Zariski connectedness theorem needs `Z~_r`
normal **and** `h~_r`'s *generic* fibre connected (not automatic once
`deg>1`) to conclude `h~_{r,*}O_Y=O_{Z~_r}`. Checking the generic fibre
directly sounds abstract, but the number of connected components of a
fibre is upper semicontinuous under specialization, so it suffices to
exhibit **any single point** whose fibre is connected -- the generic fibre
then has *at most* as many components, hence is also connected. The right
single point to pick is one where `g_r` is **étale**: away from `g_r`'s
(codimension >= 1, hence non-dense) ramification locus, this is a dense
open condition in characteristic 0 (generic smoothness), and checking there
specifically avoids conflating `g_r`'s own ramification behaviour with
`h_r`'s genuine fibre structure -- at an étale point `z` (over `x=g_r(z)`),
`f^{-1}(x)` decomposes as a disjoint union of `deg(g_r)` fibres of `h_r`,
each one an unclouded read of `h_r`'s typical behaviour, unlike at a
ramification point where `g_r`'s own identifications could make a fibre
look more (or differently) connected for reasons having nothing to do with
`h_r`.

So, in general:

```text
h_{r,*}O_Y = O_{Z_r}  <=>  Z_r is normal  AND  h_r^{-1}(z) is connected
                            for some z where g_r is etale
```

recovering the birational special case above exactly (there, `deg(h_r)=1`
forces every fibre, in particular one at an étale point, to be a single
reduced point -- trivially connected -- so only the normality half remains
to check). Computationally this second condition is itself a small, local
check: find a point where `g_r`'s ramification locus (e.g. the vanishing of
an appropriate discriminant/Jacobian rank drop) does not vanish, restrict
`Z_r`'s defining data to the corresponding fibre of `h_r`, and test
connectedness (or the stronger, often easier `isPrime`, for irreducibility)
of that fibre's ideal -- not attempted on any example in this report, but a
natural next experiment for a genuinely non-birational guessed-bound
candidate (e.g. this project's own Segre `P1xP2 -> P1` fibration, whose
`Z=X` triviality was established in the next section by a *different*
route -- already-normal target and already-connected generic fibre -- not
by this per-candidate criterion).

---

## A broader observation: none of the examples measured so far exercise a genuinely nontrivial `Z != X`

Both Stage 1's Segre `P1xP2 -> P1` and this report's `Bl_p(P3) -> P3` share
a feature not previously remarked on: **in both cases the target is already
normal (`P1` and `P3` are smooth) and `f`'s generic fibre is already
connected/irreducible** (a single point for the birational `Bl_p(P3)` case;
the irreducible `P2` fibre for the Segre projection). By the general
(non-birational) form of Zariski's connectedness theorem -- proper `f` with
normal target and connected generic fibre implies *every* fibre is
connected -- **both of these Stein factorizations are trivial: `Z=X`
exactly, `C=A` exactly**, matching this report's own data (`C_1`'s 10
generators and dimension 4 exactly match `A`'s own 10 generators and
dimension 4; no genuinely new generator was ever needed).

This means every Stein factorization exercised by this project's measured
examples so far -- including the one that stalled for 30+ minutes -- was,
with hindsight, computing something whose answer ("no Stein contraction
needed, `Z=X`") could have been obtained *for free* by a cheap upfront
check (is the candidate target already normal, and is a general fibre of
`f` already connected/irreducible?), skipping `steinHomData` and the entire
workaround apparatus. This upfront check is plausibly cheap: normality of
a *given, explicit, low-generator* target ring (rather than the large
`C_r` candidate ring) and fibre-irreducibility at one point are each much
smaller computations than either the certified resolution or even the
`isNormal(C_1)` call above (which normalizes the *bigger*, freshly built
candidate ring, not the small pre-existing target ring). Whether this
observation generalizes -- i.e. whether MMP extremal contractions
*typically* land on already-normal targets with already-connected fibres,
making a full Stein factorization computation avoidable in the common case
-- was not tested beyond these two examples, but the Mori-theoretic
construction of extremal contractions (via `Proj` of a section ring) is
suggestive that this is the common, not the exceptional, case. Flagged here
as a promising, not-yet-implemented, engineering direction: **an upfront
"already normal + already connected" fast-path check before ever invoking
`steinHomData`.**

---

## A negative result: BGG / relative Beilinson monad (Eisenbud-Schreyer) tried, not faster here

Two references sit in `references/AlgoMMP/AlgoMMP.bib` but are **not
currently cited** anywhere in `AlgoMMP.tex`: `eisenbud2008relative`
(Eisenbud-Schreyer, "Relative Beilinson monad and direct image for
families of coherent sheaves") and `kim2025onalgorithms` (Kim, "On
algorithms computing sheaf cohomology groups", which surveys the same
territory including higher direct images under a morphism). Both describe
computing `Rf_*` via the BGG correspondence and exterior algebras --
"generally more efficient" than free-resolution-based methods, per the
Eisenbud-Schreyer abstract -- which is exactly the class of computation
`steinHomData` needs and exactly the class of cost (`res(nn,
LengthLimit=>d1+d2+1)`) that stalled it. Prompted by this recollection, the
approach was tried directly on this report's stalled input.

Macaulay2 ships an implementation: the `TateOnProducts` package's
`directImageComplex(Module,List)`, which computes `Rf_*` for a module on a
product of projective spaces along a projection, via `tateResolution`
(a BGG/exterior-algebra computation) rather than a symmetric-algebra free
resolution. This lines up with the problem shape exactly: `graphData`'s
`productRing` (29 variables, bidegree `(1,0)`/`(0,1)`, matching
`P^18 x P^9`) and `graphIdeal` (265 generators) map directly onto
`TateOnProducts`'s own `productOfProjectiveSpaces({18,9})` convention
(same variable ordering and bidegrees, confirmed from the package source),
letting the existing `graphData` be reused without reconstruction:

```m2
(S,E) = productOfProjectiveSpaces({18,9}, CoefficientField=>QQ);
rho = map(S, oldProdRing, gens S);
Mgraph = coker gens (rho oldGraphIdeal);
RfM = directImageComplex(Mgraph,{1});   -- project onto the target P^9 factor
```

**Result: did not complete.** Killed after 3+ minutes elapsed (3:32 cpu
time), memory climbing to 8.5GB and still growing -- a worse trajectory
than the certified path's early behaviour, and already well past the
294.2s the `isNormal`+ZMT route needed for a complete, proof-backed answer.
Ring construction and building `Mgraph` were both trivial (under 3ms); the
entire cost was inside `directImageComplex`'s own `tateResolution` call.

**A plausible explanation, not fully confirmed**: `tateResolution`'s cost is
governed by the *exterior* algebra's own size, which grows **exponentially
in each factor's projective dimension** (an exterior algebra on `n0+1=19`
variables has total dimension `2^19` across its exterior powers) --
`Beilinson`-window and related matrix operations must in principle handle
objects at that scale for the source-side (`n0=18`) factor. This is a
*different* combinatorial explosion than the symmetric-algebra resolution
length (`d1+d2+1` scaling with total variable count), not necessarily a
smaller one: on this specific input (`n0=18`, sizeably asymmetric against
`n1=9`), it does not obviously win. **This is not evidence that BGG/Tate
methods are generally inferior** -- the package's own documentation reports
comfortable timings (12-55s) on its own worked examples, which may simply
be smaller or more favorably shaped (lower dimension per factor, or more
symmetric) than this report's `P^18 x P^9` case. Whether a more favorable
`w` (giving smaller `n0,n1`), a finite-field coefficient ring (mirroring
[[gfp-reduction-benchmark-positive]]'s ~2.3x win elsewhere in this project),
or a different entry point in `TateOnProducts` (e.g. working with a
`directImageComplex(Ideal,Module,Matrix)` call against the smaller
19-variable flattened presentation from `diagonalSubalgebraData`, rather
than the full 29-variable graph) would change this outcome was not tested.

**Practical conclusion for this input**: `isNormal(C_1)` + Zariski's Main
Theorem (294.2s, proof-backed) remains the best available verified route,
not the BGG/Tate alternative, at least as tried here.

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
target), not because the underlying construction is generically cheap. The
certified-bound path (`steinHomData` proper) is genuinely infeasible on this
input; but, as the next section shows, the package's own existing
guessed-bound escape hatch turns this from a hard stop into a fast,
independently-checkable computation on this input.

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
- That the guessed-bound workaround generalizes beyond this one input in the
  same *proof-backed* way. The `r=1` answer here is now **proved** correct
  (via `isNormal` + ZMT, not merely numerically matched), but that proof
  leaned on `f` being birational, a property of this specific contraction
  (blow-down composed with a projectively normal embedding); a genuinely
  non-birational guessed-bound candidate (e.g. a fibration-type contraction
  with `deg(g)>1`) would need the more general (non-birational) Zariski
  connectedness theorem instead, still requiring `Z_r` normal but no longer
  getting `h_r` birational for free, and this was not tested on such a case.
- Whether the guessed-bound path's cost also grows sharply with `r` the way
  the certified path's resolution length did (`r=2`'s Hilbert-function check
  already cost 6x `r=1`'s); `r=3` and above were not measured for the
  Hilbert-function check, and `isNormal` was only run at `r=1`, so whether
  either check's cost grows badly with `r` on a harder input is unknown.
- Whether the "already normal + already connected" fast-path (see the
  broader-observation section above) actually holds for MMP extremal
  contractions in general, beyond this project's two measured examples, or
  whether it is cheap enough in practice to be worth checking upfront on a
  target ring before ever attempting a Stein factorization. Not tested.

---

## Capstone: a complete two-step MMP, `Bl_p(P3) -> P3 -> point`

Everything above was building toward one end: does the guessed-bound
workaround actually let the top-level driver complete a nontrivial
multi-step smooth MMP from a pure multigraded input, with no manually
supplied graph -- the original motivation for choosing this example back in
the "Setup" section. It does. Using `steinHomDataAtBound(...,{1,0})` for
Stein factorization (the proven `r=1` bound) and `directSteinGraph` to build
the actual contraction, then feeding the result through
`mmpStepRecordData` and `threefoldMMPData` exactly as
`tests/contraction.m2`'s existing `Bl_L(P3)` pattern does:

```m2
hd = steinHomDataAtBound(graphData#"productRing",graphData#"graphIdeal",{1,0});
cd = steinCoordinateAlgebra(hd,0);
rawGraph = directSteinGraph(hd,cd);
contractionGraph = mmpGraphMorphism new HashTable from join(pairs rawGraph,
    {"sourceRing"=>graphData#"sourceRing", "targetRing"=>cd#"ring"});
divisorialContraction = new HashTable from join({
    "conclusive"=>true, "contractionGraph"=>contractionGraph,
    "steinAlgebraData"=>new HashTable from {"ring"=>cd#"ring"}
    }, pairs contractionTypeData(3, dim(cd#"ring")-1));
divisorialModel = relativeCanonicalModelData divisorialContraction;
divisorialStep = mmpStepRecordData(divisorialContraction,divisorialModel);
birationalMMP = threefoldMMPData(cd#"ring",1,{divisorialStep});
```

| Stage | cpu time | Result |
| --- | --- | --- |
| complete-linear-system graph | 0.56s | (as before) |
| Stein algebra at `r=1` | 1.46s | (as before) |
| `directSteinGraph` + `mmpGraphMorphism` | 2.12s | builds the actual contraction graph |
| `contractionTypeData` | negligible | `isBirational=true`, source/target dimension both 3 |
| `relativeCanonicalModelData` | 0.007s | `isIdentity=true` -- `P3`'s canonical algebra is already trivial, as expected |
| `mmpStepRecordData`'s `contractionSmallnessData` | **~13-14 min cpu** | `contractionIsSmall=false` -- the exceptional divisor `E` is genuinely codimension 1, confirming a real divisorial contraction |
| `threefoldMMPData(cd#"ring",1,{divisorialStep})` | 5.14s | `conclusive=true`, `terminationType="Mori fibre space"`, `numberOfSteps=2` |

**Result**: `step 0 = divisorial`, `step 1 = fibration` -- exactly the
expected geometry (`Bl_p(P3)`'s blow-down of `E` to `P3`, then `P3`'s own
Mori-fibre-space contraction to a point), obtained fully automatically from
the bigraded starting ring, no hand-built graph anywhere in the chain.

This is a new, previously unmeasured cost: `contractionSmallnessData` (the
exterior-power-of-relative-differentials support computation that
`mmpStepRecordData` runs to classify the step) took far longer than the
`isNormal` check that preceded it in this investigation (~13-14 minutes cpu
vs. 294s) -- but, crucially, it **completed**, with memory flat throughout
(no runaway growth), unlike the original certified-bound `steinHomData`
path that never reached this stage at all after 30+ minutes. Total wall
time for the whole two-step MMP, dominated by this one step, was on the
order of 13-14 minutes -- slow for an interactive session, but a
categorically different outcome from "does not complete."

**Significance**: this closes the loop on the original goal that opened
this whole line of investigation (see `docs/BOTTLENECKS-AND-MULTIGRADING.md`'s
"Examples that expose the next bottleneck", which listed `Bl_p(P3)` among
inputs that "did not complete from the raw top-level input within short
interactive runs"). With the guessed-bound-plus-proof workaround, it now
does complete, end to end, from the pure multigraded presentation -- the
first nontrivial (divisorial-then-fibration) multi-step smooth MMP example
in this project not built from a manually supplied graph.

**Caveat**: `contractionSmallnessData`'s cost was not investigated further
(no breakdown of what inside it is slow, unlike `steinHomData`'s
resolution-length root cause). Whether it generalizes cheaply to other
multi-step examples, or becomes its own new bottleneck on a harder input,
is unknown.

## Suggested next steps

- **Adopt the guessed-bound + independent-verification pattern as the
  default recovery path** when `steinHomData`'s certified-bound resolution
  is infeasible, mirroring `blowup-twisted-cubic.m2`: try
  `steinHomDataAtBound` at a small bound, and check the resulting Krull
  dimension and a few Hilbert function values against whatever is
  independently known about the expected target (even a partial invariant,
  such as expected dimension alone, is informative). Where no independent
  geometry is known in advance, fall back to `steinDataByStabilization`'s
  automated guess-and-increase loop, understanding its match is evidence,
  not proof.
- Run `steinDataByStabilization` itself (not just two manual
  `steinHomDataAtBound` calls) on this input, to confirm the automated
  stabilization loop reaches the same conclusion without needing the
  independently-known target in advance.
- Test whether the guessed-bound path's own cost grows sharply with `r`
  (only `r=1,2` were measured; `r=3+` was not) -- if it does, the workaround
  may only postpone, not remove, the wall on harder inputs.
- Profiling Macaulay2's own resolution algorithm on the specific
  265-generator/29-variable ideal that makes the *certified* path infeasible
  (which Betti numbers explode between homological degree 2 and 4) remains
  a separate, not-yet-attempted line of investigation, orthogonal to the
  workaround above.
- Since `maxHomologicalDegree = d1+d2+1` scales with **total product-ring
  variable count** (`sourceVariableCount+targetVariableCount`), reducing
  either side would directly lower the resolution length the *certified*
  path demands. `sourceVariableCount` comes from `diagonalSubalgebraData`'s
  flattening of `w` (19 here, vs Stage 1's 9 for `w=(1,1)`) and
  `targetVariableCount` from the number of sections of the threshold divisor
  (10 here, `h^0(O_{P3}(2))`). Whether a `w` exists reaching a genuine
  divisorial contraction with a smaller combined variable count was not
  investigated.
- Given the workaround above, a nontrivial multi-step smooth MMP example is
  no longer blocked by this bottleneck by default -- **confirmed**: see
  "Capstone" below, `Bl_p(P3) -> P3 -> point` now completes end to end.
  Picard-rank-one examples (single contraction to a point) remain the
  simplest fallback where no workaround is needed at all.
- Profile `mmpStepRecordData`'s `contractionSmallnessData` step (~13-14 min
  cpu in the capstone run below, the new dominant cost once Stein
  factorization itself is unblocked) the way `steinHomData` was profiled
  down to its resolution-length root cause -- not yet attempted.
- Do **not** spend effort building a `g`-finiteness check, nor a `g∘h=f`
  substitution check: both hold automatically at every bound (proved above)
  and would carry no information about whether a guessed bound was large
  enough.
- **For a birational guessed-bound candidate, `isNormal(C_r)` (or
  equivalently `integralClosure`) is the correct, necessary-and-sufficient
  check** for `h_*O_Y=O_Z` -- not a stand-in for something cheaper. Effort
  toward making this fast should target the normality computation itself
  (e.g. `integralClosure` instead of the generic `isNormal`, or exploiting
  `Y`'s own known exceptional-divisor structure to check only those
  finitely many loci via Serre's S2/Hartogs codimension-2 extension,
  rather than running a from-scratch singular-locus computation on the
  freshly built candidate ring).
- **Implement and test the "already normal + already connected" fast-path**
  flagged above: before invoking `steinHomData`/`steinHomDataAtBound` at
  all, cheaply check whether the *given, already-known* candidate target
  ring is normal and whether a spot-checked fibre of `f` is
  connected/irreducible. Both of this project's measured Stein-
  factorization-exercising examples (Segre and this report's `Bl_p(P3)`)
  would have skipped the entire bottleneck this way. Whether this holds
  broadly for MMP extremal contractions (plausible, given their
  `Proj`-of-a-section-ring construction) was not tested beyond n=2.
