# Implementation status

Baseline recorded on 2026-08-12 with Macaulay2 1.26.06.

## Pinned sources

| Component | Commit | Upstream branch at import |
| --- | --- | --- |
| `SteinFactorizationM2` | `321135a` | `fix/paper-stein-graph` |
| `flip-computation` | `ddfe5b9` | `fix/m2-1.26-weil-divisors` |

The paper itself (Takehiko Yasuda, *An algorithm for the minimal model
program in dimension three*, [arXiv:2603.13703](https://arxiv.org/abs/2603.13703))
is developed in a separate, private repository and is not pinned here as a
submodule.

The source repositories had the following local state at import time:

- the imported Stein and flip source trees had no uncommitted files;
- the original Stein source was on `codex/manual-revision-independent`; the
  corrected graph implementation now lives on `fix/paper-stein-graph`.

## Paper-to-code map

| Paper construction | Current implementation | Status |
| --- | --- | --- |
| Bigraded global Hom | `bigradedGlobalHomData` | prototype; standard tests pass |
| Stein coordinate algebra | `steinHomData`, `steinCoordinateAlgebra` | prototype; standard tests pass |
| Graph of the connected-fibre map | `directSteinGraph` | corrected kernel construction; standard tests pass |
| Relative canonical model / flip | `computeRelativeCanonicalModel` | prototype; all 13 tests and four examples pass |
| Canonical divisor and canonical ideal | `mmpCanonicalDivisorInternal`, `canonicalIdealSeedDataInternal`, `noetherCanonicalIdealSeedInternal` | `canonicalDivisor` from `WeilDivisors` by default; past codimension 12 a Noether-normalization route with a fallback to it (see below) |
| Cartier index of the canonical divisor | `canonicalIndexData` | searches `m` up to `CanonicalIndexSearchLimit`; the cheap certificates are read as sufficient conditions only (see below) |
| Nefness of the canonical divisor | `canonicalNefData`, `isCanonicalNef` | initial implementation; P3 and quintic regressions pass |
| Nef threshold | `canonicalNefThresholdData`, `canonicalNefThreshold` | small-multiple BPF and negative-curve fast paths plus effective fallback; P3 regression passes |
| Extremal contraction | `canonicalContractionAtThresholdData`, `canonicalContractionData` | initial implementation; P3 point and Segre P1xP2 fibre contractions pass |
| Contraction type | `contractionTypeData` and classification fields on contraction results | P3/point and Segre are fibre type; blow-up of a line is birational |
| Graph representation | `mmpGraphMorphism`, `GraphMorphism` | complete-linear-system, Stein contraction, and relative-model graphs share one representation |
| Relative canonical model | `relativeCanonicalModelFromBaseData`, `relativeCanonicalModelData` | P3 identity and projective toric flip regressions pass |
| Relative-model isomorphism | `relativeCanonicalModelIsomorphismData` | certified by the saturated non-locally-free locus of the canonical blow-up ideal |
| Inverse relative-model rational map | `relativeModelInverseRationalMapData` | explicit Segre/Rees coordinates; toric flip equations and base locus certified |
| Weighted relative-model graph | `b2mDiagonalData`, `b2mToGraphMorphism` | skew Rees degrees use an interior positive diagonal; weighted toric flip passes end to end |
| Contraction smallness | `contractionGraphSmallnessData`, `contractionSmallnessData` | exterior-power criterion audited; blow-up divisor, ODP small resolution, and identity regressions pass |
| MMP step records | `mmpStepRecordData` | graph-preserving divisorial/flipping/mixed records with automatic smallness |
| Top-level threefold MMP loop | `threefoldMMPData` | P3 K-negative-fibration, quintic minimal-model, and certified Bl_L(P3) birational-continuation regressions pass; over an affine base it finds and carries out a flip from the ring alone, and runs a three-step program of divisorial contractions through two intermediate targets it builds itself |
| Affine base, `R_0` not a field | `affineBaseRingInternal`, `affineBaseIrrelevantIdealInternal`, `dropIrrelevantComponentsInternal`, `mmpIsCartierInternal`, `affineContractionSmallnessInternal`, `affineExceptionalIdealInternal`, `affineFibreCurvesInternal`, `affineNegativeCurveShortcutInternal`, `affineTargetPresentationInternal`, `affineRelativeModelRingInternal` | see below |

## The relative setting: `X = Proj R` over the affine `Spec R_0`

Giving an ambient variable degree zero puts its coordinate in `R_0`, and
`X = Proj R` becomes projective over the affine `Spec R_0` rather than over a
point.  The standard three-fold flips live there without being compactified
first.  `references/AlgoMMP/RELATIVE-SETTING-AUDIT.md` audits what the paper's
statements need; what follows is what the code needed.  Every item is inert
when `R_0 = k`.

- **Ghost components.**  Classically the irrelevant ideal `B` is the
  homogeneous maximal ideal, of height `dim R >= 2`, so `V(B)` carries no
  divisor.  Over an affine base `ht(B)` is one exactly when `X -> Spec R_0` is
  birational, and then a Weil divisor of `Spec R` can have prime components
  inside `V(B)`.  Those are not on `X`, but they change the graded module and
  every section count taken from it.  In degree zero dropping them is exact:
  `ht(B) = 1` makes `K(X) = Frac(R_0)`, so `ord_P` vanishes on `K(X)` for a
  ghost prime `P` and the condition the component imposes reads `c_P >= 0`.
  Measured on `Bl_0(A^3)`: the degree-zero sections of `K + 2H` are 4 with the
  ghost and 1 without, and `K + 2H` is trivial there.
- **Cartier tests.**  `isCartier(D, IsGraded => true)` saturates the
  non-Cartier locus against `getIrrelevantIdeal(R)`, the homogeneous maximal
  ideal.  Over an affine base that ideal contains the base coordinates, so the
  saturation discards the point of `X` over the origin of `Spec R_0` -- where a
  relative contraction's singularity sits.  `mmpIsCartierInternal` saturates
  only against `B`, which is the identical answer classically (`B` is generated
  by variables, so `B` is contained in `m` and
  `saturate(saturate(J,m),B) = saturate(J,B)`).
- **The canonical-ideal seed is refused.**  It embeds `omega_R`, which is
  `O_{Spec R}(K)` for the unnormalized divisor, so its degree bookkeeping
  answers about the wrong module.
- **Contraction and smallness.**  In the one-section case the contraction is
  the structure morphism `X -> Spec R_0`; its target ring and an affine-base
  flag are recorded on the result.  Smallness cannot be read off the linear
  system's graph there, since that graph is the absolute morphism to `P^0`;
  `affineContractionSmallnessInternal` applies the same exterior-power
  criterion to `Spec R` over `Spec R_0`.  Its rank assertion is
  `dim R - dim R_0 = 1` rather than a module rank, because over an affine base
  no heft vector exists and `rank`, `prune` and `hilbertFunction` all fail.
- **Negative curves.**  Every curve proper over `k` lies in a fibre, and for a
  birational structure morphism the positive-dimensional fibres are the
  exceptional locus, so the search range is narrower than in the absolute
  setting.  `(a*K).C` and `H.C` are computed once and every threshold candidate
  `p/q` is decided by `q*(a*K).C + a*p*(H.C)`.  Without this the threshold
  search does not finish: on the flip's source the bracket is `(1/4, 1/2]`,
  whose candidates have denominators up to 31, and a base-point-free test at
  denominator 8 runs for more than fifteen minutes.  The `t = 1/4` test drops
  from 51 seconds to 0.48.  The degrees are read with `basis` rather than
  `hilbertFunction`, since `R/Q` keeps `R`'s degree-zero variables and so has
  no heft vector either.

- **Targets that are neither the base nor a point.**  The relative target is
  `Proj` over `Spec R_0` of the `R_0`-algebra the section representatives
  generate -- again a presentation of the shape the driver reads, so the next
  step starts from it directly.  Building it costs 0.19 s on the toric input
  measured.  Stein factorization is skipped only on a certificate: the morphism
  is certified birational onto its image (0.33 s; with `R` generated in degree
  one over `R_0`, `K(X)` is generated over `Frac(R_0)` by the ratios of the
  degree-one variables, and a degree-zero syzygy exhibiting `u_1 A = u B` puts
  `u/u_1 = A/B` in `Frac(T)`), and the image is checked normal, so Zariski's
  main theorem gives `Phi_* O_X = O` of the image.  Smallness there uses
  `Omega_{X/T}` rather than the graph, and needs no exterior power: the cone map
  is a `mu_e` quotient whose fixed locus lies in `V(B)` and is saturated away,
  and the extension is algebraic, so `Omega` is generically zero and its
  annihilator cuts out the support.  This is what makes a relative program more
  than one birational step long.

- **Programs three steps long.**  Two steps is the shortest length at which a
  sequence exists at all, and in the two-step input each step is also an end:
  the first contracts to an intermediate target, the second is the fibration
  that stops it.  `S3 x A^1` over `A^3` -- the toric surface obtained from `A^2`
  by three successive point blow-ups, times a line -- gives a program with a
  middle.  Its three exceptional curves have `K.E = 0, 0, -1`, and the same
  holds again after each contraction, so the program is forced to contract them
  one at a time and reaches `A^3` in three divisorial steps, the second of which
  both starts from a ring the first step built and hands one on to the third.
  Multiplying by `A^1` rather than by `P^1` keeps the structure morphism
  birational, so `dim R - dim R_0 = 1` and the negative-curve certificate
  applies.  The `P^1` version has the same program on paper, but there the
  fibre has a threshold of its own and it must stay under both surface ones or
  the fibration comes first and the program is over in one step; that forces
  `H.F >= 5`, hence eighteen degree-one generators instead of four, and that
  input was not carried through -- its canonical index alone had not returned
  after eight minutes and ten gigabytes.
- **Variable order in the target presentation.**  The base coordinates go ahead
  of the section variables in `affineRelativeTargetRingInternal`.  Nothing
  downstream reads a variable by position, but the order is the tie-break of the
  monomial order, and over an affine base the degree-zero variables make whole
  strata of monomials equal in degree, so graded reverse lexicographic falls
  through to position on all of them.  Measured on the second model of the
  three-step program, the same ring presented both ways:
  `canonicalNefThreshold` takes 0.68 s with the base coordinates first and
  203.5 s with the section variables first, and the whole three-step program
  goes from about 230 s to about 8.  Only a presentation the driver builds for
  its own next iteration was ever the slow one -- every presentation written by
  hand in this repository is the fast one -- which is why the cost appeared only
  once a step had to start from a ring an earlier step had built.

Three things are not done.  The fibre-type case of the above is refused:
certifying connected fibres there needs the `A`-module version of
`lem:section-ring-over-k`, and the refusal names it.  The cost of the
birational case has no bound in advance: the normality check on the image is a
normality check on whatever ring the sections happen to generate, and that is
cheap when the ring is small.  The two intermediate targets of the three-step
program above are a six- and a five-variable ring, the contraction that builds
the first of them costs 2.5 s with its certificate inside it, and the whole
three-step program through both of them is about eight seconds.  On the
thirteen-variable target of one toric two-step input, the same `isNormal` ran
for four hours and seventeen minutes at 6 GB without finishing.  That cost is
intrinsic there, not a redundant presentation
-- none of the eight fibre variables is removable, so the presentation is
already minimal, and `R1` needs size-nine minors of a 13 by 49 Jacobian.  `R1`
cannot simply be dropped -- birationality only makes the codimension-one points of the
image have finite fibres, which does not stop the image from being singular
there.  And the Cartier test is not exact for weighted gradings: on a weighted
presentation `Spec R - V(B)` is not a torsor over `X`, so a divisor can be
locally free on the punctured cone without being invertible on `X` -- the same
thing that happens to `O(1)` on `P(1,1,2)` -- and the test over-reports.  A
Veronese presentation, where every positive-degree generator has degree one,
avoids it.

Regressions: `tests/relative-affine-flip-mmp.m2`,
`tests/three-step-relative-mmp.m2`.  Worked examples:
`examples/07-affine-base-flip.m2`, `examples/08-three-step-program.m2`.

## WeilDivisors' graded canonical divisor, where its degree read fails

`canonicalDivisor(R,IsGraded=>true)` stops with

```text
error: no method for binary operator - applied to objects:
    -infinity (of class InfiniteNumber) - {0} (of class List)
```

on some ordinary rings.  `internalModuleToIdeal` embeds `omega` as an ideal by
walking the columns of `syz transpose presentation omega`, each a homogeneous
map `omega -> R`, until one is injective, and then reads the degree of the
embedding as `degree(t#0) - (degrees omega)#0` (WeilDivisors.m2:1808).  That
difference is the right one only when the section's *first* component is
nonzero.  The map is homogeneous, so every index `j` with `t#j != 0` gives the
same answer and any one of them will do -- but with `t#0 = 0` the degree of the
zero element is `-infinity` and the subtraction is meaningless.

It is not a corner case.  On `S3 x A^1` over `A^3`, `omega` has four generators
and all three candidate sections start with a zero, so the first candidate
crashes it.  `gradedCanonicalDivisorRetryInternal` is the same construction with
the shift read off the first nonzero component, and `mmpCanonicalDivisorInternal`
uses it only where WeilDivisors' own function fails, so nothing that works today
changes answer.  Checked against `canonicalDivisor` on rings where that one does
return: the identical divisor, not merely a linearly equivalent one.

## Canonical ideal past codimension 12

`canonicalIdealSeedDataInternal` and `mmpCanonicalDivisorInternal` compute the
canonical ideal from a free resolution of `R` over its ambient polynomial ring,
as `Ext^c(R, omega_S)`.  That resolution is out of reach at high codimension:
on `v_3(P^3)` (codimension 16) the `Ext` did not return in 887s, and on the
cyclic cover's flip target (29 variables, codimension 25) it exceeded 8GB.

Past `mmpNoetherCodimThreshold = 12`, measured as `dim ambient R - dim R`, both
functions first try `noetherCanonicalIdealSeedInternal`, which computes

```text
omega_R = Hom_A(R, omega_A)
```

for a Noether normalization `A = k[theta] -> R`, taking the `A`-basis as a lift
of a `k`-basis of the Artinian reduction `R/(theta)` rather than via `pushFwd`.
The multiplication matrices are batched by degree and solved over `k`, with the
`A`-coefficients kept in `A` rather than in `R`; doing this elementwise, or in
`R`, is what makes it intractable.

This is an attempt, not a replacement.  The route returns `null` -- and both
callers then fall through to the `Ext` computation unchanged -- when the ring is
multigraded, when the ambient variables do not all have degree 1, when the
random linear forms `theta` are not a system of parameters, or when the
`k`-basis length differs from `degree R`, which detects that `R` is not
Cohen-Macaulay.  Below the threshold the execution path is the original one
apart from the gate test itself.

Measured: `v_3(P^3)` about eight seconds against the 887s non-return above; the
cyclic cover's flip target gives its canonical divisor in 782s, about thirteen
minutes, and its canonical index, 2, in a further 659s, on a ring where this
path previously died at 15.6GB.

Regression: `tests/noether-canonical-ideal.m2`.

## Canonical index certificates are sufficient only

`canonicalIndexData` tests `m*K` for Cartier-ness with two cheap certificates
before the general `isCartier` call.  `canonicalIdealSeedInvertibleInternal`
reports whether the reflexive power is a *principal* ideal.  Principal certifies
Cartier but is strictly stronger than it -- principal means generated by one
element globally, Cartier only locally -- and the two part company as soon as
`Pic(X)` is bigger than `Z*H`.  Taking the certificate's negative as a verdict
therefore computes

```text
min{ m : m*K lies in Z*H }   rather than   min{ m : m*K is Cartier }.
```

That defect was live until 2026-08-31.  It is not a corner case: on the Segre
threefold `P1xP2`, which is smooth, so every divisor is Cartier and the index is
1, `canonicalIndexData` returned "inconclusive"; on `v_3(P^3)`, equally smooth,
it returned 3.  Only a positive may be taken from either certificate.

Regression: `tests/cartier-index-fastpath.m2`.

## Stein graph correction

The pinned paper computes the graph of `h : Y -> Z` from the kernel of

```text
Psi : B tensor C^[k] -> R_gamma,
```

using the maps from `B` and the embedding `iota` of the Stein coordinate
algebra. The implementation now constructs a joint ring from the source-block
variables and the Stein variables only, maps it to `R_gamma`, and takes the
kernel. The original target coordinates remain internal to `R_gamma`.

The previous code retained the original target and Stein coordinates in one
second grading block, leaving an extra projective scaling parameter. New
identity, square, cube, weighted, fibre-type, and divisorial regressions assert
that the corrected output graph ring has the same Krull dimension as the input
graph ring. Primeness and bihomogeneity are also checked. In the identity,
square, cube, and positive-dimensional-fibre examples, eliminating each graph
block recovers the expected source and Stein intermediate, and substitution
verifies `g o h = f`. Three admissible localization elements in the cubic
example give identical coordinate and graph ideals after renaming variables.

## Baseline test results

- `SteinFactorizationM2`: its standard suite passes with dimension assertions
  that fail for the previous `directSteinGraph`. Package documentation examples
  and the LaTeX technical note also build successfully.
- `flip-computation`: all 13 package tests pass on Macaulay2 1.26.06 after
  migrating the package import from the legacy `Divisor` name to
  `WeilDivisors`. The weighted toric test now checks the invariant
  least-degree canonical embedding rather than a package-dependent canonical
  divisor representative. All four worked examples, the package manual
  examples, and the LaTeX technical note also build successfully.

Run the same baseline with:

```sh
make test-upstreams
```

The integration-layer suite is `make test-core`; `make test` runs it together
with both upstream suites.

The assumptions and justification for automatic contraction-smallness
classification are recorded in [SMALLNESS-CRITERION.md](SMALLNESS-CRITERION.md).
