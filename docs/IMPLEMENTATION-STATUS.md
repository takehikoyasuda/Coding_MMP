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
| Top-level threefold MMP loop | `threefoldMMPData` | P3 K-negative-fibration, quintic minimal-model, and certified Bl_L(P3) birational-continuation regressions pass |

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
