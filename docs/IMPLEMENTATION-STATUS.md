# Implementation status

Baseline recorded on 2026-08-12 with Macaulay2 1.26.06.

## Pinned sources

| Component | Commit | Upstream branch at import |
| --- | --- | --- |
| Paper (`AlgoMMP`) | `dda50e7` | `revise/bigraded-degrees` |
| `SteinFactorizationM2` | `321135a` | `fix/paper-stein-graph` |
| `flip-computation` | `ac55f7e` | `fix/m2-1.26-weil-divisors` |

The source repositories had the following local state at import time:

- the paper working tree contained additional uncommitted edits to
  `AlgoMMP.tex`, `REVISION-PLAN.md`, and `tmp/`; the submodule deliberately
  pins only commit `dda50e7`;
- the imported Stein and flip source trees had no uncommitted files;
- the original Stein source was on `codex/manual-revision-independent`; the
  corrected graph implementation now lives on `fix/paper-stein-graph`.

## Paper-to-code map

| Paper construction | Current implementation | Status |
| --- | --- | --- |
| Bigraded global Hom | `bigradedGlobalHomData` | prototype; standard tests pass |
| Stein coordinate algebra | `steinHomData`, `steinCoordinateAlgebra` | prototype; standard tests pass |
| Graph of the connected-fibre map | `directSteinGraph` | corrected kernel construction; standard tests pass |
| Relative canonical model / flip | `computeFlip` | prototype; all 13 tests and four examples pass |
| Nefness of the canonical divisor | `canonicalNefData`, `isCanonicalNef` | initial implementation; P3 and quintic regressions pass |
| Nef threshold | `canonicalNefThresholdData`, `canonicalNefThreshold` | initial implementation; P3 regression passes |
| Extremal contraction | `canonicalContractionAtThresholdData`, `canonicalContractionData` | initial implementation; P3 point and Segre P1xP2 fibre contractions pass |
| Contraction type | `contractionTypeData` and classification fields on contraction results | P3/point and Segre are fibre type; blow-up of a line is birational |
| Relative canonical model | `relativeCanonicalModelFromBaseData`, `relativeCanonicalModelData` | P3 identity and projective toric flip regressions pass |
| Relative-model isomorphism | `relativeCanonicalModelIsomorphismData` | certified by the saturated non-locally-free locus of the canonical blow-up ideal |
| Contraction smallness | `contractionGraphSmallnessData`, `contractionSmallnessData` | exterior-power criterion audited; blow-up divisor, ODP small resolution, and identity regressions pass |
| MMP step records | `mmpStepRecordData` | graph-preserving divisorial/flipping/mixed records with automatic smallness |
| Top-level threefold MMP loop | `threefoldMMPData` | P3 Mori-fibre, quintic minimal-model, and certified Bl_L(P3) birational-continuation regressions pass |

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
