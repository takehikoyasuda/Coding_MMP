# Implementation status

Baseline recorded on 2026-08-12 with Macaulay2 1.26.06.

## Pinned sources

| Component | Commit | Upstream branch at import |
| --- | --- | --- |
| Paper (`AlgoMMP`) | `dda50e7` | `revise/bigraded-degrees` |
| `SteinFactorizationM2` | `321135a` | `fix/paper-stein-graph` |
| `flip-computation` | `28cefcc` | `main` |

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
| Relative canonical model / flip | `computeFlip` | prototype; genuine toric examples exist |
| Nefness of the canonical divisor | none in this repository | not implemented |
| Threshold and extremal contraction | none in this repository | not implemented |
| Top-level threefold MMP loop | none in this repository | not implemented |

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
- `flip-computation`: 12 of 13 package tests pass. Test 11
  (`FlipComputation.m2:339-361`) fails on Macaulay2 1.26.06 at an assertion in
  the weighted projective toric example. The package also reports that
  `Divisor` has been renamed to `WeilDivisors`. This is an upstream baseline
  failure, not an integration regression.

Run the same baseline with:

```sh
make test-upstreams
```
