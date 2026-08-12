# Implementation status

Baseline recorded on 2026-08-12 with Macaulay2 1.26.06.

## Pinned sources

| Component | Commit | Upstream branch at import |
| --- | --- | --- |
| Paper (`AlgoMMP`) | `dda50e7` | `revise/bigraded-degrees` |
| `SteinFactorizationM2` | `3602a2a` | `codex/manual-revision-independent` |
| `flip-computation` | `28cefcc` | `main` |

The source repositories had the following local state at import time:

- the paper working tree contained additional uncommitted edits to
  `AlgoMMP.tex`, `REVISION-PLAN.md`, and `tmp/`; the submodule deliberately
  pins only commit `dda50e7`;
- the Stein and flip source trees had no uncommitted files;
- the Stein source was on a development branch that must not be merged into
  its `main` branch as-is, according to its own `PROJECT-STATUS.md`.

## Paper-to-code map

| Paper construction | Current implementation | Status |
| --- | --- | --- |
| Bigraded global Hom | `bigradedGlobalHomData` | prototype; standard tests pass |
| Stein coordinate algebra | `steinHomData`, `steinCoordinateAlgebra` | prototype; standard tests pass |
| Graph of the connected-fibre map | `directSteinGraph` | **known mathematically incorrect** |
| Relative canonical model / flip | `computeFlip` | prototype; genuine toric examples exist |
| Nefness of the canonical divisor | none in this repository | not implemented |
| Threshold and extremal contraction | none in this repository | not implemented |
| Top-level threefold MMP loop | none in this repository | not implemented |

## Stein graph mismatch

The pinned paper computes the graph of `h : Y -> Z` from the kernel of

```text
Psi : B tensor C^[k] -> R_gamma,
```

using the maps from `B` and the embedding `iota` of the Stein coordinate
algebra. The pinned Stein package instead retains coordinates of the original
target and the Stein target in the same second grading block. That leaves an
extra projective scaling parameter. Identity, square, and cube examples can
therefore return a ring of Krull dimension four where the input graph ring has
dimension three, even though primeness and homogeneity tests pass.

Until this is replaced, the trusted Stein scope ends at the coordinate algebra
and the finite map to the original target.

## Baseline test results

- `SteinFactorizationM2`: its standard suite passes. This does not validate
  `directSteinGraph`, because the existing assertions do not detect the known
  dimension error.
- `flip-computation`: 12 of 13 package tests pass. Test 11
  (`FlipComputation.m2:339-361`) fails on Macaulay2 1.26.06 at an assertion in
  the weighted projective toric example. The package also reports that
  `Divisor` has been renamed to `WeilDivisors`. This is an upstream baseline
  failure, not an integration regression.

Run the same baseline with:

```sh
make test-upstreams
```
