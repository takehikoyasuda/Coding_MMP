# Bottlenecks and multigrading notes

This note records the implementation lessons from the August 2026 experiments
after improving the effective threefold base-point-free multiplier in
Proposition 3.1 from the old `1920/1536` scale to `7/6`.

## What improved

The old effective multiplier was no longer the main obstruction after the
threefold bound became

```text
m(3,N) = ceiling(2/N) + 5,
```

so `m(3,1)=7` and `m(3,N)=6` for `N>=2`.

This made the scaled nef tests in Algorithm 1 much more realistic.  The code
now tests the guaranteed small multiples directly in dimension three.  The
negative-curve search from a base locus is retained only as a shortcut for the
older high-dimensional fallback bounds.

The integration tests verify:

- `P3`: non-nefness, threshold `lambda=4`, and the contraction to a point;
- `P3` with an `N=2` scaled test: guaranteed multiplier `6`;
- the Segre threefold contraction at the known threshold;
- quintic threefold minimal-model termination;
- relative-model and step-record regressions.

## Examples that pass

The top-level `threefoldMMPData` currently passes several Picard-rank-one
or nearly trivial cases:

- `P3`: one Mori-fibre step to a point;
- smooth quadric threefold in `P4`: one Mori-fibre step to a point;
- smooth cubic threefold in `P4`: one Mori-fibre step to a point;
- smooth quartic threefold in `P4`: one Mori-fibre step to a point;
- complete intersection `(2,2)` in `P5`: one Mori-fibre step to a point;
- complete intersection `(2,3)` in `P5`: one Mori-fibre step to a point;
- smooth quintic threefold in `P4`: minimal model, zero steps.

For birational examples, the driver can continue after a certified divisorial
prefix:

- `Bl_L(P3) -> P3`, followed by `P3 -> point`, gives a two-step MMP;
- `Bl_p(P3) -> P3`, followed by `P3 -> point`, also gives a two-step MMP when
  the first contraction graph is supplied.

In both blow-up continuations the relative canonical model is the identity
over the `P3` target, so the post-contraction part is light.

## Examples that expose the next bottleneck

The following are geometrically good candidates but did not complete from the
raw top-level input within short interactive runs:

- Segre `P1 x P2` in `P5`;
- `Bl_p(P3)` presented by converting `Proj Rees(x1,x2,x3)` to a monograded
  source ring;
- `Bl_L(P3)` presented by converting `Proj Rees(x0,x1)` to a monograded
  source ring;
- rational normal scrolls such as `S(1,1,2)` and `S(1,2,2)`.

For the blow-up inputs, the preliminary construction is not the problem:

```text
bigradedReesProjection: about 0.002 sec
b2mToGraphMorphism:    about 0.02 sec
canonicalIndexData:    about 0.56 sec
```

The computation stalls later, in the first `canonicalNefData` call, specifically
around base-point-free tests for divisors on the monograded source ring.

For the Segre example, the known contraction still works when called directly:

```text
K + 3H = O(1,0)
```

and the connected-fibre contraction to `P1` is computed by
`canonicalContractionAtThresholdData(X,1,3)`.  However the full top-level
driver stalls before reaching that threshold construction.  Probing showed:

- `basis(0, OO(2K+H))` quickly returns no sections;
- `basis(0, OO(6*(2K+H)))` did not return within a short run.

Thus the new obstruction is not the large multiplier itself.  It is the cost
of computing global sections and base-point-free certificates after a naturally
multigraded variety has been flattened to a monograded presentation.

## BPF checks tried

The current public predicate is still essentially:

```m2
isBasePointFreeDivisor D := trim baseLocus D == ideal 1_R
```

In `WeilDivisors`, this constructs the degree-zero basis of `OO(D)` and then
uses the annihilator of the cokernel of the evaluation map, followed by
saturation.  The base locus itself is not needed as output, but this route
materializes enough of it to prove base-point-freeness.

Several general evaluation-map alternatives were probed:

- saturating the cokernel module directly;
- saturating `ann coker`;
- testing `dim(R / ann coker) <= 0`;
- testing whether `hilbertPolynomial(coker)` is zero.

The direct cokernel saturation was too naive: it misclassified `O(1)` on `P3`.
The annihilator, dimension, and Hilbert-polynomial variants were closer in
principle but did not improve the hard Segre-style cases in short runs.  The
problem can already appear in the computation of the relevant degree strand of
`OO(D)`, before the final support-empty test.

## Interpretation

The leading implementation bottleneck has moved from the effective multiplier
to monograded global-section and base-point-free computations.

This is most visible for examples whose natural construction is multigraded:
products, scrolls, blow-ups, Rees Proj constructions, and relative models.
Flattening such an object to a monograded ring hides simple degree information
and forces later steps to recover it through heavier Weil-divisor module
computations.

This does not mean that the implementation should use special geometry such as
toric polytopes or the formula `O(a,b)` on a particular Segre product.  The
desired direction is still a general algorithm.  The lesson is instead that
the general algorithm should accept and preserve multigraded presentations.

## Promising direction

The most promising next design is a multigraded-first version of the core
workflow:

1. Allow the working variety data to remain multigraded after products, Rees
   Proj constructions, Stein factorization, and relative canonical models.
2. Represent sheaves and divisor data as multigraded modules when that is the
   natural output of the preceding construction.
3. Compute global sections as specified multidegree strands instead of first
   forcing a monograded diagonal.
4. Test base-point-freeness by the support of the evaluation cokernel with
   respect to the relevant irrelevant ideal, but in the multigraded module
   category.
5. Construct the linear-system graph from the multigraded data, passing to a
   diagonal or Segre-style monograded graph only at interfaces that genuinely
   require a monograded `GraphMorphism`.

This is not a special-case shortcut.  It is a more faithful implementation of
the general algebraic operations produced by the MMP algorithm itself.

## Remaining bottlenecks after multigrading

Even with multigrading preserved, further bottlenecks may remain:

- relative canonical model computations via symbolic powers and Rees algebras;
- growth of rings after flips or relative Proj constructions;
- the `t=0` canonical-nefness search through pluricanonical systems;
- canonical Cartier index searches for singular targets;
- expensive support-empty tests for general multigraded modules.

A third one was found by direct measurement, not merely anticipated: **Stein
factorization's own bigraded global Hom construction (`steinHomData`)**, on a
**smooth**, Cartier-index-1 input, once a divisorial contraction's target has
more than a couple of embedding coordinates. See
[STEIN-FACTORIZATION-COST-EXPERIMENT-REPORT.md](STEIN-FACTORIZATION-COST-EXPERIMENT-REPORT.md):
`Bl_p(P3)` with a polarization tilted toward the blow-down ray (rather than
Stage 1's `w=(1,1)`, which happened to make the threshold divisor exactly
zero) reaches a genuine 3-dimensional-target divisorial contraction cheaply
through nef test, threshold search, and complete-linear-system graph
construction (all well under 15 seconds combined), then stalls unresolved for
30+ minutes in `steinHomData` alone, on a 29-variable product ring with a
265-generator graph ideal. Neither of Stage 1's example inputs exercised
`steinHomData` at this size (one skipped it via the trivial-point-target
shortcut, the other had a much smaller target), so this bottleneck was not
visible in either of Stage 1's "cheap" measurements.

Still, the current experiments suggest that preserving multigrading is the
best next step for obtaining nontrivial end-to-end MMP examples beyond
Picard-rank-one Fano and manually supplied divisorial prefixes.
