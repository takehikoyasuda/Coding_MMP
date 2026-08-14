# A complete one-flip MMP ending in a minimal model

**Status**: Success. A genuine small contraction and its relative canonical
model are constructed, the resulting step is classified as `flipping`, and the
public MMP driver terminates immediately afterward with
`terminationType="minimal model"` and exactly one recorded step.

**Date**: 2026-08-14  
**Branch**: `feature/multigraded-stage1`  
**Reproduction**: [`scripts/cyclic-cover-one-flip-minimal.m2`](../scripts/cyclic-cover-one-flip-minimal.m2)

## Executive summary

The earlier compact toric search could not succeed globally: a positive-
dimensional complete toric variety cannot have nef canonical divisor. The useful
part of that search was local, however: the circuit

```text
v1 + v2 = 2 v3 + v4
```

gives a very small genuine threefold flip. The successful construction keeps
this local toric flip but destroys global toricity by taking a cyclic cover.

Let `W` be the existing compact projective circuit base and let `A=O_W(1)` be
its polarization. Take the degree-four cyclic cover

```text
W' -> W,
c^4 = y_1^4 + ... + y_5^4 + w^4.
```

The cyclic-cover canonical formula is

```text
K_{W'} = pi^*(K_W + 3A).
```

The same formula holds on the two small modifications. An independent exact fan
calculation gives

```text
K_{X^-} + 3A : not nef
K_{X^+} + 3A : nef.
```

Thus the cover preserves the relative sign of the circuit flip while adding
exactly enough global positivity to make the post-flip model minimal.

The complete run takes about 7.6 CPU seconds on the same machine used for the
other August 2026 reports.

## Construction

The common projective base is the standard-graded ring already used by
`tests/relative-model.m2`:

```m2
rayList = {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1..y_(#HB)];
I0 = ker map(L,S0,apply(HB,
    h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
```

Adjoin one standard-graded cyclic-cover variable:

```m2
T = QQ[y_1..y_(#HB),w,c];
Wcover = T/(sub(I0,T)
    + ideal(c^4-(y_1^4+...+y_5^4+w^4)));
```

The defining ideal is prime. The projective singular locus is checked directly
to be

```text
ideal(y_1,...,y_5),
```

which, together with `c^4=w^4`, is a reduced zero-dimensional scheme (four
points over the algebraic closure). Hence the Fermat branch introduces no new
singularities away from the old circuit point. Near those four points the cover
is etale, so the two small modifications are etale base changes of the familiar
terminal local flip.

## The contraction

`ideal(D)` in `WeilDivisors` represents `O(-D)`. The flipping side is therefore
constructed as the second anti-canonical relative Proj:

```m2
Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase);
antiProjection = bigradedReesProjection antiIdeal;
```

The second Veronese is needed because the flipping chamber has local index two.
The implementation verifies

```text
isSmallProjection(antiProjection) = true
isS2Source(antiProjection)        = true.
```

Smallness supplies `R1`, so `small + S2` proves normality of the source. A fibre
over the point `y_1=...=y_5=0, w=c=1` has dimension one. The morphism is
therefore non-isomorphic and contracts curves, while its exceptional locus has
codimension two. Since the relative tautological class is a positive multiple
of `-K`, the contracted curves are `K`-negative.

The contraction graph is not supplied by hand:

```m2
antiGraph = b2mToGraphMorphism(antiProjection,Verbose=>false);
```

Its monograded source presentation has 35 variables.

## The flip

The contraction target is `Wcover`. The actual relative canonical model is then
computed by the project code:

```m2
flipModel = relativeCanonicalModelData(
    contraction,RelativeCanonicalMultipliers=>{1,2});
```

The result is conclusive and nonidentity. Its source ring is a 14-variable
presentation of `Xplus`. Combining the independently certified smallness with
this nonidentity relative canonical model gives

```m2
flipStep = mmpStepRecordData(
    contraction,flipModel,ContractionIsSmall=>true);
```

and the recorded type is exactly

```text
stepType = "flipping".
```

This is one MMP flip step. Over the algebraic closure it flips the four conjugate
local curves lying over the four points of the cyclic cover simultaneously.

## End-to-end MMP result

The public three-argument driver is designed to continue after a certified
birational prefix. Passing the freshly constructed flip step and its freshly
constructed next ring gives

```m2
result = threefoldMMPData(Xplus,1,{flipStep});
```

Measured output:

```text
cyclic-cover base cpu=1.65914
anti-canonical source and contraction cpu=4.58663
relative canonical model and flip step cpu=5.27137
complete MMP cpu=7.5743
sourceVariables=35
flipVariables=14
stepType=flipping
exceptionalFibreDimension=1
terminationType=minimal model
numberOfSteps=1
finalNef=true
```

The final `nef=true` is produced by the general `canonicalNefData` path inside
`threefoldMMPData`, not by the toric oracle used to design the example. The
toric calculation and the general BPF/nef calculation are independent checks of
the same conclusion.

## Exact scope of “end to end”

No contraction graph and no post-flip ring is hand-written. The script constructs

```text
cyclic-cover base
  -> anti-canonical source and its contraction graph
  -> relative canonical model
  -> flipping step record
  -> MMP minimal-model termination.
```

The first step is passed through the driver's documented certified-prefix API,
rather than rediscovered by calling `canonicalContractionData` on the flattened
35-variable source. This is deliberate: the natural anti-canonical source is a
9-variable bigraded Rees presentation, while the current top-level driver has no
entry point taking a multigraded polarization and irrelevant ideal. Flattening
it before the nef/threshold search recreates the already documented
monograded-global-section bottleneck. The contraction itself and the relative
canonical model are nevertheless both constructed and certified by the project
code in the same run.

## Significance

This is the first example in the project with all of the following at once:

- a genuine small `K`-negative contraction;
- a nonidentity relative canonical model;
- a recorded `flipping` step;
- exactly one MMP step;
- termination at a minimal model rather than a Mori fibre space;
- a complete run in seconds rather than minutes.

It also explains the correct role of the earlier toric search: use the fan to
design and certify the local flip and the divisor inequalities, then add global
canonical positivity by a cyclic cover before running the general MMP code.
