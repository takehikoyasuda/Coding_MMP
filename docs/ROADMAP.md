# Roadmap

The implementation order follows dependency order in the paper.

## Milestone 1: synchronize Stein factorization with the paper

Completed:

1. Replaced the old `directSteinGraph` construction.
2. Implemented the kernel map `B tensor C^[k] -> R_gamma` from the pinned paper.
3. Added dimension assertions that fail on the old identity, square, and cube
   outputs, and extended them to weighted and higher-dimensional examples.
4. Rebuilt the package manual and technical note with the revised construction.
5. Added elimination checks for both graph projections and substitution checks
   for `g o h = f`.
6. Verified independence from three admissible localization elements in the
   cubic example.

The old component-based construction is not currently retained: the direct
kernel construction is the algorithm in the pinned paper and the tested path.

## Milestone 2: stabilize the flip package

Completed:

1. Located the weighted test 11 failure: it asserted a particular canonical
   divisor representative returned by the legacy `Divisor` package.
2. Migrated the package and examples to `WeilDivisors`.
3. Replaced the representative-dependent assertion with the invariant
   least-degree canonical embedding used by the current paper and code.
4. Reconciled `computeFlip` with the pinned paper's three-step
   relative-canonical-model algorithm. Its multiplier schedule contains the
   factorial sequence required in the paper while trying smaller divisors first.
5. Preserved the genuine toric, projective, and index-two regressions; all 13
   package tests and four worked examples pass on M2 1.26.06.

## Milestone 3: implement contractions

1. Represent normal monograded threefold input and graph morphisms uniformly.
2. Implement the canonical-divisor nefness test.
3. Construct an ample Cartier divisor and compute the nef threshold.
4. Construct the induced morphism and pass it through corrected Stein
   factorization to obtain the contraction.

## Milestone 4: implement the MMP driver

1. Distinguish fibre type from birational contractions by dimension.
2. Compute the relative canonical model for birational steps.
3. Use corrected Stein factorization to test whether that model is an
   isomorphism.
4. Record divisorial, flipping, and mixed steps without losing graph data.
5. Stop at a nef canonical divisor or a Mori fibre space.

Every milestone should add worked examples whose expected geometry is known
independently of the implementation.
