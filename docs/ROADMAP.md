# Roadmap

The implementation order follows dependency order in the paper.

## Milestone 1: synchronize Stein factorization with the paper

Completed:

1. Replaced the old `directSteinGraph` construction.
2. Implemented the kernel map `B tensor C^[k] -> R_gamma` from the pinned paper.
3. Added dimension assertions that fail on the old identity, square, and cube
   outputs, and extended them to weighted and higher-dimensional examples.
4. Rebuilt the package manual and technical note with the revised construction.

Remaining review:

1. Strengthen automatic checks of both graph projections and `g o h = f`.
2. Add explicit independence tests for different admissible localization
   elements.
3. Decide whether the expensive component-based construction is useful as a
   small reference implementation.

## Milestone 2: stabilize the flip package

1. Locate the exact assertion failing in weighted test 11 on M2 1.26.06.
2. Migrate from the renamed `Divisor` package interface where necessary.
3. Reconcile `computeFlip` with the pinned paper's current three-step
   relative-canonical-model algorithm.
4. Preserve the existing genuine toric and index-two regressions.

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
