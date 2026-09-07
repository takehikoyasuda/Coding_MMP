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
   (Both have since changed: the entry point is `computeRelativeCanonicalModel`,
   and the schedule is the paper's own consecutive `m = 1, 2, 3, ...`, the
   revision having dropped the divisibility condition that the factorial
   sequence existed to satisfy.)
5. Preserved the genuine toric, projective, and index-two regressions; all 13
   package tests and four worked examples pass on M2 1.26.06.

## Milestone 3: implement contractions

1. **Implemented:** represent public contraction and relative-model graphs
   uniformly as `GraphMorphism`, with an adapter for legacy integration and
   Stein graph tables.
2. **Implemented:** construct the weighted ample Cartier divisor and decide
   canonical-divisor nefness by the paper's parallel base-point-free searches.
3. **Implemented:** compute the nef threshold by dyadic bracketing and the
   finite rational candidate search.  Scaled threefold nef tests now use the
   improved Proposition 3.1 guaranteed test directly: multiplier 7 for `N=1`
   and 6 for `N>=2`.  The negative-curve shortcut remains only for older
   high-dimensional fallback bounds.
4. **Implemented:** construct the complete-linear-system graph and pass it
   through corrected Stein factorization to obtain the contraction.

## Milestone 4: implement the MMP driver

1. **Implemented:** distinguish fibre type from birational contractions by
   source and connected-fibre target dimensions.
2. **Implemented:** compute the relative canonical model for birational steps,
   returning the target itself in the Cartier case and otherwise using the
   relative canonical algebra / flip computation.
3. **Implemented:** test whether the relative canonical model is an
   isomorphism using invertibility of its canonical blow-up ideal.
4. **Implemented:** recover explicit homogeneous coordinates for the rational
   inverse of a nonidentity relative-model projection by substituting its Rees
   generators into the Segre coordinates, and certify the graph equations and
   indeterminacy locus.
5. **Implemented:** extend the Segre graph bridge to skew Rees fibre degrees by
   choosing an interior integral diagonal with positive transformed weights;
   the weighted toric flip now passes through graph and inverse construction.
6. **Implemented:** compute the exceptional-locus codimension from the support
   of the second exterior power of relative differentials and record
   divisorial, flipping, and mixed steps without losing either graph.
7. **Implemented:** the top-level driver iterates birational models and stops
   at a nef canonical divisor or a K-negative fibration.  A certified
   `Bl_L(P3) -> P3` divisorial prefix is retained while the continued driver
   reaches the contraction `P3 -> point`.

Every milestone should add worked examples whose expected geometry is known
independently of the implementation.

## Milestone 5: the relative setting, over an affine base

The paper's Definition 2.1 has `R_0 = k`, so `X = Proj R` is projective over a
point.  Giving some ambient variables degree zero puts their coordinates in
`R_0` and makes `X` projective over the affine `Spec R_0`.  This is where the
standard three-fold flips live without being compactified first, and it removes
both of the walls the compact search ran into: no compactification has to be
found, and no Segre flattening is needed to raise the dimension.
`references/AlgoMMP/RELATIVE-SETTING-AUDIT.md` audits what the paper's
statements need there; this milestone is what the code needs.

1. **Implemented:** decide canonical nefness over an affine base.  A
   degree-zero variable is a coordinate on the base, not a malformed input:
   `weightedAmpleDivisorData` takes the lcm of the positive weights only, and
   `multigradedBlockData` assigns such a variable to no block.
2. **Implemented:** contract to the affine base.  In the one-section case the
   morphism is the structure morphism `X -> Spec R_0`, whose target has
   dimension `dim R_0` and not zero.
3. **Implemented:** normalize divisors by the irrelevant ideal.  Over an affine
   base `ht(B)` can be one, and then a divisor of `Spec R` can have components
   inside `V(B)` that are not on `X` but do change the graded module and every
   section count taken from it (section 9.1 of the audit).
4. **Implemented:** the Cartier test, the canonical index, and the
   canonical-ideal seed over an affine base.  `isCartier`'s graded branch
   saturates against the homogeneous maximal ideal, which there contains the
   base coordinates and discards the point over the origin of `Spec R_0`; the
   seed embeds `omega_R`, which is the unnormalized divisor's module.
5. **Implemented:** smallness of the structure morphism, from the relative
   differentials of `Spec R` over `Spec R_0`, and the relative canonical model
   over an affine base, re-graded from FlipComputation's Rees presentation into
   the form the driver reads.
6. **Implemented:** a negative-curve certificate for the relative setting.
   Every curve proper over `k` lies in a fibre, and for a birational structure
   morphism the positive-dimensional fibres are its exceptional locus, so the
   search range is that locus; the two intersection numbers with `a*K` and `H`
   are computed once and every threshold candidate is then decided by
   arithmetic.  Without it the threshold search does not finish.
7. **Not implemented:** a contraction whose target is neither the base nor a
   point.  `Phi_{|MD|}` is built as a morphism to `P^{n-1}`, which over an
   affine base is the absolute morphism and forgets the base; the relative
   target is a `Proj` over `Spec R_0`, and the Stein factorization of it needs
   the `A`-module version of `lem:section-ring-over-k` (sections 5 and 6 of the
   audit).  That case is refused with a warning rather than answered.  Until it
   is in, a relative MMP over a fixed affine base is at most one birational
   step long, since the only contraction it can build is the one to the base
   and Algorithm 4 then returns the whole relative canonical model at once.
8. **Not implemented:** an exact Cartier test for weighted gradings.  On a
   weighted presentation `Spec R - V(B)` is not a torsor over `X`, so a divisor
   can be locally free on the punctured cone without being invertible on `X`,
   and the test over-reports.  A Veronese presentation avoids it; see
   `examples/07-affine-base-flip.m2`.
