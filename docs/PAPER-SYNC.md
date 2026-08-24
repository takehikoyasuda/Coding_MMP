# Synchronizing the code with the paper revision

Status of this repository and its two submodules against the revised paper
(v3), and what is still outstanding. Written 2026-08-24.

Check against the paper repository's `main`: the revision branch
`revise/prop-hom-display-formula` has been merged into it, and `main` carries
further copy-editing commits on top (drafting annotations and commented-out
body text removed, citation labels standardized, bibliography trimmed). Its
`Use of AI` section reads "the first two arXiv versions" and "third version",
so `main` is the v3 state. Corrected 2026-08-24; this file originally said the
revision was only on the branch and that `main` was pre-revision, which was
already untrue when it was written.

## The three changes that prompted this

1. **Bigraded varieties admit mixed degrees.** Section 2.2 now sets
   `deg(y_j) = (d_j,0)` and `deg(x_i) = (a_i,c_i)` with `a` a further datum;
   the second block's variables may be nonzero in the first component.
   Section 4's ambient `S` is still strictly block diagonal, so this affects
   the Section 2 constructions and not the global-Hom bound.
2. **Deligne--Mumford stacks.** Section 4 introduces
   `X = [(Spec R - V(R_dagger))/G_m^2]` as the stacky counterpart of
   `biProj R`, with `biProj R` as its coarse moduli space, and states
   Proposition 4.2 and Corollary 4.3 as statements about `Hom` over the stack.
   Section 5.1 and Lemma 6.6 use quotient stacks too.
3. **Flips became relative canonical models.** Section 6 is now "Relative
   canonical models and the minimal model program", Algorithm 4 computes the
   relative canonical model, and a flip is the special case of a small
   contraction.

## Done

Numbering, terminology and behaviour have been brought in line with v3.

- Citations updated throughout to v3's numbering, and the `v2` version pin
  dropped in favour of the version-less arXiv URL (`abc742d`, `0c3adba`,
  `6fdbe70`). §4 keeps Proposition 4.2 and Corollary 4.3; §5's evaluation
  lemma moved from Lemma 5.2 to Lemma 5.3, Lemma 3.5 to Lemma 3.6, the Stein
  algorithm from Algorithm 1 to Algorithm 2, and the relative-canonical-model
  algorithm from Algorithm 3 to Algorithm 4.
- `multiplierSchedule` removed and `MaxSteps` replaced by `MaxMultiplier`
  (`0c3adba`, `abc742d`). Lemma 6.6 imposes no divisibility condition on `m`
  and Algorithm 4 enumerates `m = 1, 2, 3, ...`, so the divisors-of-`n!`
  detour lost its reason to exist; it was also skipping `5, 7, 9, ...`.
- `computeRelativeCanonicalModel` returns the identity when the canonical
  class is trivial, as Algorithm 4 Step 3 asks (`c2d3235`).
- An exhausted multiplier search is reported as
  `"conclusive" => false, "phase" => "relative canonical model"` instead of
  escaping as a raw error through `threefoldMMPData` (`50c032f`).
- `computeFlip` renamed to `computeRelativeCanonicalModel` and
  `flipDivisorData` to `antiCanonicalDivisorData` (`4173285`, `56c8e2e`).
  Repository names, the package name `FlipComputation`, file and directory
  names, and the `examples/toric-flip*.m2` filenames are deliberately
  unchanged: Remark 6.12 of the paper gives the repository URLs and the paper
  is on arXiv.
- Skew (mixed-degree) multigraded rings no longer get a guessed irrelevant
  ideal (`1e87a0d`); see the next section for what that leaves open.

## Outstanding

### 1. Say what the stack computation computes (change 2 above)

The computation itself does not change -- the code evaluates Corollary 4.3's
right-hand side, `Hom_R(M_{>=r},N)_{>=0}`, which is a statement about graded
modules either way. What changes is what the answer *means*, and two places in
`SteinFactorizationM2` describe it in pre-revision terms:

- [`SteinFactorization.m2:573`](../third_party/SteinFactorizationM2/SteinFactorization.m2#L573)
  calls the input "a bigraded projective scheme". The paper hedged that word
  in scare quotes before the revision and now has an actual stack to name.
- [`SteinFactorization.m2:650`](../third_party/SteinFactorizationM2/SteinFactorization.m2#L650)
  says `C` "is the section ring of `Z` for the polarization pulled back from
  `X`". True, but Remark 5.2 can now say why the grading is the one it is.

Remark 5.2 is the material to draw on: the quotient stacks are used to retain
all grading indices, because `O_X(v)` is a line bundle on the stack for every
`v`, so every graded piece `C_v` can be kept. On the coarse space one is
restricted to multiples of `l = lcm` of the weights, which raises the degrees
the computation runs at. The remark also notes the stacks are not intrinsic to
Stein factorization -- the same `Z -> X` comes out either way.

`flip-computation` says "bigraded variety" in a few places
(`FlipComputation/basics.m2`, `FlipComputation/doc.m2`); those follow Section
2's Definition 2.5, which is scheme-theoretic, so they are already correct.

Cheap, self-contained, no correctness risk.

### 2. Document the multigraded entry points

`make install` emits 33 `missing node` warnings. The substantive ones are the
multigraded overloads, which are exported but have no documentation node:
`canonicalNefData(R,a,H)`, `canonicalScaledNefData(R,a,t,H)`,
`canonicalContractionAtThresholdData(R,a,lambda,H)`,
`canonicalContractionData(R,a,H)`, `threefoldMMPData(R,a,H)`, and the option
nodes they cite (`IrrelevantIdeal`, `DivisorClassDegrees`, and the various
search limits).

This matters more since `1e87a0d`: on a skew multigraded ring these entry
points now *stop* rather than guessing an irrelevant ideal, and the message
tells the caller to supply `IrrelevantIdeal`. That instruction is currently
only in `IrrelevantIdeal`'s own node, and the entry points where a caller
meets it are undocumented.

Sequencing: item 3 below changes what this documentation should say, so do
item 3 first, or write item 2 knowing it will need revisiting.

### 3. Thread the provenance irrelevant ideal through the pipeline

`multigradedBlockData`'s block-classification heuristic is still uncorrected.
`1e87a0d` made every caller refuse to trust it unless the degree matrix is
verifiably block *diagonal*, so the failure mode is now a clear error rather
than a silent wrong answer -- but on a skew ring the caller has to supply
`IrrelevantIdeal` by hand.

`B2MProjection` and `GraphMorphism` already carry the correct
`irrelevantIdeal` from the construction that built them. Passing it down
automatically (from `relativeCanonicalModelFromBaseData` and the contraction
data into the nef/threshold/contraction calls) would remove the manual step.

This is a usability improvement now, not a correctness fix -- `1e87a0d`
removed the correctness problem. `tests/multigraded-skew-cartier.m2` pins the
current behaviour and `research-log/docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md`
has the analysis.

### 4. Divisorial relative canonical models are not computed

Lemma 6.6's test asks the projection to be small, so
`computeRelativeCanonicalModel` accepts only the identity or a small model. A
relative canonical model that is genuinely divisorial is refused at every
multiplier, and raising `MaxMultiplier` cannot help. Since `50c032f` this is
reported as an inconclusive result rather than an error, and the manual says
so, but the case is not implemented and there is no example of one.

`mmpStepRecordData`'s `"mixed"` classification anticipates it; the existing
test constructs that label by passing `ContractionIsSmall => false` to a model
that is in fact small, so the genuinely divisorial path is untested.

### 5. Repository visibility

`SteinFactorizationM2` is public. `Coding_MMP` and `flip-computation` are
still private and are to be made public when the revision appears on arXiv.
Both have been checked for secrets and local absolute paths, and their
histories rewritten where such paths appeared.
