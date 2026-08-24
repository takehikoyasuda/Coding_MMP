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
- `SteinFactorizationM2`'s documentation now names the quotient stacks the
  algorithm is stated over, and says why the grading on `C` is the one it is
  (`d3a2bfd`). The top node had called the input "a bigraded projective
  scheme"; `steinHomData` had stated the polarization without a reason for it.
  Remark 5.2's caveat is kept: the stacks retain every graded piece `C_v`
  because `O_X(v)` is a line bundle on the stack for every `v`, whereas the
  coarse space restricts to multiples of the weight lcm `l` -- the Veronese
  subrings `A^(l)`, `C^(l)`, giving the same `Z -> X` at higher degrees -- so
  they are a computational convenience, not intrinsic to Stein factorization.
  Documentation only; `make docs` builds clean and `run-tests.sh` passes.
  `flip-computation`'s "bigraded variety" wording follows Definition 2.5,
  which is scheme-theoretic, and was left alone.
- `IrrelevantIdeal` now accepts the `B2MProjection` or `GraphMorphism` that
  built the ring, not only an ideal, so a caller no longer writes
  `sub(P#irrelevantIdeal,R)` by hand. The eight entry points that validated
  the option separately share one `normalizeIrrelevantIdealOption`, which also
  rejects a provenance object whose ambient variables do not match the ring's
  -- `substitute` maps by position between rings of equal generator count, so
  without that guard an unrelated object would have produced a wrong ideal
  silently. The existing `(BasicDivisor,B2MProjection)` predicate overloads
  had no such guard.

  The framing came from the observation that an irrelevant ideal is the
  product of the ideals of the variable blocks and nothing else, so what
  decides it is the *partition* of the variables -- not an ideal, which cannot
  leave the ring it lives in. Measured on `tests/multigraded-skew-cartier.m2`'s
  ring `Z` and now asserted there: each `B` is exactly its own partition's
  product, and the provenance and heuristic partitions differ only in where
  `u_2`, of skew degree `(1,1)`, is put. That is the whole defect.

  The threading stops at the multigraded entry points on purpose. On a singly
  graded ring there is one block, so `B` is the ideal of all the variables with
  nothing to classify (asserted for `P^3`), and `threefoldMMPData`'s own
  `nextRing` is monograded, so the `(Ring,ZZ,List)` loop needs no provenance
  ideal and accepting one there would only add a way to be wrong.
- The multigraded entry points are documented, and `make install`'s 33
  `missing node` warnings are gone (0 warnings, 0 errors). All 33 were option
  nodes -- `[method, Option]` -- not missing method nodes, so every `@TO`
  link from `IrrelevantIdeal`, `DivisorClassDegrees` and the search-limit
  symbols into the methods that accept them was dead. The overloads taking an
  ample class `H` were added as keys to their existing method nodes
  (`canonicalNefData`, `canonicalNefThresholdData`, `canonicalScaledNefData`,
  `canonicalContractionAtThresholdData`, `canonicalContractionData`), each with
  a paragraph saying that `H` must be supplied because
  `weightedAmpleDivisorData` reads a single set of weights, and that
  `IrrelevantIdeal` takes an ideal or the provenance object.

  Two corrections to what this file previously said. `threefoldMMPData(R,a,H)`
  was already documented, contrary to the list here. And two of the options are
  accepted but unusable: `isCanonicalNef` and `canonicalNefThreshold` declare
  `IrrelevantIdeal` through `options canonicalNefData` /
  `options canonicalNefThresholdData`, yet have no overload taking `H` and drop
  the option when forwarding, so it can never take effect. Their nodes say so
  rather than implying otherwise; whether to reject it there instead is a
  behaviour question, left alone.

  Also fixed in passing: six typewriter-text markups in the manual were
  broken -- five `{tt ...}` missing the backslash, and one carrying a literal
  tab where `\t` belonged -- so those words rendered as `tt ...` instead.

## Outstanding

### 1. Divisorial relative canonical models are not computed

Lemma 6.6's test asks the projection to be small, so
`computeRelativeCanonicalModel` accepts only the identity or a small model. A
relative canonical model that is genuinely divisorial is refused at every
multiplier, and raising `MaxMultiplier` cannot help. Since `50c032f` this is
reported as an inconclusive result rather than an error, and the manual says
so, but the case is not implemented and there is no example of one.

`mmpStepRecordData`'s `"mixed"` classification anticipates it; the existing
test constructs that label by passing `ContractionIsSmall => false` to a model
that is in fact small, so the genuinely divisorial path is untested.

### 2. Repository visibility

`SteinFactorizationM2` is public. `Coding_MMP` and `flip-computation` are
still private and are to be made public when the revision appears on arXiv.
Both have been checked for secrets and local absolute paths, and their
histories rewritten where such paths appeared.
