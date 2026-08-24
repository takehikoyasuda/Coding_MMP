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
- The variable blocks of a multigraded presentation can now be named directly,
  with `VariableBlocks => {{...},{...}}`, instead of the irrelevant ideal they
  determine. This is the datum the paper's presentation carries -- Definition
  2.5 writes the ambient as `k[y,x]` and puts `S_dagger = <y_j x_i> S` -- and
  the one the code had been throwing away and guessing back: `multigradedBlockData`
  took a ring alone and classified each variable by the last nonzero entry of
  its degree vector.

  Change 1 above is what makes that guess unsound rather than merely
  redundant. Section 2.2 sets `deg(y_j) = (d_j,0)` but `deg(x_i) = (a_i,c_i)`
  with `a` a further datum, so a second-block variable may be nonzero in the
  first component and is then indistinguishable from a first-block one by that
  rule. `tests/multigraded-skew-cartier.m2`'s `u_2`, of degree `(1,1)`, is
  exactly that, and it is the entire discrepancy between the guessed and the
  true irrelevant ideal on that ring.

  `multigradedBlockData(R,blocks)` takes the partition, requires it to be
  exact (one nonempty block per degree component, every variable once, all of
  them variables of `R`) and rejects it otherwise; ordering is not used, since
  the ideal is the symmetric product of the block ideals. All eight entry
  points with `IrrelevantIdeal` take `VariableBlocks` too, resolved in one
  shared `irrelevantIdealDataInternal` which also decides the geometric
  dimension -- replacing the same ten lines repeated in three of them.
  Precedence is blocks, then an ideal, then the gated heuristic; supplying
  blocks and an ideal together is refused rather than silently ranked.

  `IrrelevantIdeal` keeps working and is now the secondary entrance: an ideal
  cannot leave the ring it lives in, whereas blocks are a property of the
  variables. Verified on that ring: the named blocks give exactly the
  provenance ideal, and an entry point reaches the same verdict as when handed
  the ideal by hand.
- The line between the paper and this package's extension of it is drawn where
  the two run out. Section 3 opens "Let `X = Proj R` be a normal monograded
  variety", and a bigraded input reaches it through Section 2.3's
  `w`-diagonal, which is monograded again; the multigraded entry points here
  are an extension, added because that diagonal blows the presentation up in
  practice, and they are the data-returning methods only.

  `isCanonicalNef` and `canonicalNefThreshold` are the paper's algorithms as
  stated, and they inherit `IrrelevantIdeal` and `VariableBlocks` through
  `options canonicalNefData` / `options canonicalNefThresholdData` without
  being able to use either: neither has an overload taking `H`, and both drop
  the options when forwarding. They used to drop them in silence, which sent a
  multigraded ring into the monograded dimension test `dim R - 1` and reported
  "expected a projective threefold" about a ring whose geometric dimension is
  3. They now refuse the options and name the data-returning method to use
  instead. The alternative -- giving the wrappers multigraded overloads too --
  was weighed and declined: keeping the extension on the data methods is the
  clearer line.

## Outstanding

### 1. The mixed MMP step has no example and is untested

`mmpStepRecordData` labels a birational step from two independent facts: whether
the relative canonical model `g` is the identity, and whether the *contraction*
`f` is small.

| `stepType` | `g` | `f` |
| --- | --- | --- |
| `divisorial` | identity | -- |
| `flipping` | nontrivial | small |
| `mixed` | nontrivial | not small |

`mixed` is the case Lemma 6.9 (`lem:mixed-step`) is stated for: `f` contracts a
divisor while `g` is still a nontrivial small model, which can happen when the
source is not Q-factorial. It has no worked example. `tests/relative-model.m2`
produces the label by passing `ContractionIsSmall => false` to a model whose
contraction is in fact small, so the real path -- a genuinely non-small `f`
reaching a nontrivial `g` -- has never run.

What is needed is an example, not an implementation: the classification code
already handles the case, and `contractionSmallnessData` already decides `f`'s
smallness. Finding a threefold whose extremal contraction is non-small while
its relative canonical model is nontrivial is the work.

**This replaces an item that claimed divisorial relative canonical models were
unimplemented.** That was a misreading. `g` is always small or the identity,
and the paper proves it rather than assuming it:

- Proposition 6.8's termination argument shows that for a sufficiently
  divisible `m` the candidate is `Proj` of the relative canonical algebra
  itself, so "such an `m` passes both tests".
- Corollary 6.10's proof then uses "the morphism `g` is small" as an
  established consequence of Proposition 6.8.
- Smallness is part of the definition of an MMP step in both frameworks the
  paper cites (Kollár's Definition 1, Hashizume's Definition 3.5).
- The identity is the Q-Gorenstein case: "If the target is Q-Gorenstein, its
  relative canonical model is the target itself."

The word "divisorial" appears once in `AlgoMMP.tex`, in "reflexive divisorial
sheaf"; there is no notion of a divisorial relative canonical model to
implement. Two consequences of the correction: accepting only the identity or a
small projection is the theorem rather than a limitation, and the old claim
that raising `MaxMultiplier` "cannot help" was wrong -- it is exactly what
helps, since the search enumerates `m = 1, 2, 3, ...` and will reach a
sufficiently divisible one. `relativeCanonicalModelFromBaseData`'s comment and
its user-visible `warning` string carried the same misreading and now say this.

### 2. Repository visibility

`SteinFactorizationM2` is public. `Coding_MMP` and `flip-computation` are
still private and are to be made public when the revision appears on arXiv.
Both have been checked for secrets and local absolute paths, and their
histories rewritten where such paths appeared.
