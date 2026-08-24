# MMP computation in Macaulay2

Macaulay2 implementation project for the algorithms in Takehiko Yasuda,
*An algorithm for the minimal model program in dimension three*.

This repository is the integration layer. It pins the two existing prototype
implementations as Git submodules, and contains the remaining algorithms and
the top-level MMP driver. The paper itself is available on arXiv
([arXiv:2603.13703](https://arxiv.org/abs/2603.13703)) and is not part of this
repository. Numbered results are cited by their v3 numbering; earlier versions
number some of them differently.

## Checkout

```sh
git clone --recurse-submodules <repository-url>
cd Coding_MMP
make test-upstreams
```

For an existing checkout:

```sh
git submodule update --init --recursive
```

The current development environment uses Macaulay2 1.26.06.

## Repository layout

| Path | Role |
| --- | --- |
| `third_party/SteinFactorizationM2` | bigraded Hom and Stein-factorization prototype |
| `third_party/flip-computation` | relative canonical model / flip prototype |
| `MMPComputation.m2` | integration package for nefness and contraction algorithms |
| `tests/` | integration-layer regression tests |
| `docs/IMPLEMENTATION-STATUS.md` | trusted scope, known failures, and paper-to-code map |
| `docs/ROADMAP.md` | implementation order for the full MMP |
| `docs/PAPER-SYNC.md` | what the paper's revision changed, what has been followed, and what is outstanding |
| `scripts/test-upstreams.sh` | reproducible baseline test runner |
| [`research-log/`](research-log/README.md) | archived cost measurements, root-cause investigations, and negative results from performance work; not required reading to use the package |

## Stein graph status

The Stein development branch now implements the graph construction in the
paper as the kernel of

```text
B tensor C^[k]  -->  R_gamma.
```

The output ring contains the source and Stein coordinates, but not the original
target coordinates. New dimension regressions detect the extra scaling
parameter produced by the old construction. See `docs/IMPLEMENTATION-STATUS.md`
for the verification scope and remaining review items.

## MMP integration package

The integration API is implemented in `MMPComputation.m2`.  In most cases,
start with the top-level driver:

```m2
needsPackage("MMPComputation", FileName => "MMPComputation.m2");
R = QQ[x0,x1,x2,x3];
result = threefoldMMPData(R,1);
result#"terminationType"
```

Here `R` is the homogeneous coordinate ring of the projective threefold and
`1` means that `K_X` itself is Cartier.  More generally, the second argument
is a known positive integer `a` such that `a*K_X` is Cartier.  If it is not
known, compute it with `canonicalIndexData R` first.

The lower-level entry points are useful when only one stage is needed or when
inspecting an intermediate certificate:

```m2
needsPackage("MMPComputation", FileName => "MMPComputation.m2");
result = canonicalNefData(R, a)
answer = isCanonicalNef(R, a)
thresholdData = canonicalNefThresholdData(R, a)
lambda = canonicalNefThreshold(R, a)
contraction = canonicalContractionData(R, a)
```

Choose an entry point by the answer you need:

| Question | Function | Result to read |
| --- | --- | --- |
| Run the complete program | `threefoldMMPData(R,a)` | `result#"terminationType"` and `result#"numberOfSteps"` |
| Is `K_X` nef? | `isCanonicalNef(R,a)` | a Boolean |
| What is the nef threshold? | `canonicalNefThreshold(R,a)` | a rational number; call only after `K_X` is known not to be nef |
| What is the Cartier index? | `canonicalIndexData R` | `result#"index"` |
| How was an answer certified? | the corresponding function ending in `Data` | the returned `HashTable` fields |

As a naming convention, functions ending in `Data` expose detailed
intermediate objects and certificates.  They are mainly for diagnosis and
mathematical inspection; the shorter functions are the clearer starting
point.

These functions assume that `R` presents a normal log terminal projective
threefold.  They do not verify normality or log terminality.  The
implementation follows the paper's parallel search using reflexive
pluricanonical divisors and effective base-point-free tests of positive
perturbations.  When the canonical divisor is not nef, the threshold API
implements the paper's dyadic bracketing and finite rational candidate search.
The contraction API constructs the complete-linear-system graph at the
threshold and computes its connected-fibre part with Stein factorization.  Its
result records source and target dimensions, dimension drop, and whether the
contraction is birational or of fibre type.  All public contraction and
relative-model graphs use the common `GraphMorphism` representation;
`mmpGraphMorphism` adapts legacy integration or Stein graph tables.
For a birational result, `relativeCanonicalModelData(contraction)` computes the
next model over the contraction target, using the identity model when the
canonical algebra is already trivial and `FlipComputation` otherwise.
`relativeCanonicalModelIsomorphismData(model)` records whether that model is
the identity, certified by the locally-free locus of its blow-up ideal.
`mmpStepRecordData` retains both morphism graphs and records fibre, divisorial,
flipping, or mixed step metadata.  The original contraction's smallness is
computed from the codimension of the support of the second exterior power of
relative differentials; an explicit certificate can also be supplied.  The
[smallness criterion](docs/SMALLNESS-CRITERION.md) records its assumptions,
justification, and independent regressions.
For a nonidentity relative model,
`relativeModelInverseRationalMapData(model)` gives explicit homogeneous
coordinates for the rational inverse of its projection, and certifies them
against both the model and graph equations and the Rees-center base locus.
When Rees generators have different weighted degrees, `b2mDiagonalData`
chooses an interior integral diagonal and converts the skew fibre grading to
positive weights before constructing the same graph and inverse certificates.
The end-to-end entry point is `threefoldMMPData(R,a)`.  It returns the recorded
graph sequence and terminates at either a minimal model or a K-negative
fibration.
`threefoldMMPData(R,a,steps)` resumes from a current model while preserving an
independently certified nonterminal prefix, which is useful for long computed
birational steps and checkpointed runs.

Every top-level result has a Boolean `"conclusive"` field.  If it is `true`,
read `"terminationType"` (`"minimal model"` or `"K-negative fibration"`) and
`"steps"`.  If it is `false`, `"phase"` identifies the bounded search that
stopped; the partial data and completed steps are retained in the result.

The package does not compute the relative Picard number.  The fibration result
certifies a connected-fibre morphism to a lower-dimensional target for which
`-K_X` is relatively ample, but makes no relative-Picard-number-one claim.

## Documentation

`MMPComputation.m2` carries a standard Macaulay2 package manual (`doc ///...///`
blocks after `beginDocumentation()`) describing each public function's usage,
inputs, and outputs, with runnable examples for the top-level API. Build and
browse it with

```sh
make install
```

The install target installs the pinned `SteinFactorization` and
`FlipComputation` dependencies before installing `MMPComputation`; this is
required because documentation examples are checked in fresh Macaulay2
processes whose working directory is not the repository.  Then browse the
manual in Macaulay2 with

```m2
needsPackage "MMPComputation";
viewHelp "MMPComputation";
```

`installPackage` also runs and validates every documented example as part of
building the manual.

Regression tests in `tests/` are run with `make test-core`; a separate slow
capstone test (a two-step MMP computed end to end, `~15` minutes of cpu time)
is run on demand with `make test-slow`.

## Use of AI

The integration-layer code, tests, and documentation in this repository were
written essentially by an AI system (Claude), with edits by the author.
ChatGPT was also used during development, mainly for design and algorithm
discussion.  The author has read the AI-written material and believes it to be
correct, but has not checked every detail.  The underlying algorithms are the ones in the paper
above, and each one added here is checked against the regression suite in
`tests/`, so large errors are unlikely, but this is a research prototype, not
verified software.

## License

This repository's integration-layer code (`MMPComputation.m2`, `tests/`,
`scripts/`, `research-log/`) is dedicated to the public domain under CC0 1.0,
the same license as both pinned implementation submodules; see
[LICENSE](LICENSE).
