# Worked examples

The minimal model programs these packages run to completion, kept as real
Macaulay2 sessions and published at
<https://takehikoyasuda.github.io/Coding_MMP/examples.html>.

| File | What it computes |
| --- | --- |
| `01-projective-space.m2` | `P3`: `K` non-nef, nef threshold `4`, contraction to a point, one-step MMP |
| `02-quintic.m2` | smooth quintic threefold: `K=0` certified nef, minimal model in zero steps |
| `03-segre-fibration.m2` | Segre `P1xP2`: `K+3H=O(1,0)` gives the fibre-type contraction to `P1` |
| `04-disconnected-fibres.m2` | `P1xP2 -> P1` through the squaring map: a Stein factorization whose finite part has degree 2 |
| `05-blowup-of-a-line.m2` | `Bl_L(P3)`: Stein factorization, divisorial (codimension 1) against the ODP small resolution (codimension 2), then `Bl_L(P3) -> P3 -> point` |
| `06-toric-flip.m2` | toric circuit target: relative canonical model is a flip, with a certified inverse rational map |

## Scope

Section 3 of the paper opens with a monograded `X = Proj R`, and a bigraded
ring appears in it only as the graph of a morphism.  Every example here stays
inside that setting: the varieties are monograded, and the bigraded rings are
graphs of morphisms.  The package's multigraded entry points, which take a
multigraded variety directly, are an extension beyond the paper (see
`docs/PAPER-SYNC.md`), and this page does not use them.

## How the page is produced

`run.sh` feeds each `.m2` file to Macaulay2 on standard input, so Macaulay2
echoes it the way it echoes an interactive session; the result is written to
`.out` beside it, and the wall time to `.time`.  `build-page.py` then
substitutes those into `page.template.html`, which holds the prose.  Nothing on
the published page is transcribed by hand, so it cannot quote output Macaulay2
no longer produces.

```sh
make examples        # re-run all six and rewrite every .out and .time
make examples-page   # build ./preview/examples.html and look at it
make site            # the whole published site, manual included, into ./site
```

Open the preview rather than a bare page in the repository root: the page links
`Style/doc.css` and `Style/katex` relatively, the way the site serves them, so
without that directory beside it there is no stylesheet and the mathematics
stays as raw TeX.  `make examples-page` copies Macaulay2's `Style` tree into
`preview/` for exactly that reason.

### The markers in the template

```
@@session <name> | <expr> ; <expr> ; ...
@@seconds <name>@@
@@sourcelines <name>@@
```

`session` folds the whole transcript into a `<details>` element and puts the
value of each `<expr>` on the fold, so the results stay visible while the
session itself is one click away.  The values are looked up in the transcript
by matching the expression against what Macaulay2 echoed, never written out
here, and the build stops if an expression is missing from the session or if
Macaulay2 renders its value over several lines -- `nefTest#"witnessT"` prints
`1/2` as a three-line fraction, and half a fraction on a chip would be worse
than no chip.

Or one at a time, from the repository root:

```sh
examples/run.sh examples/06-toric-flip.m2
```

## Two things to know before editing an example

The scripts are read by Macaulay2 as interactive input, which differs from
`load` in two ways that have already produced silent breakage:

- **`i1`, `o1`, `i2`, `o2`, ... are bound** to the session's own inputs and
  outputs.  A ring `QQ[o0,o1,o2]` therefore does not have the variables it
  looks like it has.  Avoid those names.
- **A line that is already a complete expression is evaluated at once.**  A
  continuation such as a leading `==` on the next line is then a fresh
  statement, and a syntax error.  Break lines only where the expression so far
  is incomplete.
- **Many plain names are already taken.**  `graphIdeal`, `sourceRing`, `step`,
  `target`, `source` and `ring` are protected symbols of Macaulay2 or of the
  three loaded packages, and assigning to one is an error.  To check a script
  before running it, compare the names it assigns against
  `keys P.Dictionary` for every `P` in `loadedPackages`.

`build-page.py` refuses to build the page if any transcript contains a
Macaulay2 error, which catches all of these.  It also caught: a step record holds
its smallness verdict under `"contractionSmallnessData"`, not at the top level,
so `divisorialStep#"exceptionalCodimension"` is a missing key rather than the
codimension.

## Relation to the test suite

The examples cover the same ground as `tests/nefness.m2`,
`tests/contraction.m2`, and `tests/relative-model.m2`, which assert the values
shown here and run in `make test-core`.

CI re-runs `examples/run.sh` on every push before it rebuilds the page, so the
published page always shows what the current sources produce.  The committed
`.out` files are there to be read in a checkout, and to make a change in the
output visible in a diff.  Refresh them with `make examples` when you change
anything the examples exercise.
