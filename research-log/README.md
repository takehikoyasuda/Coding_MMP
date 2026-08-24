# Research log

This directory is an archive of the experimentation trail behind
`MMPComputation.m2`: cost measurements, root-cause investigations, benchmark
reports, and design ideas that were tried and either adopted, refuted, or left
open. It is **not required reading to use the package** -- see the top-level
[README.md](../README.md) and [docs/](../docs/) for that. It exists so that
performance decisions and negative results are traceable rather than lost.

`docs/` holds the investigation reports and design notes; `scripts/` holds the
one-off `.m2` probe and profiling scripts they refer to. Neither is exercised
by `make test` or `make test-core`; they are not regression tests, and some
scripts take many minutes to run.

## What was adopted into `MMPComputation.m2`

- **`docs/BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md`,
  `docs/BPF-HOM-BOTTLENECK-ROOT-CAUSE-SUMMARY.md`**: root-caused the
  base-point-free (BPF) test's cost to `weilDivisorToModule` construction and
  `Hom(dualModule,R^1)`, not the ideal-saturation assessment step. This
  reframing drove every fastpath below.
- **`docs/CARTIER-INDEX-FASTPATH-AND-CYCLIC-COVER-INVESTIGATION.md`**: the
  canonical-ideal-seed / class-degree Cartier certificate, extended to
  `canonicalIndexData` and `isCartier`. Implemented.
- **`saturation_strategies.md`**: surveyed eight saturation-speedup strategies;
  none independently panned out, but the write-up motivated the
  `saturate(ann coker f) == saturate(image f)` identity below.
- The **`module-saturate-bypasses-ann-bottleneck`** result (no separate report
  file; see the commit "Bypass ann(coker) in basePointFreeModuleInternal via
  module saturate"): proved and implemented a ~4-6x speedup in
  `basePointFreeModuleInternal` by saturating the image of the evaluation map
  directly instead of materializing `ann(coker f)` first.
- **`docs/STEIN-FACTORIZATION-COST-EXPERIMENT-REPORT.md`**: root-caused
  `steinHomData`'s free-resolution blowup on `Bl_p(P3)`, then proved (not just
  measured) a resolution-length bound via `isNormal` + Zariski's Main Theorem,
  generalized to non-birational maps via an etale-fibre criterion. This
  workaround is what makes the `Bl_p(P3) -> P3 -> point` end-to-end MMP
  (`tests/bl-p-p3-two-step-mmp.m2`) possible at all.

## What was measured but not adopted (or is still open)

- **`docs/GFP-REDUCTION-BENCHMARK-REPORT.md`**: QQ -> GF(p) reduction gives a
  genuine ~2.3x constant-factor speedup on BPF checks, but is not lifted to a
  rigorous characteristic-0 certificate, so it is not wired into the package.
- **`docs/INVERTIBLE-IDEAL-CACHING-EXPERIMENT-REPORT.md`**: caching invertible
  ideals from Cartier multiples to avoid reflexive-hull recomputation is
  correct but 4-6x *slower* in practice. Not adopted.
- **`docs/CYCLIC-QUOTIENT-CHARACTER-EXPERIMENT-REPORT.md`**: the fastpath
  design notes' hypothesis that base-point-free section counts are tabulable
  by singularity type is false (they grow cubically on cyclic quotient
  singularities). Closes off that direction.
- **`docs/STAGE1-MEASUREMENT-PLAN.md` / `-RESULTS.md`,
  `docs/STAGE2-MEASUREMENT-RESULTS.md`**: the original staged benchmark plan
  for multigraded preservation (block structure, singular/skew-graded cases)
  and its results, precursor to the reports above.
- **`docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md`**: investigates Stage 1's
  multigraded machinery on a genuinely singular target where `K` is not
  Cartier. Found that `multigradedBlockData`'s block classification silently
  disagrees with the ring's true irrelevant ideal on a skew-graded ring,
  which makes the Stage 1 saturated Cartier test wrongly report `K` Cartier;
  proposes a task list and measurement protocol for the fix, not implemented
  here.
- **`docs/BOTTLENECKS-AND-MULTIGRADING.md`**: the original survey of
  monograded-flattening bottlenecks that motivated keeping presentations
  multigraded; superseded in detail by the reports above but kept as the
  original map of the problem.
- **`docs/ITERATED-MULTIGRADING-MMP-PLAN.md`**: plan for driving the MMP loop
  on a genuinely multigraded (not flattened) presentation across more than one
  iteration. Phase 1 (terminal branches only) is implemented and tested
  (`tests/multigraded-mmp-driver.m2`); later phases are open.
- **`docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md`,
  `docs/CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md`**: two different concrete
  routes tried toward a fully automated one-flip minimal-model example; the
  cyclic-cover route reached a hand-assembled example, but full automation on
  its natural multigraded presentation stalls (see the two reports above for
  why).
- **`docs/algorithmic_mmp_bpf_fastpath_notes.md`**: the original design notes
  for the whole BPF fastpath line of investigation; several of its later
  sections (7-17) are the ones closed off by the character experiment above.
- **`docs/SIMPLE-FLIP-NEF-TRACTABILITY-REPORT.md`,
  `docs/COMPACT-TORIC-FLIP-FAN-CONSTRUCTION-REPORT.md`**: exhaustive search
  (90+ configurations total) for a compact example whose flip target is
  actually nef, so an end-to-end flip example could be built. None found; the
  compactification method itself is suspected, not just the ray choice.
- **`docs/LOG-MMP-BOUNDARY-DIVISOR-DESIGN.md`**: design-only (unimplemented)
  proposal to handle the cyclic-cover construction directly as a log pair
  `(W,Delta)` instead of taking an actual cyclic cover, to sidestep the BPF
  cost above. Mathematically sound, small if pursued, but not built.

## `scripts/`

One-off probe and profiling scripts, mostly named after what they measure
(`*-bpf-probe.m2`, `*-cartier-probe.m2`, `*-driver-probe.m2`,
`*-profile.m2`). Each corresponds to a specific claim in one of the reports
above; none are meant to be run as regression tests, and several
(`toric-hypersurface-*`, `cyclic-cover-multigraded-*`) take from tens of
seconds to tens of minutes depending on the input size used at investigation
time.
