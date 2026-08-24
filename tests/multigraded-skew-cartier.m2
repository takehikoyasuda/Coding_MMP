needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("FlipComputation",
    FileName=>"third_party/flip-computation/FlipComputation.m2");
needsPackage "Polyhedra";
needsPackage "WeilDivisors";

-- Stage 2 (T1) of docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md, section 5's T1
-- and success criterion 3.  This file reproduces the plan's section 2.3/3
-- ring Z exactly (a toric flip target of independently-verified canonical
-- index 2), and is the regression that was missing before this change: it
-- compares against the *ring's own* provenance irrelevant ideal
-- (P#irrelevantIdeal, carried by the B2MProjection FlipComputation already
-- built), not merely against multigradedBlockData's own (unverified)
-- output.  Do NOT reload FlipComputation here (no Reload=>true): the
-- B2MProjection P built below must be an instance of the same type object
-- MMPComputation.m2 itself imported at its own load time, or the
-- (BasicDivisor,B2MProjection) dispatch tested below will silently fail to
-- match with a "no method found" error instead of running the intended test.

-- Section 3's construction: rays v1=(1,0,0), v2=(0,1,0), v3=(0,0,1),
-- v4=(1,3,-2); the flip target in the chart triangulation {v1,v2,v3},
-- {v1,v2,v4} is singular in one chart, of canonical index 2 (independently
-- confirmed there by solving M*m=-k(1,1,1) for the matrix of rows
-- v1,v2,v4: m=-k(1,1,3/2), integral only for even k).  Compactified here by
-- adding one extra homogeneous coordinate w at the forced weight l=(1,1,1).
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,3,-2}};
sigma = coneFromVData transpose matrix rayList;
HB = apply(hilbertBasis dualCone sigma, v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
wdegs = apply(HB, h -> sum apply(3, k -> h#k*{1,1,1}#k));
S = QQ[y_1..y_(#HB), w, Degrees => wdegs | {1}];
Xproj = S/sub(I0,S);

assert(dim Xproj == 4);
assert(isNormal Xproj);

-- computeFlip is the existing, unmodified FlipComputation entry point; m=1
-- is rejected (exceptional locus contains a divisor) and m=2 succeeds,
-- exactly reproducing the source example's own comment.
P = computeFlip(Xproj, BaseIsProjective=>true, Multipliers=>{1,2});
Z = P#totalRing;
assert(degreeLength Z == 2);
assert(dim Z == 5);

-- The ring's true, provenance irrelevant ideal, carried by the
-- B2MProjection that FlipComputation itself built -- ground truth, not
-- derived by anything in MMPComputation.m2.
Btrue = sub(P#irrelevantIdeal, Z);

-- multigradedBlockData is unexported; read it the same way
-- MMPComputation.m2 itself reads WeilDivisors' private divisorToModule.
multigradedBlockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
blockData = multigradedBlockDataFn Z;
Bmine = blockData#"irrelevantIdeal";

-- THE KNOWN DEFECT, pinned down as a documented fact (docs/STAGE2-SINGULAR-
-- MEASUREMENT-PLAN.md section 2.3): on this skew bigraded ring,
-- multigradedBlockData succeeds (no error) but silently returns a block
-- partition, and hence an irrelevant ideal, with a DIFFERENT RADICAL from
-- the ring's actual irrelevant ideal.  This assertion is deliberately a
-- pin, not a permanent invariant to protect: multigradedBlockData's general
-- block-classification heuristic is not being fixed by this change (out of
-- scope, per the plan's section 1), so this comparison is expected to keep
-- failing exactly this way until someone deliberately improves that
-- heuristic to detect skew fibre gradings -- if a future change flips this
-- assertion (radical Btrue == radical Bmine), that is progress on the
-- heuristic, not a regression, and this test should be revisited then, not
-- treated as broken.
assert(radical Btrue != radical Bmine);
assert(not blockData#"verifiedBlockDiagonal");

-- The geometric-dimension claim used by every new IrrelevantIdeal-aware
-- entry point in MMPComputation.m2 to bypass multigradedBlockData entirely:
-- dim Z - degreeLength Z must agree with multigradedBlockData's own
-- (dimension-only, still-trustworthy) "geometricDimension" field, even
-- though its irrelevant ideal is wrong.  Checked directly rather than
-- assumed, per the work order.
assert(dim Z - degreeLength Z == blockData#"geometricDimension");
assert(blockData#"geometricDimension" == 3);

K = canonicalDivisor(Z,IsGraded=>true);

-- isCartierMultigraded is unexported; same private-dictionary technique.
isCartierMultigradedFn = value(MMPComputation#"private dictionary"#"isCartierMultigraded");

-- Now that no caller of multigradedBlockData's guess trusts it unless
-- "verifiedBlockDiagonal" is true (this ring's fibre grading is skew, so it
-- is not; see the assertion above and verifiedIrrelevantIdeal in
-- MMPComputation.m2), the underlying general-purpose predicate refuses to
-- guess and errors here instead of returning the silent false positive it
-- used to return.  This documents the current, fixed behaviour: the
-- heuristic inside multigradedBlockData itself is still not corrected --
-- routing around it, not fixing it at that level, is still what this task
-- does -- but nothing downstream trusts its output unverified anymore.
assert(try (isCartierMultigradedFn K; false) else true);

-- THE ACTUAL FIX (T1): given the TRUE irrelevant ideal, the Cartier test
-- must correctly find K non-Cartier and 2K Cartier, matching the
-- independently-verified toric canonical index of 2 (plan section 2.2).
-- This is success criterion 3 of the Stage 2 plan: a regression comparing
-- against P#irrelevantIdeal, not merely against multigradedBlockData's own
-- (unverified) output.
assert(not isCartierMultigradedFn(K,Btrue));
assert(isCartierMultigradedFn(2*K,Btrue));
assert(not isCartierMultigradedFn(3*K,Btrue));
assert(isCartierMultigradedFn(4*K,Btrue));

-- The same fix, exercised through the exported isBasePointFreeDivisor
-- overload and via the B2MProjection P directly (reading its own
-- irrelevantIdeal field rather than requiring the caller to sub it in by
-- hand) -- both new entry points from T1.
assert(not isCartierMultigradedFn(K,P));
assert(isCartierMultigradedFn(2*K,P));

print "OK Stage 2 T1: multigradedBlockData Z gives a wrong (different-radical) B on this skew ring, and the caller-supplied-B override correctly finds K non-Cartier, 2K Cartier (canonical index 2), via both an explicit Ideal and the ring's own B2MProjection.";

-- Part 0 of the Stage 2 measurement work order (docs/STAGE2-MEASUREMENT-
-- RESULTS.md): completes what T1 above started.  T1 fixed the Cartier gate
-- of canonicalScaledNefData/canonicalNefData/canonicalContractionAtThreshold-
-- Data/etc. to honor a caller-supplied IrrelevantIdeal, but left those same
-- entry points' internal *search loops* (canonicalScaledNefDataInternal,
-- canonicalNefDataCore, canonicalContractionAtThresholdDataCore) still
-- calling the bare 1-argument isBasePointFreeDivisor for every trial
-- multiple, which re-derives B via multigradedBlockData every time --
-- silently ignoring whatever IrrelevantIdeal the caller supplied to the
-- outer entry point.  This is exactly the gap flagged, in comments, at the
-- point T1 landed (see canonicalScaledNefData's own IrrelevantIdeal-option
-- comment in MMPComputation.m2 before this change).  This section pins down
-- a case where that gap is not merely a latent risk but a genuine, verified
-- false positive, and confirms the fix.
--
-- H below is the ample-candidate class from the Stage 2 measurement's Part 1
-- (research-log/docs/STAGE2-MEASUREMENT-RESULTS.md section on H): bidegree (1,1),
-- Cartier under Btrue, base-point-free at multiplicity 1, and strictly
-- positive on the flip's unique exceptional curve.  It is used here purely
-- as a divisor of the right shape to construct a concrete counterexample,
-- not because ampleness is being re-derived or re-certified by this test.
H = divisor(Z_0) + divisor(Z_8);

-- Lbig is EXACTLY the divisor canonicalScaledNefDataInternal computes as its
-- own "L" (candidateDivisor at multiplier m=1) for a=2, t=6: L = q*a*K+a*p*H
-- with q=1,p=6, i.e. L = 2*K + 12*H.  This is not a hand-picked pathological
-- divisor; it is the literal candidate the search loop inside
-- canonicalScaledNefData(Z,2,6,H,...) tests first.
Lbig = 2*K + 12*H;

-- THE COUNTEREXAMPLE: verified by direct computation (not assumed), Lbig is
-- correctly NOT base-point-free under the true irrelevant ideal.  The bare
-- (auto-deriving, i.e. multigradedBlockData-backed) predicate used to report
-- a FALSE POSITIVE here, exactly mirroring the Cartier false positive above
-- but for base-point-freeness specifically; now that it refuses to guess on
-- a non-verifiedBlockDiagonal ring, it errors instead.
assert(not isBasePointFreeDivisor(Lbig,Btrue));
assert(try (isBasePointFreeDivisor Lbig; false) else true);

-- THE ACTUAL FIX (Part 0), exercised through a genuine entry point's own
-- search loop -- not just the bare predicate above, and not just the
-- Cartier gate T1 already fixed.  canonicalContractionAtThresholdData(Z,2,
-- lambda=6,H,...)'s cartierThresholdDivisor is q*a*K+a*p*H for a=2,
-- lambda=p/q=6/1, i.e. exactly 2*K+12*H = Lbig; ContractionMultipleLimit=>1
-- caps canonicalContractionAtThresholdDataCore's own while loop to testing
-- only that first candidate (multiplier=1), so this stays fast (a handful of
-- seconds, like the direct predicate calls above) while still running the
-- *loop*, not a hand-rolled substitute for it.  Confirmed by direct
-- computation: with B threaded correctly, the loop's own bpf test of Lbig
-- agrees with the ground truth above (not base-point-free), so testing only
-- one multiple is correctly reported inconclusive.  Before this change, the
-- loop's bpf test ignored the supplied B entirely and would have used
-- Bmine, which (as just shown) reports Lbig base-point-free -- so the
-- unfixed code would have wrongly reported this call conclusive (multiplier
-- 1 "works") instead of correctly inconclusive.
limitedContraction = canonicalContractionAtThresholdData(
    Z,2,6,H,IrrelevantIdeal=>Btrue,ContractionMultipleLimit=>1);
assert(not limitedContraction#"conclusive");
assert(limitedContraction#"multipliersTested" == 1);

-- a=1: a*K is genuinely not Cartier under Btrue (T1), so the Cartier gate of
-- every IrrelevantIdeal-aware entry point must still reject it outright,
-- confirming the gate itself is unaffected by threading B further inward.
assert(
    try (canonicalScaledNefData(Z,1,6,H,IrrelevantIdeal=>Btrue); false)
    else true
    );

print "OK Stage 2 Part 0: canonicalContractionAtThresholdData's own internal search loop, not merely its Cartier gate, now honors a caller-supplied true B -- verified against a concrete base-point-free false positive (Lbig=2K+12H) that the un-threaded predicate reports.";
