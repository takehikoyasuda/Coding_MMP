-- Cross-check docs/COMPACT-TORIC-FLIP-FAN-CONSTRUCTION-REPORT.md's purely
-- combinatorial (isNef/NormalToricVarieties) conclusion against this
-- project's own general algorithm (canonicalNefData/canonicalContractionData),
-- now that the canonical-ideal/class-degree BPF fastpath is in place.  That
-- report explicitly left this cross-check undone ("not cross-checked in this
-- report").
--
-- Chamber A and chamber B (the pre-/post-flip small resolutions of the
-- non-Gorenstein circuit v1+v2=2v3+v4) share the SAME 5-variable Cox ring
-- (rank-2 grading); they differ only in irrelevant ideal (Stanley-Reisner
-- ideal of the two triangulations).  This is exactly the VGIT/wall-crossing
-- picture, and every support prime here is a single Cox variable -- the ideal
-- case for the new fastpath.
--
-- This script tests chamber B specifically: doc found K non-nef there too,
-- and identified its non-fibre-type (divisorial) contraction landing on the
-- shared singular non-Q-factorial base W.  It deliberately stops right after
-- that one step (does not call canonicalIndexData on the resulting ring):
-- scripts/cyclic-cover-raw-driver-probe.m2 already showed that a raw
-- canonicalIndexData/isCartier call on a *different*, monograded, birational
-- next-ring can itself take 30+ minutes -- a separate, not-yet-fixed
-- bottleneck this script does not re-trigger.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");
needsPackage("NormalToricVarieties");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

-- Combinatorial ground truth first (fast, exact; from the report).
rayList = {{1,0,0},{0,1,0},{0,0,1},{-1,-1,1},{1,1,-2}};
outerCones = {{0,2,3},{0,3,4},{1,2,3},{1,3,4}};
XB = normalToricVariety(rayList, outerCones | {{0,1,2},{0,1,4}});
assert(isWellDefined XB and isComplete XB);
assert(not isNef toricDivisor XB);
H12toric = toricDivisor({0,0,0,1,2},XB);
assert(isAmple H12toric);
assert(isCartier H12toric);
assert(isCartier(2*toricDivisor XB));
assert(not isCartier(toricDivisor XB));
stamp("toric ground truth confirmed (chamber B: nef=false, index=2, H=(1,2) ample+Cartier)");

-- Same data as this project's own multigraded Cox-ring presentation.
R = QQ[x_0..x_4, Degrees=>{{1,-1},{1,-1},{-1,2},{1,0},{0,1}}];
BB = ideal(x_3*x_4, x_2*x_3, x_1*x_4, x_1*x_2, x_0*x_4, x_0*x_2);
stamp("R, BB constructed");

isCartierSaturatedInternalFn = value(
    MMPComputation#"private dictionary"#"isCartierSaturatedInternal");

K = canonicalDivisor(R,IsGraded=>true);
print("K=" | toString K);
H = divisor(x_3) + 2*divisor(x_4);
print("H=" | toString H);
stamp("K, H constructed");

-- KNOWN BUG (found in this session): isCartierSaturatedInternal delegates to
-- WeilDivisors' nonCartierLocus(D,IsGraded=>true), which hard-wires an
-- internal saturation by getIrrelevantIdeal(R) -- WeilDivisors' own generic
-- "variables of positive degree" rule -- BEFORE isCartierSaturatedInternal
-- ever gets to re-saturate by the caller-supplied B.  On this ring,
-- getIrrelevantIdeal(R) wrongly excludes x_2 (its degree (-1,2) fails the
-- naive entrywise-positive test), silently destroying the genuine
-- obstruction.  Both calls below therefore return the WRONG answer (true)
-- and are recorded as known-unreliable rather than asserted on.
print("isCartierSaturatedInternal(K,BB) [KNOWN UNRELIABLE, see comment]=" |
    toString isCartierSaturatedInternalFn(K,BB));
print("isCartierSaturatedInternal(2*K,BB) [KNOWN UNRELIABLE, see comment]=" |
    toString isCartierSaturatedInternalFn(2*K,BB));
print("getIrrelevantIdeal(R) [WeilDivisors' own, generic, wrong for this ring]=" |
    toString ((value(WeilDivisors#"private dictionary"#"getIrrelevantIdeal")) R));
-- H does not involve x_2 in its support, and is independently confirmed
-- ample+Cartier via NormalToricVarieties' isAmple/isCartier above, so this
-- one assertion is cross-validated rather than solely trusted.
assert(isCartierSaturatedInternalFn(H,BB));
stamp("H's Cartier-ness cross-checked (K's own check is known-unreliable here)");

-- The canonical index (a=2) is therefore taken directly from the
-- independently-verified toric ground truth above, NOT from
-- canonicalIndexData/isCartier (which would also inherit this bug).

nefData = canonicalNefData(R,2,H,IrrelevantIdeal=>BB);
print("nefData#conclusive=" | toString nefData#"conclusive");
print("nefData#nef=" | toString nefData#"nef");
stamp("canonicalNefData(R,2,H,BB) done");
assert(nefData#"conclusive");
assert(not nefData#"nef");

contraction = canonicalContractionData(R,2,H,IrrelevantIdeal=>BB,
    ThresholdSearchLimit=>20, ContractionMultipleLimit=>20);
print("contraction#conclusive=" | toString contraction#"conclusive");
stamp("canonicalContractionData(R,2,H,BB) done");
assert(contraction#"conclusive");
print("contraction#isFibreType=" | toString contraction#"isFibreType");
print("contraction#threshold=" | toString contraction#"threshold");
print("contraction#sourceDimension=" | toString contraction#"sourceDimension");
print("contraction#targetDimension=" | toString contraction#"targetDimension");

if contraction#"isFibreType" then (
    print("UNEXPECTED: contraction is fibre type; the report predicted divisorial.");
    ) else (
    model = relativeCanonicalModelData(contraction,
        RelativeCanonicalMultipliers=>{1,2});
    stamp("relativeCanonicalModelData done");
    print("model#conclusive=" | toString model#"conclusive");
    print("model#isIdentity=" | toString model#"isIdentity");
    record = mmpStepRecordData(contraction,model);
    stamp("mmpStepRecordData done");
    print("record#stepType=" | toString record#"stepType");
    nextRing = record#"nextRing";
    print("nextRing numgens ambient=" | toString numgens ambient nextRing);
    print("nextRing dim=" | toString dim nextRing);
    print("nextRing degreeLength=" | toString degreeLength nextRing);
    );
flush stdio;
