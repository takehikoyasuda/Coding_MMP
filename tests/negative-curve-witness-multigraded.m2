needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- Iterated multigrading, Phase 4 idea (research-log/docs/ITERATED-MULTIGRADING-MMP-PLAN.md):
-- negativeCurveWitnessData generalizes the package's unexported
-- negativeBaseLocusCurveData (monograded-only: it requires degreeLength
-- ambient R == 1) to genuinely multigraded presentations, using
-- hilbertFunction at the multidegree n*h (h the caller's ample class's own
-- multidegree) rather than single-graded regularity.  This is a candidate
-- cheaper alternative to isBasePointFreeDivisor's weilDivisorToModule-based
-- test for the "prove K+tH is not nef" search inside
-- canonicalScaledNefDataInternal (not yet wired in; this file tests the
-- standalone function only).

weilDivisorsPkg = needsPackage "WeilDivisors";
weilDivisorToModule = value(
    weilDivisorsPkg#"private dictionary"#"divisorToModule");

-- Bigraded P1xP2: K=O(-2,-3), H=O(1,1).
S = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
H = divisor(s) + divisor(u);
K = canonicalDivisor(S,IsGraded=>true);
h = {1,1};
B = ideal(s,t) * ideal(u,v,w1);
zeroDegree = toList(degreeLength S : 0);
candidateBaseLocus = D -> trim ann coker basis(zeroDegree,weilDivisorToModule D);

-- L = K+2H = O(0,-1): no sections at all, a known non-nef divisor (also used
-- in isBasePointFreeDivisorInternal's own defect-diagnosis comment).  The
-- witness curve is {pt in P1} x {line in P2}, on which O(0,-1) restricts to
-- O_{P1}(-1).
L = K + 2*H;
witnessL = negativeCurveWitnessData(L,candidateBaseLocus L,B,h);
assert(witnessL =!= null);
assert(witnessL#"intersection" == -1);
assert(dim(S/(witnessL#"curveIdeal")) - degreeLength S == 1);

print "OK negativeCurveWitnessData: K+2H=O(0,-1) on P1xP2 gives a genuine -1 witness curve.";

-- No false positives: two known base-point-free (hence nef) divisors must
-- both give null, not a spurious negative witness.
witnessH = negativeCurveWitnessData(H,candidateBaseLocus H,B,h);
assert(witnessH === null);

M = K + 3*H;  -- O(1,0): base-point-free, the projection to P1.
witnessM = negativeCurveWitnessData(M,candidateBaseLocus M,B,h);
assert(witnessM === null);

print "OK negativeCurveWitnessData: two base-point-free divisors give no witness (no false positive).";

-- Option and argument gates.
assert(try (negativeCurveWitnessData(L,candidateBaseLocus L,B,{1,1,1}); false) else true);
assert(try (negativeCurveWitnessData(L,candidateBaseLocus L,B,h,
    NegativeCurveSearchLimit=>0); false) else true);
P3 = QQ[y0,y1,y2,y3];
assert(try (negativeCurveWitnessData(L,ideal(0_P3),B,h); false) else true);

print "OK negativeCurveWitnessData: dimension and ring-mismatch gates reject bad input.";
