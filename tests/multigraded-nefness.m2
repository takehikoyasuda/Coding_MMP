needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- Stage 1 measurement plan (research-log/docs/STAGE1-MEASUREMENT-PLAN.md), T1-T5 and T4.
-- Exercises the public multigraded entry points only, on the two rank-2
-- inputs from plan section 5.1: Bl_p(P3) and Segre P1xP2.

-- Segre P1xP2: K=O(-2,-3), H=O(1,1), threshold lambda=3, K+3H=O(1,0)
-- gives the connected-fibre contraction to P1.
S = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
H = divisor(s) + divisor(u);

-- The unsaturated (pre-fix) predicate is wrong on this ring; the saturated
-- one, used throughout this package since T2, is not.
assert(trim baseLocus divisor(s) == ideal(s,t));
assert(isBasePointFreeDivisor divisor s);
K = canonicalDivisor(S,IsGraded=>true);
assert(isBasePointFreeDivisor(-K));

segreNef = canonicalNefData(S,1,H);
assert(segreNef#"conclusive");
assert(not segreNef#"nef");

segreThreshold = canonicalNefThresholdData(S,1,H);
assert(segreThreshold#"conclusive");
assert(segreThreshold#"threshold" == 3);

segreContraction = canonicalContractionAtThresholdData(S,1,3,H);
assert(segreContraction#"conclusive");
assert(segreContraction#"threshold" == 3);
assert(segreContraction#"multiplier" == 1);
assert(segreContraction#"sourceDimension" == 3);
assert(segreContraction#"targetDimension" == 1);
assert(segreContraction#"isFibreType");
assert(segreContraction#"steinFactorizationType" == "computed");
assert(instance(segreContraction#"contractionGraph",GraphMorphism));

print "OK Segre P1xP2 multigraded: threshold=3, contraction to P1.";

-- Bl_p(P3): the graph closure in P3 x P2, w=O(1,1).  isCartier(K,IsGraded=>
-- true) is known-wrong here (K is Cartier, this is a smooth variety); the
-- multigraded path must not rely on it.
Sb = QQ[x0,x1,x2,x3,u0,u1,u2,
    Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
R = Sb/minors(2, matrix{{x1,x2,x3},{u0,u1,u2}});
w = divisor(x0) + divisor(u0);
Kb = canonicalDivisor(R,IsGraded=>true);
assert(not isCartier(Kb,IsGraded=>true));
assert(isBasePointFreeDivisor w);

blpNef = canonicalNefData(R,1,w);
assert(blpNef#"conclusive");
assert(not blpNef#"nef");

blpThreshold = canonicalNefThresholdData(R,1,w);
assert(blpThreshold#"conclusive");
assert(blpThreshold#"threshold" == 2);

blpContraction = canonicalContractionAtThresholdData(R,1,2,w);
assert(blpContraction#"conclusive");
assert(blpContraction#"threshold" == 2);
assert(blpContraction#"multiplier" == 1);
assert(blpContraction#"sourceDimension" == 3);
assert(blpContraction#"targetDimension" == 0);
assert(blpContraction#"steinFactorizationType" == "trivial point target");

print "OK Bl_p(P3) multigraded: threshold=2, contraction to a point (K+2w is numerically trivial).";

-- T4: binary search must not move any existing threshold.
p3 = QQ[y0,y1,y2,y3];
p3Threshold = canonicalNefThresholdData(p3,1);
assert(p3Threshold#"conclusive");
assert(p3Threshold#"threshold" == 4);
assert(p3Threshold#"testsRun" <= p3Threshold#"linearTestsRunEquivalent");

print "OK T4: binary search still gives P3's threshold 4, with testsRun <= the linear-equivalent count.";
