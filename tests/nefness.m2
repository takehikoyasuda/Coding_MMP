needsPackage("MMPComputation",FileName=>"MMPComputation.m2");

-- The effective constants stated explicitly for threefolds in the paper.
assert(effectiveNefMultiplier(3,1) == 1920);
assert(effectiveNefMultiplier(3,2) == 1536);

-- P^3 has K=-4H, so K is not nef and K+4H=0 is nef.
R = QQ[x0,x1,x2,x3];
ample = weightedAmpleDivisorData R;
assert(ample#"weights" == {1,1,1,1});
assert(ample#"cartierDegree" == 1);
assert(isBasePointFreeDivisor ample#"divisor");
negative = canonicalNefData(R,1);
assert(negative#"conclusive");
assert(not negative#"nef");
assert(negative#"witnessType" == "non-nef positive perturbation");
assert(negative#"witnessT" == 1/2);
threshold = canonicalScaledNefData(R,1,4);
assert(threshold#"nef");
assert(threshold#"basePointFree");
thresholdData = canonicalNefThresholdData(R,1);
assert(thresholdData#"conclusive");
assert(thresholdData#"threshold" == 4);
assert(thresholdData#"lowerBound" < 4);
assert(thresholdData#"upperBound" >= 4);
assert(canonicalNefThreshold(R,1) == 4);
boundedThreshold = canonicalNefThresholdData(R,1,ThresholdSearchLimit=>1);
assert(not boundedThreshold#"conclusive");
assert(boundedThreshold#"phase" == "upper bound");
pointContraction = canonicalContractionData(R,1);
assert(pointContraction#"conclusive");
assert(pointContraction#"threshold" == 4);
assert(pointContraction#"targetDimension" == 0);
assert(pointContraction#"contractionType" == "fibration");
assert(pointContraction#"isFibreType");
assert(not pointContraction#"isBirational");
assert(pointContraction#"dimensionDrop" == 3);
assert(pointContraction#"steinFactorizationType" == "trivial point target");

-- On P(1,1,1,2), the construction uses O(2), not the generally noninvertible
-- O(1), and its complete linear system is base-point-free.
W = QQ[z0,z1,z2,z3,Degrees=>{1,1,1,2}];
weightedAmple = weightedAmpleDivisorData W;
assert(weightedAmple#"cartierDegree" == 2);
assert((degree weightedAmple#"section")#0 == 2);
assert(isBasePointFreeDivisor weightedAmple#"divisor");

-- A smooth quintic threefold has trivial canonical divisor, hence the first
-- pluricanonical search certifies nefness immediately.
S = QQ[y0,y1,y2,y3,y4];
Q = S/ideal(y0^5+y1^5+y2^5+y3^5+y4^5);
nonnegative = canonicalNefData(Q,1);
assert(nonnegative#"conclusive");
assert(nonnegative#"nef");
assert(nonnegative#"iteration" == 1);
assert(nonnegative#"witnessType" == "base-point-free pluricanonical divisor");
assert(isCanonicalNef(Q,1));

print "OK effective nef multipliers: m(3,1)=1920 and m(3,2)=1536.";
print "OK P3: K is non-nef, detected by the t=1/2 perturbation.";
print "OK P3: the computed nef threshold is lambda=4.";
print "OK P3: the threshold divisor gives the contraction to a point.";
print "OK P(1,1,1,2): the constructed ample Cartier degree is 2.";
print "OK quintic threefold: K=0 is certified nef at the first iteration.";
