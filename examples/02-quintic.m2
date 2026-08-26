needsPackage("MMPComputation", FileName => "MMPComputation.m2")
S = QQ[y0,y1,y2,y3,y4];
Q = S/ideal(y0^5+y1^5+y2^5+y3^5+y4^5);
dim Q - 1
nefTest = canonicalNefData(Q,1);
nefTest#"nef"
nefTest#"iteration"
nefTest#"witnessType"
isCanonicalNef(Q,1)
mmp = threefoldMMPData(Q,1);
mmp#"terminationType"
mmp#"numberOfSteps"
