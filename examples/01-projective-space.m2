needsPackage("MMPComputation", FileName => "MMPComputation.m2")
R = QQ[x0,x1,x2,x3];
ample = weightedAmpleDivisorData R;
ample#"weights"
ample#"cartierDegree"
isBasePointFreeDivisor ample#"divisor"
nefTest = canonicalNefData(R,1);
nefTest#"conclusive"
nefTest#"nef"
nefTest#"witnessType"
nefTest#"witnessT"
nefTest#"scaledTest"#"N"
nefTest#"scaledTest"#"guaranteedMultiplier"
nefTest#"scaledTest"#"multipliersTested"
nefTest#"scaledTest"#"certificateType"
thresholdTest = canonicalNefThresholdData(R,1);
thresholdTest#"threshold"
(thresholdTest#"lowerBound", thresholdTest#"upperBound")
atThreshold = canonicalScaledNefData(R,1,4);
(atThreshold#"nef", atThreshold#"basePointFree")
contraction = canonicalContractionData(R,1);
contraction#"contractionType"
contraction#"sourceDimension"
contraction#"targetDimension"
contraction#"dimensionDrop"
contraction#"steinFactorizationType"
mmp = threefoldMMPData(R,1);
mmp#"terminationType"
mmp#"numberOfSteps"
apply(mmp#"steps", s -> s#"stepType")
