needsPackage("MMPComputation", FileName => "MMPComputation.m2")
S = QQ[z00,z01,z02,z10,z11,z12];
X = S/minors(2, matrix{{z00,z01,z02},{z10,z11,z12}});
dim X - 1
canonicalNefThreshold(X,1)
contraction = canonicalContractionAtThresholdData(X,1,3);
contraction#"conclusive"
contraction#"threshold"
contraction#"multiplier"
contraction#"guaranteedMultiplier"
contraction#"contractionType"
(contraction#"sourceDimension", contraction#"targetDimension")
contraction#"dimensionDrop"
contraction#"steinFactorizationType"
contraction#"steinHomData"#"certifiedBound"
contraction#"linearSystemGraph"#"targetVariableCount"
isPrime contraction#"linearSystemGraph"#"graphIdeal"
graph = contraction#"contractionGraph";
class graph
numgens source vars graph#ambientRing
graph#fiberVariables
graph#baseVariables
dim(graph#totalRing) == dim X + 1
