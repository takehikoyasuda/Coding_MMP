needsPackage("MMPComputation", FileName => "MMPComputation.m2")
B = QQ[z00,z01,z02,z10,z11,z12,t0,t1,
    Degrees => {{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{0,1},{0,1}}];
A0 = QQ[s0,s1,x0,x1,x2,sourceScale,targetScale];
parametrization = map(A0,B,{
    s0*x0*sourceScale, s0*x1*sourceScale, s0*x2*sourceScale,
    s1*x0*sourceScale, s1*x1*sourceScale, s1*x2*sourceScale,
    s0^2*targetScale, s1^2*targetScale});
fIdeal = kernel parametrization;
irrelevantTarget = ideal(t0,t1);
generalFibre = saturate(fIdeal + ideal(t0-t1), irrelevantTarget);
#decompose generalFibre
branchFibre = saturate(fIdeal + ideal(t1), irrelevantTarget);
#decompose branchFibre
steinData = steinHomData(B, fIdeal);
steinData#"certifiedBound"
steinAlgebra = steinCoordinateAlgebra steinData;
dim(steinAlgebra#"ring") - 1
dim(steinAlgebra#"baseRing") - 1
typeData = contractionTypeData(3, dim(steinAlgebra#"ring") - 1);
typeData#"dimensionDrop"
rank(steinAlgebra#"strandAsAModule")
