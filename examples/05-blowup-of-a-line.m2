needsPackage("MMPComputation", FileName => "MMPComputation.m2")
B = QQ[y00,y01,y10,y11,y20,y21,y30,y31,z0,z1,z2,z3,
    Degrees => {
        {1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},
        {0,1},{0,1},{0,1},{0,1}}];
A0 = QQ[x0,x1,x2,x3,u,v,sourceScale,targetScale];
A = A0/ideal(x0*v-x1*u);
parametrization = map(A,B,{
    x0*u*sourceScale, x0*v*sourceScale,
    x1*u*sourceScale, x1*v*sourceScale,
    x2*u*sourceScale, x2*v*sourceScale,
    x3*u*sourceScale, x3*v*sourceScale,
    x0*targetScale, x1*targetScale, x2*targetScale, x3*targetScale});
blowupIdeal = kernel parametrization;
steinData = steinHomData(B, blowupIdeal);
steinData#"certifiedBound"
steinAlgebra = steinCoordinateAlgebra steinData;
dim(steinAlgebra#"ring") - 1
degreeLength(steinAlgebra#"ring")
typeData = contractionTypeData(3, dim(steinAlgebra#"ring") - 1);
typeData#"contractionType"
typeData#"dimensionDrop"
SP = QQ[w00,w01,w10,w11,w20,w21,w30,w31];
blowupSourceMap = map(SP,B, flatten entries vars SP | toList(4:0_SP));
blowupSourceRing = SP/blowupSourceMap eliminate(blowupIdeal, drop(flatten entries vars B,8));
dim blowupSourceRing - 1
blowupGraph = mmpGraphMorphism new HashTable from {
    "jointRing" => B,
    "graphIdeal" => blowupIdeal,
    "sourceVariableCount" => 8,
    "sourceRing" => blowupSourceRing,
    "targetRing" => steinAlgebra#"ring"};
smallness = contractionGraphSmallnessData blowupGraph;
smallness#"isSmall"
smallness#"exceptionalDimension"
smallness#"exceptionalCodimension"
ODP = QQ[g0,g1,g2,g3,g4]/ideal(g0*g1-g2*g3);
smallGraph = b2mToGraphMorphism bigradedReesProjection ideal(ODP_0,ODP_2);
odpSmallness = contractionGraphSmallnessData smallGraph;
odpSmallness#"isSmall"
odpSmallness#"exceptionalDimension"
odpSmallness#"exceptionalCodimension"
contraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionGraph" => blowupGraph,
    "steinAlgebraData" => new HashTable from {"ring" => steinAlgebra#"ring"}};
model = relativeCanonicalModelData contraction;
model#"relativeModelType"
blowupStep = mmpStepRecordData(contraction, model);
blowupStep#"stepType"
mmp = threefoldMMPData(steinAlgebra#"ring", 1, {blowupStep});
mmp#"terminationType"
mmp#"numberOfSteps"
apply(mmp#"steps", r -> r#"stepType")
