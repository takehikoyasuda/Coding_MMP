needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");

-- A Q-Cartier target has itself as its relative canonical model.  This is the
-- branch used after an ordinary divisorial contraction.
P3 = QQ[p0,p1,p2,p3];
identityHyperplane = (weightedAmpleDivisorData P3)#"divisor";
identityContractionGraph = (completeLinearSystemGraphData identityHyperplane)#"graph";
identityModel = relativeCanonicalModelFromBaseData P3;
assert(identityModel#"conclusive");
assert(identityModel#"relativeModelType" == "identity");
assert(identityModel#"isIdentity");
assert(identityModel#"relativeModelRing" === P3);
identityCheck = relativeCanonicalModelIsomorphismData identityModel;
assert(identityCheck#"isIsomorphism");

identityContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionGraph" => identityContractionGraph,
    "steinAlgebraData" => new HashTable from {"ring" => P3}
    };
assert((relativeCanonicalModelData identityContraction)#"isIdentity");
identityStep = mmpStepRecordData(identityContraction,identityModel);
assert(identityStep#"stepType" == "divisorial");
assert(identityStep#"stepTypeConclusive");
assert(not identityStep#"inverseRelativeModelRequired");
assert(identityStep#"inverseRelativeModelData" === null);
assert(try (relativeModelInverseRationalMapData identityModel; false) else true);

-- The projective toric circuit target is not Q-Gorenstein.  Its relative
-- canonical model is the independently verified flip in FlipComputation.
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB,
    h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
S = QQ[y_1 .. y_(#HB),w];
W = S/sub(I0,S);
flipModel = relativeCanonicalModelFromBaseData(
    W,RelativeCanonicalMultipliers=>{1});
assert(flipModel#"conclusive");
assert(flipModel#"relativeModelType" == "computed");
assert(not flipModel#"isIdentity");
assert(not (relativeCanonicalModelIsomorphismData flipModel)#"isIsomorphism");
assert(instance(flipModel#"relativeModelGraph",GraphMorphism));
assert(instance(flipModel#"relativeModelProjection",B2MProjection));
assert(dim(flipModel#"relativeModelRing")-1 == 3);
assert(dim(flipModel#"relativeModelGraph"#totalRing)-2 == 3);
inverseModel = relativeModelInverseRationalMapData flipModel;
assert(inverseModel#"sourceRing" === W);
assert(inverseModel#"targetRing" === flipModel#"relativeModelRing");
assert(#inverseModel#"coordinateImages" == 12);
assert(inverseModel#"degreeScale" == 2);
assert(inverseModel#"modelRelationsVanish");
assert(inverseModel#"graphRelationsVanish");
assert(inverseModel#"baseLocusCertified");
assert(saturate(radical inverseModel#"baseIdeal",ideal vars W)
    == saturate(radical ideal(W_4,W_3),ideal vars W));

-- The same toric target with grading l=(3,2,1) has canonical ideal generators
-- of degrees 2 and 3.  Its Rees fibre block is skew, so the generalized
-- diagonal construction (slope two) is required for both graph and inverse.
weightedEll = {3,2,1};
weightedDegrees = apply(HB,h -> sum apply(3,k -> h#k*weightedEll#k));
assert(weightedDegrees == {2,5,3,6,7});
WS0 = QQ[wy_1..wy_(#HB),Degrees=>weightedDegrees];
WI0 = ker map(L,WS0,apply(HB,
    h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
WS = QQ[wy_1..wy_(#HB),ww,Degrees=>weightedDegrees|{1}];
WW = WS/sub(WI0,WS);
weightedFlipModel = relativeCanonicalModelFromBaseData(
    WW,RelativeCanonicalMultipliers=>{1});
assert(not weightedFlipModel#"isIdentity");
assert(instance(weightedFlipModel#"relativeModelGraph",GraphMorphism));
weightedProjection = weightedFlipModel#"relativeModelProjection";
assert(apply(weightedProjection#fiberVariables,degree) == {{1,0},{1,1}});
weightedInverse = relativeModelInverseRationalMapData weightedFlipModel;
assert(weightedInverse#"diagonalData"#"diagonalSlope" == 2);
assert(weightedInverse#"diagonalData"#"transformedFiberWeights" == {2,1});
assert(weightedInverse#"modelRelationsVanish");
assert(weightedInverse#"graphRelationsVanish");
assert(weightedInverse#"baseLocusCertified");

nontrivialContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionGraph" => flipModel#"relativeModelGraph"
    };
flippingStep = mmpStepRecordData(
    nontrivialContraction,flipModel,ContractionIsSmall=>true);
mixedStep = mmpStepRecordData(
    nontrivialContraction,flipModel,ContractionIsSmall=>false);
automaticStep = mmpStepRecordData(nontrivialContraction,flipModel);
assert(flippingStep#"stepType" == "flipping");
assert(mixedStep#"stepType" == "mixed");
assert(automaticStep#"stepType" == "flipping");
assert(automaticStep#"stepTypeConclusive");
assert(automaticStep#"contractionIsSmall");
assert(flippingStep#"contractionGraph" === flipModel#"relativeModelGraph");
assert(flippingStep#"relativeModelGraph" === flipModel#"relativeModelGraph");
assert(flippingStep#"inverseRelativeModelRequired");
assert(flippingStep#"inverseRelativeModelData"#"baseLocusCertified");

fibreContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => false
    };
assert(try (relativeCanonicalModelData fibreContraction; false) else true);

print "OK relative model: Q-Cartier P3 target returns the identity model.";
print "OK relative model: non-Q-Gorenstein toric target returns the known flip graph.";
print "OK inverse map: Rees generators give certified rational coordinates for the toric flip.";
print "OK weighted flip: skew Rees degrees use a certified positive diagonal.";
print "OK relative model: fibre-type contractions are rejected before flip computation.";
print "OK step records: divisorial, flipping, and mixed subtypes retain normalized graphs.";
