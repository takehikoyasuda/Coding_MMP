needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");

-- A Q-Cartier target has itself as its relative canonical model.  This is the
-- branch used after an ordinary divisorial contraction.
P3 = QQ[p0,p1,p2,p3];
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
    "contractionGraph" => "identity contraction graph",
    "steinAlgebraData" => new HashTable from {"ring" => P3}
    };
assert((relativeCanonicalModelData identityContraction)#"isIdentity");
identityStep = mmpStepRecordData(identityContraction,identityModel);
assert(identityStep#"stepType" == "divisorial");
assert(identityStep#"stepTypeConclusive");
assert(not identityStep#"inverseRelativeModelRequired");

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

nontrivialContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionGraph" => "retained contraction graph"
    };
flippingStep = mmpStepRecordData(
    nontrivialContraction,flipModel,ContractionIsSmall=>true);
mixedStep = mmpStepRecordData(
    nontrivialContraction,flipModel,ContractionIsSmall=>false);
unknownStep = mmpStepRecordData(nontrivialContraction,flipModel);
assert(flippingStep#"stepType" == "flipping");
assert(mixedStep#"stepType" == "mixed");
assert(unknownStep#"stepType" == "flipping-or-mixed");
assert(not unknownStep#"stepTypeConclusive");
assert(flippingStep#"contractionGraph" == "retained contraction graph");
assert(flippingStep#"relativeModelGraph" === flipModel#"relativeModelGraph");
assert(flippingStep#"inverseRelativeModelRequired");

fibreContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => false
    };
assert(try (relativeCanonicalModelData fibreContraction; false) else true);

print "OK relative model: Q-Cartier P3 target returns the identity model.";
print "OK relative model: non-Q-Gorenstein toric target returns the known flip graph.";
print "OK relative model: fibre-type contractions are rejected before flip computation.";
print "OK step records: divisorial, flipping, mixed, and unresolved subtypes retain both graphs.";
