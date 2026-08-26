needsPackage("MMPComputation", FileName => "MMPComputation.m2")
needsPackage("Polyhedra")
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v)
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0, apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)))
S = QQ[y_1 .. y_(#HB),w];
W = S/sub(I0,S);
dim W - 1
canonicalIdeal W != ideal 1_W
flipModel = relativeCanonicalModelFromBaseData(W, RelativeCanonicalMultipliers => {1});
flipModel#"conclusive"
flipModel#"relativeModelType"
flipModel#"isIdentity"
(relativeCanonicalModelIsomorphismData flipModel)#"isIsomorphism"
dim(flipModel#"relativeModelRing") - 1
class flipModel#"relativeModelGraph"
inverseModel = relativeModelInverseRationalMapData flipModel;
#inverseModel#"coordinateImages"
inverseModel#"degreeScale"
inverseModel#"modelRelationsVanish"
inverseModel#"graphRelationsVanish"
inverseModel#"baseLocusCertified"
saturate(radical inverseModel#"baseIdeal", ideal vars W) == saturate(radical ideal(W_4,W_3), ideal vars W)
contraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionGraph" => flipModel#"relativeModelGraph"};
flippingStep = mmpStepRecordData(contraction, flipModel);
flippingStep#"stepType"
flippingStep#"contractionIsSmall"
flippingStep#"inverseRelativeModelRequired"
