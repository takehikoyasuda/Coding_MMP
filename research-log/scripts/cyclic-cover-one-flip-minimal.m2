needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");
needsPackage("NormalToricVarieties");

stamp = label -> (
    print(label | " cpu=" | toString cpuTime());
    flush stdio;
    );

-- Start with the compact projective toric circuit base W.  Its two small
-- modifications are related by the circuit v1+v2=2v3+v4.
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB,
    h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));

-- Independent fan calculation motivating the cover: A is the polarization
-- of the compactification.  K+3A is non-nef before the flip and nef after it.
compactRays = {{1,0,0},{0,1,0},{0,0,1},{-1,-1,1},{1,1,-2}};
outerCones = {{0,2,3},{0,3,4},{1,2,3},{1,3,4}};
minusFan = normalToricVariety(
    compactRays,outerCones|{{0,1,2},{0,1,4}});
plusFan = normalToricVariety(
    compactRays,outerCones|{{0,2,4},{1,2,4}});
Aminus = toricDivisor({0,0,0,1,0},minusFan);
Aplus = toricDivisor({0,0,0,1,0},plusFan);
assert(not isNef(toricDivisor minusFan+3*Aminus));
assert(isNef(toricDivisor plusFan+3*Aplus));

-- A degree-four cyclic cover, branched in 4A.  The cyclic-cover formula gives
-- K_cover = pullback(K_W+3A).  On the canonical side K+3A is nef, while on
-- the anti-canonical side it is negative precisely on the flipping curves.
T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
branch = sum apply(coverVars,q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));
assert(dim Wcover-1 == 3);
assert(isPrime ideal Wcover);
coverIrrelevant = ideal flatten entries vars Wcover;
expectedSingular = ideal take(flatten entries vars Wcover,#HB);
actualSingular = sub(ideal singularLocus Wcover,Wcover);
assert(saturate(radical actualSingular,coverIrrelevant)
    == saturate(radical expectedSingular,coverIrrelevant));
assert(dim(Wcover/expectedSingular)-1 == 0);
stamp("cyclic-cover base");

-- The anti-canonical relative model is the starting threefold Xminus.  The
-- second Veronese is used because the local flipping side has index two.
Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase); -- ideal(D) represents O(-D)
antiProjection = bigradedReesProjection antiIdeal;
assert(isSmallProjection(antiProjection,Verbose=>false));
assert(isS2Source antiProjection);
antiGraph = b2mToGraphMorphism(antiProjection,Verbose=>false);
Xminus = antiGraph#sourceRing;
antiAmbient = antiProjection#ambientRing;
antiBaseVars = antiProjection#baseVariables;
pointIdeal = ideal join(take(antiBaseVars,#HB),
    {antiBaseVars#(#HB)-1,antiBaseVars#(#HB+1)-1});
fibreIdeal = trim(antiProjection#definingIdeal+pointIdeal);
fibreDimension = dim(antiAmbient/fibreIdeal)-1;
assert(fibreDimension == 1);
stamp("anti-canonical source and contraction");

contraction = new HashTable from join({
    "conclusive"=>true,
    "contractionGraph"=>antiGraph,
    "steinAlgebraData"=>new HashTable from {"ring"=>Wcover},
    "constructionCertificate"=>
        "Proj of the second anti-canonical algebra; small and S2"
    },pairs contractionTypeData(3,3));

-- Construct the relative canonical model from the contraction target.  This
-- is the actual flip, not a supplied post-flip ring.
flipModel = relativeCanonicalModelData(
    contraction,RelativeCanonicalMultipliers=>{1,2});
assert(flipModel#"conclusive");
assert(not flipModel#"isIdentity");
Xplus = flipModel#"relativeModelRing";
flipStep = mmpStepRecordData(
    contraction,flipModel,ContractionIsSmall=>true);
assert(flipStep#"stepType" == "flipping");
assert(flipStep#"nextRing" === Xplus);
stamp("relative canonical model and flip step");

-- The public driver accepts a certified birational prefix and continues from
-- its next ring.  It must immediately recognize Xplus as a minimal model.
result = threefoldMMPData(Xplus,1,{flipStep});
stamp("complete MMP");

print("sourceVariables=" | toString numgens ambient Xminus);
print("flipVariables=" | toString numgens ambient Xplus);
print("stepType=" | flipStep#"stepType");
print("exceptionalFibreDimension=" | toString fibreDimension);
print("terminationType=" | result#"terminationType");
print("numberOfSteps=" | toString result#"numberOfSteps");
print("finalNef=" | toString result#"finalNefData"#"nef");
flush stdio;

assert(result#"conclusive");
assert(result#"terminationType" == "minimal model");
assert(result#"numberOfSteps" == 1);
assert(result#"finalNefData"#"nef");
