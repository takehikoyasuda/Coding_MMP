-- Raw-driver probe: can threefoldMMPData(Xminus,index) now discover the
-- flipping contraction and its flip completely on its own -- i.e. WITHOUT
-- the hand-built bigradedReesProjection/relativeCanonicalModelData/
-- mmpStepRecordData prefix that scripts/cyclic-cover-one-flip-minimal.m2
-- supplies by hand -- now that the canonical-ideal/class-degree BPF fast
-- path has removed the monograded-global-section bottleneck that the
-- CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT said made this impractical?
--
-- This script reconstructs Xminus exactly as in
-- scripts/cyclic-cover-one-flip-minimal.m2, then calls
-- threefoldMMPData(Xminus,index) with NO certified prefix at all.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");
needsPackage("NormalToricVarieties");

stamp = label -> (
    print(label | " cpu=" | toString cpuTime());
    flush stdio;
    );

rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB,
    h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));

T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
branch = sum apply(coverVars,q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));
stamp("cyclic-cover base");

Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase);
antiProjection = bigradedReesProjection antiIdeal;
assert(isSmallProjection(antiProjection,Verbose=>false));
assert(isS2Source antiProjection);
antiGraph = b2mToGraphMorphism(antiProjection,Verbose=>false);
Xminus = antiGraph#sourceRing;
stamp("Xminus constructed (no contraction/flip built by hand from here on)");

print("Xminus numgens ambient = " | toString numgens ambient Xminus);

indexData = canonicalIndexData(Xminus,CanonicalIndexSearchLimit=>12);
stamp("canonicalIndexData(Xminus)");
print("indexData conclusive=" | toString indexData#"conclusive");
if indexData#"conclusive" then
    print("index=" | toString indexData#"index");

if not indexData#"conclusive" then (
    print("STOP: canonical index search on Xminus was inconclusive; cannot call threefoldMMPData(Xminus,_).");
    ) else (
    idx := indexData#"index";
    result = threefoldMMPData(Xminus,idx,
        MMPMaxSteps=>4,
        NefSearchLimit=>12,
        ThresholdSearchLimit=>12,
        ContractionMultipleLimit=>12,
        RelativeCanonicalMultipliers=>{1,2},
        RelativeCanonicalVerbose=>true);
    stamp("threefoldMMPData(Xminus,idx) -- fully automatic");
    print("conclusive=" | toString result#"conclusive");
    if result#"conclusive" then (
        print("terminationType=" | result#"terminationType");
        print("numberOfSteps=" | toString result#"numberOfSteps");
        scan(result#"steps",s -> print("  stepType=" | s#"stepType"));
        ) else (
        print("phase=" | result#"phase");
        );
    )
flush stdio;
