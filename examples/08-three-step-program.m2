needsPackage("MMPComputation", FileName => "MMPComputation.m2")
monomials4 = QQ[ea,eb,ec,et]
ambientX = QQ[a,b,c,w_0,w_1,w_2,w_3, Degrees => {0,0,0,1,1,1,1}]
X = ambientX/ker map(monomials4, ambientX,
    {ea,eb,ec, ea^3*et, ea^2*eb*et, ea*eb^3*et, eb^6*et})
dim X - 1
isNormal X
flatten degrees X
ideal X
(canonicalIndexData X)#"index"
(canonicalNefData(X, 1))#"nef"
canonicalNefThreshold(X, 1)
contraction = canonicalContractionData(X, 1);
contraction#"contractionType"
contraction#"targetDimension"
contraction#"steinFactorizationType"
flatten degrees contraction#"relativeTargetRing"
smallness = contractionSmallnessData contraction;
smallness#"isSmall"
smallness#"exceptionalDimension"
mmp = threefoldMMPData(X, 1);
mmp#"terminationType"
mmp#"numberOfSteps"
apply(mmp#"steps", r -> r#"stepType")
apply(mmp#"steps", r -> r#"contractionToRelativeTarget")
apply(mmp#"steps", r -> r#"contractionIsStructureMorphism")
apply(mmp#"steps", r -> flatten degrees r#"nextRing")
flatten degrees mmp#"finalRing"
ideal mmp#"finalRing"
(mmp#"finalNefData")#"witnessType"
ambientY = QQ[a,b,c,v_0,v_1,v_2, Degrees => {0,0,0,1,1,1}]
groundTruthY = ambientY/ker map(monomials4, ambientY,
    {ea,eb,ec, ea^2*et, ea*eb*et, eb^3*et})
ambientZ = QQ[a,b,c,z_0,z_1, Degrees => {0,0,0,1,1}]
groundTruthZ = ambientZ/ker map(monomials4, ambientZ, {ea,eb,ec, ea*et, eb*et})
ideal groundTruthY
ideal groundTruthZ
sameRing = (A, B) -> (
    ambA := ambient A; ambB := ambient B;
    byDegree := amb -> (
        vs := flatten entries vars amb;
        {select(vs, v -> (degree v)#0 == 1), select(vs, v -> (degree v)#0 == 0)});
    src := byDegree ambA; tgt := byDegree ambB;
    found := false;
    scan(permutations tgt#0, p1 -> if not found then
        scan(permutations tgt#1, p0 -> if not found then (
            images := new MutableList from toList(numgens ambA : null);
            scan(#(src#0), i -> images#(index (src#0)#i) = p1#i);
            scan(#(src#1), i -> images#(index (src#1)#i) = p0#i);
            if (map(ambB, ambA, toList images))(ideal A) == ideal B then
                found = true)));
    found)
sameRing(mmp#"steps"#0#"nextRing", groundTruthY)
sameRing(mmp#"steps"#1#"nextRing", groundTruthZ)
canonicalNefThreshold(groundTruthY, 1)
canonicalNefThreshold(groundTruthZ, 1)
