needsPackage("MMPComputation", FileName => "MMPComputation.m2")
monomials4 = QQ[ea,eb,ec,et]
baseGenerators = {eb, eb^2*ec, ea, ea*eb*ec, ea^2*ec}
relativeModel = (fibreGenerators, letter) -> (
    n := #fibreGenerators;
    S := QQ[p_1 .. p_5, (getSymbol letter)_1 .. (getSymbol letter)_n,
        Degrees => join(toList(5:0), toList(n:1))];
    S/ker map(monomials4, S, baseGenerators | fibreGenerators))
X = relativeModel({et, ec*et, eb*ec^2*et, eb^2*ec^3*et, ea*ec^2*et,
    ea*eb*ec^3*et}, "q")
dim X - 1
flatten degrees X
(canonicalIndexData X)#"index"
(canonicalNefData(X, 1))#"nef"
mmp = threefoldMMPData(X, 1);
mmp#"terminationType"
mmp#"numberOfSteps"
apply(mmp#"steps", r -> r#"stepType")
apply(mmp#"steps", r -> r#"contractionIsSmall")
apply(mmp#"steps", r -> (r#"relativeModelData")#"isIdentity")
apply(mmp#"steps", r -> flatten degrees r#"nextRing")
contraction = mmp#"steps"#0#"contractionData";
contraction#"threshold"
contraction#"contractionType"
contraction#"steinFactorizationType"
flatten degrees contraction#"relativeTargetRing"
flipContraction = mmp#"steps"#2#"contractionData";
flipContraction#"steinFactorizationType"
flipContraction#"contractionIsStructureMorphism"
(mmp#"steps"#2#"contractionSmallnessData")#"exceptionalDimension"
flippingSource = mmp#"steps"#1#"nextRing";
(canonicalIndexData flippingSource)#"index"
finalRing = mmp#"finalRing";
(canonicalIndexData finalRing)#"index"
(canonicalNefData(finalRing, 1))#"nef"
(mmp#"finalNefData")#"witnessType"
groundTruthX1 = relativeModel({ea*eb*ec*et, ea*eb*ec^2*et, ea*eb^2*ec^3*et,
    ea^2*eb*ec^3*et}, "s")
groundTruthY = relativeModel({ea^2*eb^2*ec^2*et, ea^2*eb^2*ec^3*et}, "y")
groundTruthZ = relativeModel({eb*et, ea*et}, "z")
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
sameRing(mmp#"steps"#0#"nextRing", groundTruthX1)
sameRing(mmp#"steps"#1#"nextRing", groundTruthY)
sameRing(finalRing, groundTruthZ)
