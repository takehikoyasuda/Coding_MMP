needsPackage("MMPComputation", FileName => "MMPComputation.m2")
needsPackage "Polyhedra"
coxWeights = {1,1,-2,-1}
veroneseSide = (w, side, d) -> (
    degvec := apply(w, c -> side*c);
    lam := if d == 1 then id_(ZZ^4)
        else mingens ker map(coker matrix{{d}}, ZZ^4, matrix{degvec});
    exponents := apply(
        hilbertBasis coneFromHData((lam || matrix{degvec}*lam)),
        v -> flatten entries (lam * v));
    L := QQ[za,zb,zc,zd];
    S := QQ[u_1 .. u_(#exponents),
        Degrees => apply(exponents,
            a -> (sum apply(4, i -> degvec#i * a#i)) // d)];
    S/ker map(L, S, apply(exponents,
        h -> za^(h#0)*zb^(h#1)*zc^(h#2)*zd^(h#3))))
Y = veroneseSide(coxWeights, -1, 2);
numgens Y
flatten degrees Y
dim Y - 1
isNormal Y
indexData = canonicalIndexData Y;
indexData#"index"
nefData = canonicalNefData(Y, 2);
nefData#"nef"
nefData#"witnessType"
canonicalNefThreshold(Y, 2)
contraction = canonicalContractionData(Y, 2);
contraction#"contractionType"
contraction#"steinFactorizationType"
contraction#"affineBaseDimension"
dim(contraction#"steinAlgebraData"#"ring")
smallness = contractionSmallnessData contraction;
smallness#"isSmall"
smallness#"exceptionalDimension"
smallness#"exceptionalCodimension"
mmp = threefoldMMPData(Y, 2);
mmp#"terminationType"
mmp#"numberOfSteps"
apply(mmp#"steps", r -> r#"stepType")
Z = mmp#"finalRing";
flatten degrees Z
(canonicalIndexData Z)#"index"
(canonicalNefData(Z, 1))#"nef"
groundTruthZ = veroneseSide(coxWeights, 1, 1);
flatten degrees groundTruthZ
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
sameRing(Z, groundTruthZ)
blowup = (QQ[a,b,c,x,y,z, Degrees => {0,0,0,1,1,1}])/minors(2,
    matrix{{a,b,c},{x,y,z}});
(canonicalIndexData blowup)#"index"
canonicalNefThreshold(blowup, 1)
blowupSmallness = contractionSmallnessData canonicalContractionData(blowup, 1);
blowupSmallness#"isSmall"
blowupSmallness#"exceptionalDimension"
blowupMMP = threefoldMMPData(blowup, 1);
blowupMMP#"terminationType"
apply(blowupMMP#"steps", r -> r#"stepType")
flatten degrees blowupMMP#"finalRing"
Y3 = veroneseSide({1,1,-1,-3}, -1, 3);
flatten degrees Y3
(canonicalIndexData Y3)#"index"
canonicalNefThreshold(Y3, 3)
mmp3 = threefoldMMPData(Y3, 3);
mmp3#"terminationType"
apply(mmp3#"steps", r -> r#"stepType")
(canonicalIndexData mmp3#"finalRing")#"index"
segre = QQ[a,b,x,y,z0,z1]/ideal(a*y-b*x);
twoStepAmbient = QQ[w_1 .. w_8, wa, wb, Degrees => {1,1,1,1,1,1,1,1,0,0}];
twoStep = twoStepAmbient/ker map(segre, twoStepAmbient,
    flatten apply({x,y}, f -> apply({z0^3,z0^2*z1,z0*z1^2,z1^3}, g -> f*g))
    | {a,b});
dim twoStep - 1
canonicalNefThreshold(twoStep, 1)
twoStepContraction = canonicalContractionData(twoStep, 1);
twoStepContraction#"contractionType"
twoStepContraction#"targetDimension"
twoStepContraction#"steinFactorizationType"
flatten degrees twoStepContraction#"relativeTargetRing"
ideal twoStepContraction#"relativeTargetRing"
(contractionSmallnessData twoStepContraction)#"exceptionalDimension"
twoStepMMP = threefoldMMPData(twoStep, 1);
twoStepMMP#"terminationType"
twoStepMMP#"numberOfSteps"
apply(twoStepMMP#"steps", r -> r#"stepType")
