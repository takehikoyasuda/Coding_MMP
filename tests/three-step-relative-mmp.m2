needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- A relative MMP three steps long, found by the driver from the ring alone.
--
-- Every MMP this project had computed before was one or two steps: a single
-- flip (tests/relative-affine-flip-mmp.m2), a single divisorial contraction,
-- or a divisorial contraction followed by a K-negative fibration.  Two steps
-- is the shortest length at which a *sequence* exists at all, and one step of
-- it was always the last one.  This is the first input whose program has a
-- middle: a step that both starts from a ring the driver built itself and
-- hands one on to a further step.
--
-- The threefold is a product of a surface with a line, over an affine base.
-- In N = Z^2 the fan of A^2 = cone(u1,u2), u1 = (1,0), u2 = (0,1), is
-- subdivided by
--
--     u3 = (1,1),   u4 = u1+u3 = (2,1),   u5 = u1+u4 = (3,1),
--
-- each a star subdivision at a torus-fixed point of the previous exceptional
-- curve, so the surface S3 of the resulting fan -- whose rays in cyclic order
-- are u1, u5, u4, u3, u2 -- is a chain of three smooth point blow-ups over
-- A^2.  Write E1, E2, E3 for the divisors of u3, u4, u5.  Reading the
-- self-intersections off the neighbours in the fan,
--
--     u4+u2 = 2*u3,  u5+u3 = 2*u4,  u1+u4 = u5,
--
-- gives E1^2 = E2^2 = -2 and E3^2 = -1, hence by adjunction
--
--     K.E1 = K.E2 = 0,   K.E3 = -1.
--
-- So on S3 exactly one of the three curves is K-negative, and the same holds
-- again after E3 is contracted, and again after E2 is: the relative MMP over
-- A^2 is forced to contract E3, then E2, then E1, and only then is K nef.
-- Three steps, with no choice made anywhere and no coincidence of thresholds
-- to arrange.
--
-- X = S3 x A^1 is that surface as a threefold, projective over the affine
-- base A^3 = A^2 x A^1.  Multiplying by A^1 rather than by P^1 is what keeps
-- this affordable: the structure morphism stays birational, so
-- dim R - dim R_0 = 1 and the negative-curve certificate of the relative
-- setting applies -- every threshold candidate is then decided by an
-- intersection number on a fibre curve instead of by a base-point-free test.
-- With P^1 the intersection numbers still give a three-step program --
-- divisorial, divisorial, then the fibration to A^2 -- but there the fibre has
-- a threshold of its own, and it has to stay under both surface ones or the
-- fibration comes first and the program is over in one step.  With
-- H.E1 = H.E2 = 1 that asks 2/(H.F) < 1 for the first step and, after the
-- first contraction has moved the polarization to K+H, 2/(H.F - 2) < 1 for the
-- second: H.F >= 5.  Eighteen degree-one generators instead of four, and that
-- input was not carried through -- its canonical index alone had not
-- returned after eight minutes and ten gigabytes.
--
-- The polarization is the relatively ample A on S3 with A.E1 = A.E2 = A.E3 =
-- 1, namely -3*E1 - 5*E2 - 6*E3, whose sections over k[a,b] are the four
-- monomials below.  X is then presented the way the relative setting asks
-- for: Proj of a Z-graded ring whose degree-zero part is the coordinate ring
-- k[a,b,c] of the base.
ambientX = QQ[a,b,c,w_0,w_1,w_2,w_3, Degrees => {0,0,0,1,1,1,1}];
cox = QQ[ea,eb,ec,et];
X = ambientX/ker map(cox,ambientX,
    {ea,eb,ec, ea^3*et, ea^2*eb*et, ea*eb^3*et, eb^6*et});

assert(dim X - 1 == 3);
assert(isNormal X);
assert(any(flatten degrees X, d -> d == 0));

-- X is smooth, so the singularity hypotheses the algorithm is written for and
-- does not check are not in doubt here, and the canonical index is 1.
irrelevantOf = R -> ideal select(flatten entries vars R, q -> (degree q)#0 > 0);
isSmoothOver = R -> (
    singular := saturate(sub(ideal singularLocus R,R),irrelevantOf R);
    singular == ideal 1_R);
assert(isSmoothOver X);
assert((canonicalIndexData X)#"index" == 1);
assert(not (canonicalNefData(X,1))#"nef");

-- The three curves, read off the ring rather than off the fan.  Over an
-- affine base every curve of X proper over k lies in a fibre of X -> Spec R_0,
-- and here there are exactly three, with the intersection numbers the fan
-- predicts: two K-trivial and one K-negative, all three of degree one against
-- the polarization.  This is the whole three-step program in one table -- the
-- count of curves is what drops at each step, and the count of K-negative ones
-- is one throughout.
curveDegreeData = value(
    MMPComputation#"private dictionary"#"affineCurveDegreeDataInternal");
canonicalDivisorOf = value(
    MMPComputation#"private dictionary"#"mmpCanonicalDivisorInternal");
curveDegrees = R -> sort apply(
    curveDegreeData(R,canonicalDivisorOf R,
        (weightedAmpleDivisorData R)#"divisor",1),
    entry -> {entry#"canonicalDegree",entry#"ampleDegree"});
assert(curveDegrees X == {{-1,1},{0,1},{0,1}});

-- The threshold is 1: K + t*A is nef exactly for t >= 1, since the one
-- K-negative curve has (K + t*A).E3 = -1 + t and the K-trivial ones have
-- t >= 0 to spare.
assert(canonicalNefThreshold(X,1) == 1);

-- The first contraction.  Its target is neither the affine base nor a point,
-- so it is built as Proj over Spec R_0 of the algebra the section
-- representatives generate, and the Stein factorization is skipped on the
-- birational-onto-a-normal-image certificate rather than computed.
firstContraction = canonicalContractionData(X,1);
assert(firstContraction#"conclusive");
assert(firstContraction#"threshold" == 1);
assert(firstContraction#"isBirational");
assert(not firstContraction#"isFibreType");
assert(firstContraction#"sourceDimension" == 3);
assert(firstContraction#"targetDimension" == 3);
assert(not firstContraction#?"contractionIsStructureMorphism");
assert(firstContraction#"steinFactorizationType"
    == "trivial: birational onto a normal image over the affine base");

-- E3 x A^1 is a surface in a threefold, so the step is divisorial, not a flip.
firstSmallness = contractionSmallnessData firstContraction;
assert(not firstSmallness#"isSmall");
assert(firstSmallness#"exceptionalDimension" == 2);
assert(firstSmallness#"exceptionalCodimension" == 1);

<< "OK three-step relative MMP: X = S3 x A^1 over A^3 has three fibre curves, "
   << "one of them K-negative, and contracts divisorially at t = 1." << endl;

-- Ground truth for the two intermediate models, built the same way as X from
-- their own polarizations: on S2 the ample class with A.E1 = A.E2 = 1 is
-- -2*E1 - 3*E2, with sections a^2, ab, b^3, and on S1 the class with A.E1 = 1
-- is -E1, with sections a, b -- the Rees algebra of (a,b), which is
-- Bl_0(A^2) x A^1.
ambientY = QQ[a,b,c,v_0,v_1,v_2, Degrees => {0,0,0,1,1,1}];
groundTruthY = ambientY/ker map(cox,ambientY,
    {ea,eb,ec, ea^2*et, ea*eb*et, eb^3*et});
ambientZ = QQ[a,b,c,z_0,z_1, Degrees => {0,0,0,1,1}];
groundTruthZ = ambientZ/ker map(cox,ambientZ,{ea,eb,ec, ea*et, eb*et});

assert(dim groundTruthY - 1 == 3);
assert(dim groundTruthZ - 1 == 3);
assert(isSmoothOver groundTruthY);
assert(isSmoothOver groundTruthZ);
-- one curve fewer at each stage, and still exactly one of them K-negative
assert(curveDegrees groundTruthY == {{-1,1},{0,1}});
assert(curveDegrees groundTruthZ == {{-1,1}});
assert((canonicalIndexData groundTruthY)#"index" == 1);
assert((canonicalIndexData groundTruthZ)#"index" == 1);
assert(not (canonicalNefData(groundTruthY,1))#"nef");
assert(not (canonicalNefData(groundTruthZ,1))#"nef");
assert(canonicalNefThreshold(groundTruthY,1) == 1);
assert(canonicalNefThreshold(groundTruthZ,1) == 1);

-- Some degree-preserving relabelling of the variables carries one defining
-- ideal onto the other: the output is the expected model, not merely something
-- with its numbers.
matchesGroundTruth = (A1,B1) -> (
    ambA := ambient A1;
    ambB := ambient B1;
    if numgens ambA != numgens ambB then return false;
    srcOne := select(flatten entries vars ambA, v -> (degree v)#0 == 1);
    srcZero := select(flatten entries vars ambA, v -> (degree v)#0 == 0);
    tgtOne := select(flatten entries vars ambB, v -> (degree v)#0 == 1);
    tgtZero := select(flatten entries vars ambB, v -> (degree v)#0 == 0);
    if #srcOne != #tgtOne or #srcZero != #tgtZero then return false;
    found := false;
    scan(permutations tgtOne, p1 -> if not found then
        scan(permutations tgtZero, p0 -> if not found then (
            images := new MutableList from toList(numgens ambA : null);
            scan(#srcOne, i -> images#(index srcOne#i) = p1#i);
            scan(#srcZero, i -> images#(index srcZero#i) = p0#i);
            if (map(ambB,ambA,toList images))(ideal A1) == ideal B1 then
                found = true;
            )));
    found);

-- The whole program, from the ring alone: no contraction graph, no target and
-- no polarization supplied at any step.
mmp = threefoldMMPData(X,1);
assert(mmp#"conclusive");
assert(mmp#"terminationType" == "minimal model");
assert(mmp#"numberOfSteps" == 3);
steps = mmp#"steps";
assert(apply(steps, r -> r#"stepType")
    == {"divisorial","divisorial","divisorial"});
assert(all(steps, r -> r#"stepTypeConclusive"));
assert(all(steps, r -> not r#"contractionIsSmall"));

-- The first two contractions go to intermediate targets the driver builds, and
-- only the last one is the structure morphism to the affine base.  That is
-- what makes this a program with a middle rather than two programs of length
-- one.
assert(steps#0#"contractionToRelativeTarget");
assert(steps#1#"contractionToRelativeTarget");
assert(not steps#0#"contractionIsStructureMorphism");
assert(not steps#1#"contractionIsStructureMorphism");
assert(not steps#2#"contractionToRelativeTarget");
assert(steps#2#"contractionIsStructureMorphism");

assert(matchesGroundTruth(steps#0#"nextRing",groundTruthY));
assert(matchesGroundTruth(steps#1#"nextRing",groundTruthZ));

-- A^3, handed back as Proj of A^3[t] so that the last iteration has a Proj to
-- read, and K is nef there on a base-point-free pluricanonical certificate.
finalRing = mmp#"finalRing";
assert(finalRing === steps#2#"nextRing");
assert(dim finalRing - 1 == 3);
assert(sort flatten degrees finalRing == {0,0,0,1});
assert(ideal finalRing == ideal 0_(ambient finalRing));
assert((mmp#"finalNefData")#"conclusive");
assert((mmp#"finalNefData")#"nef");
assert((mmp#"finalNefData")#"witnessType"
    == "base-point-free pluricanonical divisor");
-- and the same question asked again from the outside
assert((canonicalIndexData finalRing)#"index" == 1);
assert((canonicalNefData(finalRing,1))#"nef");

<< "OK three-step relative MMP: threefoldMMPData contracts E3, then E2, then "
   << "E1, reaching A^3 as a minimal model in three divisorial steps, and each "
   << "intermediate model is the expected one." << endl;
