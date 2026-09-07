needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");

-- A flip found and carried out by the driver, over an affine base.
--
-- Let N = Z^3 and sigma = cone(v1,v2,v3,v4) with
--
--     v1 = (1,0,0),  v2 = (0,1,0),  v3 = (0,0,1),  v4 = (1,1,-2),
--
-- the circuit v1 + v2 = 2 v3 + v4 of examples/toric-flip.m2 in
-- third_party/flip-computation.  X = Spec k[sigma^v cap M] is a threefold that
-- is not Q-Gorenstein, and the two triangulations of the circuit give its two
-- small modifications:
--
--     Y : {v1,v2,v3}, {v1,v2,v4}   wall <v1,v2>,   K.C = -1 < 0
--     Z : {v1,v3,v4}, {v2,v3,v4}   wall <v3,v4>,   K.C = +1 > 0
--
-- so Y -> X is a flipping contraction and Z is its flip.  Y is singular (the
-- cone <v1,v2,v4> has determinant -2, a 1/2(1,1,1) point) and Z is smooth.
--
-- Both sides are presented here the way the relative setting asks for: as
-- Proj of a Z-graded ring whose degree-zero part is the coordinate ring of X.
-- In Cox coordinates the circuit gives Cl(X) = Z with deg(z1,z2,z3,z4) =
-- (1,1,-2,-1), and Y is Proj of the ring of monomials of nonpositive weight,
-- graded by minus the weight.
--
-- Y's presentation is the SECOND VERONESE of that ring.  The ring itself needs
-- a degree-two generator (z3 alone, of weight -2, is not a product of
-- lower-degree elements), and with a weighted grading Spec R minus V(B) is not
-- a C^*-torsor over Y: at the 1/2(1,1,1) point the stabilizer is mu_2, which
-- lets a divisor be locally free on the punctured cone without being invertible
-- on Y.  The Cartier test then over-reports and the canonical index comes back
-- 1 where it is 2.  The Veronese has every positive-degree generator in degree
-- one, so the action is free and the test is exact.
veroneseY = () -> (
    -- Y's semigroup is {a >= 0 : 2a3+a4-a1-a2 >= 0}; the second Veronese
    -- intersects it with Lambda = {a : a1+a2+a4 even}, whose basis
    -- (2,0,0,0), (1,1,0,0), (0,0,1,0), (1,0,0,1) turns a into (2c1+c2+c4, c2,
    -- c3, c4) and the degree into c3-c1-c2.
    C := coneFromHData(
        matrix{{2,1,0,1},{0,1,0,0},{0,0,1,0},{0,0,0,1},{-1,-1,1,0}});
    HBc := apply(hilbertBasis C, v -> flatten entries v);
    HBa := apply(HBc, c -> {2*c#0+c#1+c#3, c#1, c#2, c#3});
    L := QQ[za,zb,zc,zd];
    S := QQ[u_1 .. u_(#HBa), Degrees => apply(HBc, c -> c#2-c#0-c#1)];
    S/ker map(L, S, apply(HBa,
        h -> za^(h#0)*zb^(h#1)*zc^(h#2)*zd^(h#3))));

-- Z, from its own semigroup {a >= 0 : a1+a2-2a3-a4 >= 0}, as ground truth.
groundTruthZ = () -> (
    C := coneFromHData(matrix{{1,1,-2,-1}} || id_(ZZ^4));
    HB := apply(hilbertBasis C, v -> flatten entries v);
    L := QQ[za,zb,zc,zd];
    S := QQ[w_1 .. w_(#HB), Degrees => apply(HB, a -> a#0+a#1-2*a#2-a#3)];
    S/ker map(L, S, apply(HB,
        h -> za^(h#0)*zb^(h#1)*zc^(h#2)*zd^(h#3))));

Y = veroneseY();
Z = groundTruthZ();

assert(dim Y - 1 == 3);
assert(isNormal Y);
assert(any(flatten degrees Y, d -> d == 0));

-- The canonical index is 2, which is what the 1/2(1,1,1) point forces, and K
-- is not nef.  Both were wrong before the relative-setting work: the index came
-- back 1 because isCartier's graded branch saturates the non-Cartier locus
-- against the homogeneous maximal ideal, which over an affine base contains the
-- base coordinates and so discards the very point where K fails to be Cartier.
indexY = canonicalIndexData Y;
assert(indexY#"conclusive");
assert(indexY#"index" == 2);
assert(not (canonicalNefData(Y,2))#"nef");

-- Z is smooth, its canonical index is 1, and K_Z is nef.
indexZ = canonicalIndexData Z;
assert(indexZ#"conclusive");
assert(indexZ#"index" == 1);
assert((canonicalNefData(Z,1))#"nef");

<< "OK relative affine flip: Y has canonical index 2 and K not nef; Z is its "
   << "nef counterpart." << endl;

-- The threshold.  H.C = 1 and (2K).C = -1 on the wall curve, so K + tH is nef
-- exactly for t >= 1/2.  Reaching this at all depends on the negative-curve
-- certificate: the candidates below 1/2 have denominators up to 31, and their
-- base-point-free tests construct O(m*L) with coefficients proportional to the
-- denominator -- half a second at denominator 2 and more than fifteen minutes
-- at denominator 8.  Deciding them by an intersection number on the fibre curve
-- instead is what makes the search finish.
assert(canonicalNefThreshold(Y,2) == 1/2);

contraction = canonicalContractionData(Y,2);
assert(contraction#"conclusive");
assert(contraction#"threshold" == 1/2);
assert(contraction#"isBirational");
assert(not contraction#"isFibreType");
assert(contraction#"contractionType" == "birational");
assert(contraction#"sourceDimension" == 3);
assert(contraction#"targetDimension" == 3);
assert(contraction#"affineBaseDimension" == 3);
assert(contraction#"contractionIsStructureMorphism");
assert(contraction#"steinFactorizationType" == "structure morphism to the affine base");
assert(dim(contraction#"steinAlgebraData"#"ring") == 3);
assert(not contraction#"steinAlgebraData"#"baseIsProjective");

-- The contraction is small: its exceptional locus is the wall curve, of
-- dimension one in a threefold.
smallness = contractionSmallnessData contraction;
assert(smallness#"isSmall");
assert(smallness#"exceptionalDimension" == 1);
assert(smallness#"exceptionalCodimension" == 2);
assert(#(smallness#"fibreCurves") == 1);

<< "OK relative affine flip: the contraction at t = 1/2 is the small "
   << "birational structure morphism Y -> Spec R_0." << endl;

-- The whole MMP, from the ring alone.
mmp = threefoldMMPData(Y,2);
assert(mmp#"conclusive");
assert(mmp#"terminationType" == "minimal model");
assert(mmp#"numberOfSteps" == 1);
flipStep = (mmp#"steps")#0;
assert(flipStep#"stepType" == "flipping");
assert(flipStep#"contractionIsSmall");
assert(flipStep#"stepTypeConclusive");
assert(flipStep#"contractionIsStructureMorphism");
assert(not flipStep#"inverseRelativeModelRequired");
assert(not (flipStep#"relativeModelData")#"isIdentity");
assert(not (flipStep#"relativeModelData")#"baseIsProjective");

flipRing = mmp#"finalRing";
assert(dim flipRing - 1 == 3);
assert(sort flatten degrees flipRing == sort flatten degrees Z);

-- The output is the flip, not merely something with its numbers: some
-- degree-preserving relabelling of the variables carries one defining ideal
-- onto the other.
matchesGroundTruth = (A,B) -> (
    ambA := ambient A;
    ambB := ambient B;
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
            if (map(ambB,ambA,toList images))(ideal A) == ideal B then
                found = true;
            )));
    found);
assert(matchesGroundTruth(flipRing,Z));

<< "OK relative affine flip: threefoldMMPData reaches a minimal model in one "
   << "flipping step, and the flip is the expected toric Z." << endl;

-- Control: the same smallness test says NOT small on a divisorial contraction
-- over an affine base.  Bl_0(A^3), as Proj of the Rees algebra of (a,b,c),
-- contracts the exceptional surface E, of dimension two in a threefold.
S2 = QQ[a,b,c,x,y,z, Degrees => {0,0,0,1,1,1}];
blowup = S2/minors(2, matrix{{a,b,c},{x,y,z}});
blowupContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionIsStructureMorphism" => true,
    "sourceRing" => blowup
    };
blowupSmallness = contractionSmallnessData blowupContraction;
assert(not blowupSmallness#"isSmall");
assert(blowupSmallness#"exceptionalDimension" == 2);
assert(blowupSmallness#"exceptionalCodimension" == 1);

-- Control: the test refuses a fibration, where the structure morphism is not
-- generically finite and the relative differentials do not have rank one.
fibration = QQ[t,x0,x1,x2, Degrees => {0,1,1,1}];
fibrationContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionIsStructureMorphism" => true,
    "sourceRing" => fibration
    };
assert(try (contractionSmallnessData fibrationContraction; false) else true);

<< "OK relative affine flip: the smallness test separates the small "
   << "contraction from a divisorial one and refuses a fibration." << endl;
