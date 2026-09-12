needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- A relative MMP three steps long whose last step is a flip.
--
-- Runs in about two and a half minutes, nearly all of it the first step: the
-- nef-threshold search and the contraction after it are 69 s and 129 s of cpu
-- time when timed on their own, and everything after that first step is under
-- twenty seconds together.
--
-- tests/three-step-relative-mmp.m2 reaches three steps with three divisorial
-- contractions, and there every relative canonical model is the identity: the
-- targets are Q-Gorenstein, so Algorithm 4 returns the base it was given.  This
-- program ends with a flip instead -- a small contraction whose relative
-- canonical model is a new variety, constructed rather than recognized -- and
-- it is the first program here that is more than one step long and contains
-- one.
--
-- Why the flip has to come last.  Over an affine base the flipping contraction
-- the code can carry out is the structure morphism X -> Spec R_0, and that is
-- the contraction at the threshold only when the relative Picard rank is one.
-- A flip onto an intermediate target would ask Algorithm 4 for the relative
-- canonical model of a base that is itself a Proj over Spec R_0, whose Rees
-- construction has variables of degree zero in the fibre grading and so no heft
-- vector.  A program with a flip in it therefore has to spend its Picard rank
-- on divisorial steps first, and flip at the end.
--
-- The base is example 7's.  In N = Z^3 let
--
--     v1 = (1,0,0),  v2 = (0,1,0),  v3 = (0,0,1),  v4 = (1,1,-2),
--
-- a circuit with v1 + v2 = 2v3 + v4, and let sigma = cone(v1,v2,v3,v4), so
-- Spec R_0 = Spec k[sigma^v cap M] is an affine threefold that is not
-- Q-Gorenstein.  The two triangulations of the circuit are its two small
-- modifications,
--
--     Y : {v1,v2,v3}, {v1,v2,v4}   wall <v1,v2>,  K.C = -1
--     Z : {v1,v3,v4}, {v2,v3,v4}   wall <v3,v4>,  K.C = +1
--
-- so Y -> Spec R_0 is the flipping contraction and Z is the flip.  Y is
-- singular: <v1,v2,v4> has multiplicity two, a 1/2(1,1,1) point.
--
-- Two rays are added above Y:
--
--     w  = (1,1,-1),        interior to <v1,v2,v4>.  The star subdivision at w
--                           resolves the 1/2(1,1,1) point, so X1 is smooth.
--     w2 = v2 + v4 = (1,2,-2),  on the facet <v2,v4> of sigma, subdividing
--                           <v2,w,v4> once more.
--
-- X is the resulting smooth threefold, projective over Spec R_0 of relative
-- Picard rank three.  Polarized by H = 4*D_{v4} + D_w + 3*D_{w2}, its wall
-- curves have
--
--     (K.C, H.C) = (-1,1) on <w,w2>,   (-1,2) on <v1,w>,   (0,1) on the rest,
--
-- so the threshold is 1, only <w,w2> attains it, and D_{w2} is what contracts.
-- Nothing is tuned: the program is forced at every step.
--
-- What the configuration is for is what the circuit wall <v1,v2> does.  On X
-- and on X1 that wall is K-trivial -- the resolution's exceptional divisor
-- absorbs the discrepancy -- and it turns K-negative only on Y, once both
-- divisorial steps have happened.  The flip is invisible from the start and
-- appears when the two divisors are gone.
--
-- All four models are subrings of k[a,b,c,t] sharing the degree-zero part
--
--     R_0 = k[b, b^2*c, a, a*b*c, a^2*c] = k[sigma^v cap M],
--
-- each generated over it by the sections of the divisor the previous step hands
-- on.  Every generator has degree zero or one, which is what the Cartier test
-- needs: on a weighted presentation Spec R - V(B) is not a torsor over X and
-- the test over-reports, and Y at its own primitive polarization does need a
-- degree-two generator, so the model below is the second Veronese there.
cox = QQ[a,b,c,t];
baseGenerators = {b, b^2*c, a, a*b*c, a^2*c};
relativeModel = (fibreGenerators,letter) -> (
    n := #fibreGenerators;
    S := QQ[p_1 .. p_5, (getSymbol letter)_1 .. (getSymbol letter)_n,
        Degrees => join(toList(5:0),toList(n:1))];
    S/ker map(cox,S,baseGenerators | fibreGenerators));

X = relativeModel({t, c*t, b*c^2*t, b^2*c^3*t, a*c^2*t, a*b*c^3*t},"q");
groundTruthX1 = relativeModel(
    {a*b*c*t, a*b*c^2*t, a*b^2*c^3*t, a^2*b*c^3*t},"s");
groundTruthY = relativeModel({a^2*b^2*c^2*t, a^2*b^2*c^3*t},"y");
groundTruthZ = relativeModel({b*t, a*t},"z");

assert(dim X - 1 == 3);
assert(sort flatten degrees X == {0,0,0,0,0,1,1,1,1,1,1});
assert(all({groundTruthX1,groundTruthY,groundTruthZ}, R -> dim R - 1 == 3));
-- normality is not asserted by computation here: each of these is the semigroup
-- ring of a saturated affine semigroup -- the generators are the Hilbert basis
-- of {(m,n) : n >= 0, <m,v_i> + n*h_i >= 0} -- and such a ring is normal.  The
-- driver checks it where it needs it, on the two intermediate targets it builds
-- itself, as part of the Stein-factorization certificate.

irrelevantOf = R -> ideal select(flatten entries vars R, q -> (degree q)#0 > 0);
isSmoothOver = R -> (
    singular := saturate(sub(ideal singularLocus R,R),irrelevantOf R);
    singular == ideal 1_R);
curveDegreeData = value(
    MMPComputation#"private dictionary"#"affineCurveDegreeDataInternal");
canonicalDivisorOf = value(
    MMPComputation#"private dictionary"#"mmpCanonicalDivisorInternal");
curveDegrees = (R,a) -> sort apply(
    curveDegreeData(R,canonicalDivisorOf R,
        (weightedAmpleDivisorData R)#"divisor",a),
    entry -> {entry#"canonicalDegree",entry#"ampleDegree"});

-- X is smooth -- every cone of its fan has multiplicity one, which is a fact
-- about the input rather than something to compute: `singularLocus` here would
-- ask for the size-seven minors of a 38 by 11 Jacobian.  What the algorithm
-- needs and what is checked is that K is Cartier, index 1.
assert((canonicalIndexData X)#"index" == 1);
assert(not (canonicalNefData(X,1))#"nef");
-- The three complete curves the search finds in the fibres: one K-negative and
-- two K-trivial.  The K-trivial ones are the point of the configuration -- one
-- of them is the circuit wall, which cannot be contracted while the two extra
-- divisors are there.
assert(curveDegrees(X,1) == {{-1,1},{0,1},{0,1}});
assert(canonicalNefThreshold(X,1) == 1);

<< "OK three-step flip MMP: X has canonical index 1 over the non-Q-Gorenstein "
   << "affine base, one K-negative and two K-trivial fibre curves, and "
   << "threshold 1." << endl;

-- Some degree-preserving relabelling of the variables carries one defining
-- ideal onto the other.
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

-- The whole program, from the ring alone.
mmp = threefoldMMPData(X,1);
assert(mmp#"conclusive");
assert(mmp#"terminationType" == "minimal model");
assert(mmp#"numberOfSteps" == 3);
steps = mmp#"steps";
assert(apply(steps, r -> r#"stepType")
    == {"divisorial","divisorial","flipping"});
assert(all(steps, r -> r#"stepTypeConclusive"));

-- The two divisorial steps go to intermediate targets the driver builds, and
-- their relative canonical models are the identity: a Q-Gorenstein target is
-- its own relative canonical model, and nothing has to be constructed.
assert(not steps#0#"contractionIsSmall");
assert(not steps#1#"contractionIsSmall");
assert(steps#0#"contractionToRelativeTarget");
assert(steps#1#"contractionToRelativeTarget");
assert((steps#0#"relativeModelData")#"isIdentity");
assert((steps#1#"relativeModelData")#"isIdentity");
assert(matchesGroundTruth(steps#0#"nextRing",groundTruthX1));
assert(matchesGroundTruth(steps#1#"nextRing",groundTruthY));

-- The third step is the flip.  Its contraction is small -- exceptional locus of
-- dimension one in a threefold -- it is the structure morphism to the affine
-- base, and its relative canonical model is *not* the identity: this is the one
-- step of the program where Algorithm 4 constructs something.
flipStep = steps#2;
assert(flipStep#"stepType" == "flipping");
assert(flipStep#"contractionIsSmall");
assert(flipStep#"contractionIsStructureMorphism");
assert(not flipStep#"contractionToRelativeTarget");
assert(not (flipStep#"relativeModelData")#"isIdentity");
assert(not (flipStep#"relativeModelData")#"baseIsProjective");
assert(matchesGroundTruth(flipStep#"nextRing",groundTruthZ));

<< "OK three-step flip MMP: threefoldMMPData contracts D_w2, then D_w, then "
   << "flips, and all three targets are the expected models." << endl;

-- The model the program flips is Y, with the 1/2(1,1,1) point the two
-- divisorial steps put back, and its canonical index is 2 rather than 1.
flippingSource = steps#1#"nextRing";
assert((canonicalIndexData flippingSource)#"index" == 2);
assert(not isSmoothOver flippingSource);
assert(canonicalNefThreshold(flippingSource,2) == 1/2);
assert(curveDegrees(flippingSource,2) == {{-1,1}});

-- And the sign of K on the one complete curve flips across the operation, which
-- is what makes this a flip rather than a flop or an isomorphism.  On the way
-- there the count of curves drops by one at each divisorial step.
finalRing = mmp#"finalRing";
assert(finalRing === flipStep#"nextRing");
assert(curveDegrees(steps#0#"nextRing",1) == {{-1,1},{0,1}});
assert(curveDegrees(finalRing,1) == {{1,1}});

-- The flip is a minimal model, checked the driver's way and again from outside,
-- and it is smooth where the model it replaced had the 1/2(1,1,1) point.
assert((mmp#"finalNefData")#"conclusive");
assert((mmp#"finalNefData")#"nef");
assert((canonicalIndexData finalRing)#"index" == 1);
assert((canonicalNefData(finalRing,1))#"nef");
assert(isSmoothOver finalRing);

<< "OK three-step flip MMP: the flipped model is a minimal model -- K nef, "
   << "smooth, and K.C going from -1 to +1 on the one complete curve." << endl;
