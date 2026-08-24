-- -*- coding: utf-8 -*-
if fileExists (currentFileDirectory |
        "third_party/SteinFactorizationM2/SteinFactorization.m2") then (
    needsPackage("SteinFactorization",
        FileName=>currentFileDirectory |
            "third_party/SteinFactorizationM2/SteinFactorization.m2");
    ) else (
    needsPackage "SteinFactorization";
    );
if fileExists (currentFileDirectory |
        "third_party/flip-computation/FlipComputation.m2") then (
    needsPackage("FlipComputation",
        FileName=>currentFileDirectory |
            "third_party/flip-computation/FlipComputation.m2");
    ) else (
    needsPackage "FlipComputation";
    );
newPackage(
    "MMPComputation",
    Version => "0.1.0",
    Date => "12 August 2026",
    HomePage => "https://github.com/takehikoyasuda/Coding_MMP",
    Authors => {{
        Name => "Takehiko Yasuda",
        Email => "yasuda.takehiko.sci@osaka-u.ac.jp"
        }},
    Headline => "computations for the minimal model program in dimension three",
    Keywords => {"Algebraic Geometry"},
    PackageImports => {"WeilDivisors", "SteinFactorization", "FlipComputation"},
    AuxiliaryFiles => false
    )

protect mmpCanonicalIdealSeedData;

export {
    "weightedAmpleDivisorData",
    "effectiveNefMultiplier",
    "isBasePointFreeDivisor",
    "canonicalScaledNefData",
    "canonicalNefThresholdData",
    "canonicalNefThreshold",
    "completeLinearSystemGraphData",
    "completeLinearSystemGraphDataMultigraded",
    "diagonalSubalgebraData",
    "mmpGraphMorphism",
    "contractionTypeData",
    "canonicalContractionAtThresholdData",
    "canonicalContractionData",
    "relativeCanonicalModelFromBaseData",
    "relativeCanonicalModelData",
    "relativeCanonicalModelIsomorphismData",
    "relativeModelInverseRationalMapData",
    "contractionGraphSmallnessData",
    "contractionSmallnessData",
    "mmpStepRecordData",
    "canonicalIndexData",
    "threefoldMMPData",
    "canonicalNefData",
    "isCanonicalNef",
    "NefSearchLimit",
    "ThresholdSearchLimit",
    "ContractionMultipleLimit",
    "RelativeCanonicalMultipliers",
    "RelativeCanonicalMaxMultiplier",
    "RelativeCanonicalVerbose",
    "ContractionIsSmall",
    "CanonicalIndexSearchLimit",
    "MMPMaxSteps",
    "IrrelevantIdeal",
    "DivisorClassDegrees",
    "negativeCurveWitnessData",
    "NegativeCurveSearchLimit"
    }

weilDivisorsPackage := needsPackage "WeilDivisors";
weilDivisorToModule := value(
    weilDivisorsPackage#"private dictionary"#"divisorToModule");

-- research-log/docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md section 6.3: WeilDivisors'
-- mapToProjectiveSpace defends against the D = 0 case (embedAsIdeal's
-- returned degree shift d1 is the zero degree, so the naive map's kernel
-- would be inhomogeneous) by checking only d1#0 == 0, i.e. only the first
-- component of the degree vector. On a multigraded ring (degreeLength > 1)
-- this misfires whenever d1 is a nonzero vector whose first entry happens to
-- be 0 -- observed concretely on a rank-2 toric hypersurface candidate whose
-- threshold divisor has embedding shift d1 = {0,1}: not the zero vector, so
-- the defense should not fire, but it does, and every returned section is
-- multiplied by the ring's first variable. Section counts and the
-- homogeneous kernel are unaffected (the extra factor is common to every
-- section), but the representatives carry an artificial common factor that
-- can fabricate spurious base-locus components and needlessly raise
-- Gröbner-basis degrees downstream.
--
-- mapToProjectiveSpaceInternal reproduces WeilDivisors' mapToProjectiveSpace
-- exactly, replacing the single-component check with an all-components
-- check, so the defense fires only when d1 really is the zero degree
-- vector, in any degreeLength (this also reproduces the original behaviour
-- exactly when degreeLength R = 1, where d1 has a single component).
mapToProjectiveSpaceInternal = method(
    Options => {KnownCartier=>true, Variable=>"YY"});
mapToProjectiveSpaceInternal BasicDivisor := RingMap => o -> D1 -> (
    if not isHomogeneous D1 then
        error "mapToProjectiveSpaceInternal: expected a graded/homogeneous divisor";
    if not o.KnownCartier and not isCartier(D1,IsGraded=>true) then
        error "mapToProjectiveSpaceInternal: expected a Cartier divisor";
    newVar := if instance(o.Variable,Symbol) then o.Variable
        else if instance(o.Variable,String) then getSymbol o.Variable
        else error "mapToProjectiveSpaceInternal: expected option Variable to be a string or a symbol";
    R1 := ring D1;
    -- WeilDivisors' own mapToProjectiveSpace writes this as "prune OO(D1)";
    -- OO(D1) is installed (installMethod(symbol SPACE,OO,RWeilDivisor,...))
    -- as exactly divisorToModule(D1), which weilDivisorToModule already is
    -- (see its definition above). Using it directly here, instead of the raw
    -- OO symbol, also sidesteps an unrelated M2 package-closing check that
    -- rejects any bare reference to the core ScriptedFunctor OO from inside
    -- a newPackage body ("mutable unexported unset symbol(s) ... 'OO'").
    M1 := prune weilDivisorToModule D1;
    L1 := embedAsIdeal(M1,IsGraded=>true);
    d1 := L1#1;
    M1 = L1#0*R1^{d1};
    b1 := super((basis(degree sub(1,R1),M1))**R1);
    n1 := #(first entries b1);
    K1 := coefficientRing R1;
    myMon := monoid[toList(newVar_1..newVar_n1)];
    S1 := K1 myMon;
    varTargetList := first entries b1;
    -- the only change from WeilDivisors' mapToProjectiveSpace: check every
    -- component of d1, not just d1#0, before applying the D = 0 defense.
    isZeroDegree := instance(d1,List) and all(d1,e -> instance(e,Number) and e == 0);
    if isZeroDegree then (
        R1varList := first entries vars R1;
        if #R1varList > 0 then (
            vv := R1varList#0;
            varTargetList = apply(varTargetList,ss -> ss*vv);
            )
        );
    map(R1,S1,varTargetList)
    )

-- Stage 1 (T1) of research-log/docs/STAGE1-MEASUREMENT-PLAN.md: block structure and the
-- irrelevant ideal of a (possibly multigraded) presentation.  Unexported by
-- design -- this is bookkeeping consumed by T2/T3/T5, not a public entry
-- point.
--
-- A presentation is admissible when its degree matrix is block lower
-- triangular with positive diagonal: the variables of block s have degree
-- zero in every component after s and positive degree in component s.  We
-- discover the blocks by scanning, for each variable, the *last* nonzero
-- component of its degree vector (after applying a candidate reordering of
-- the r degree components) and checking that component is positive; if that
-- succeeds for every variable with a consistent block assignment, the
-- reordering witnesses admissibility.  Only permutations of the degree
-- components are tried (not of the variables), matching the plan's
-- "search over permutations of the degree components" instruction; for
-- r = 1 there is exactly one (trivial) permutation, reproducing the
-- monograded case unconditionally: B = ideal vars R.
--
-- Verified against a ring actually produced by bigradedReesProjection (an
-- ideal with generators of unequal degree, so the fibre variables u_i pick
-- up strictly positive degrees in the *base* component): the identity
-- permutation already witnesses admissibility there, contrary to the
-- concern that the returned ambient ring might need the two degree
-- components reversed.  The permutation search is kept regardless, since it
-- is correct and cheap for the r <= 2 case this package needs, and it
-- reports which permutation it used.
multigradedBlockData = method()
multigradedBlockData Ring := R -> (
    A := ambient R;
    n := numgens A;
    avars := flatten entries vars A;
    Rvars := flatten entries vars R;
    if n != #Rvars then
        error "multigradedBlockData: ambient and quotient generator counts disagree";
    r := degreeLength A;
    if r <= 0 then
        error "multigradedBlockData: expected a graded ring";
    -- For a candidate component order (a permutation of 0..r-1), classify
    -- each variable by the last nonzero entry of its reordered degree
    -- vector, and require that entry to be positive.  Returns a list of
    -- 1-indexed block numbers, or null if the order fails some variable.
    tryOrder := perm -> (
        assignment := new MutableList from toList(n:null);
        ok := true;
        scan(n, j -> if ok then (
            dg := degree avars#j;
            reordered := apply(perm, i -> dg#i);
            lastNonzero := 0;
            scan(#reordered, k -> if reordered#k != 0 then lastNonzero = k+1);
            if lastNonzero == 0 or reordered#(lastNonzero-1) <= 0 then
                ok = false
            else assignment#j = lastNonzero;
            ));
        if ok then toList assignment else null
        );
    perms := permutations r;
    assignment := null;
    usedPermutation := null;
    scan(perms, perm -> if assignment === null then (
        candidate := tryOrder perm;
        if candidate =!= null then (
            assignment = candidate;
            usedPermutation = perm;
            );
        ));
    if assignment === null then
        error "multigradedBlockData: not block lower triangular with positive diagonal for any permutation of the degree components";
    blockIndices := apply(r, s0 -> select(n, j -> assignment#j == s0+1));
    if any(blockIndices, idxs -> #idxs == 0) then
        error "multigradedBlockData: a degree component has no variables assigned to it";
    blockVariables := apply(blockIndices, idxs -> apply(idxs, j -> Rvars#j));
    blockIdeals := apply(blockVariables, vs -> ideal vs);
    B := product blockIdeals;
    -- The "last nonzero component, must be positive" test above only checks
    -- that the winning permutation's assignment is block LOWER TRIANGULAR
    -- (docs/MULTIGRADED-DESIGN.md's admissibility condition), which allows a
    -- variable's degree to be nonzero in components strictly before its own
    -- block.  That is by design -- a Rees algebra's own added block does
    -- this -- but it also means two variables that are geometrically part of
    -- the SAME block (e.g. the same fibre) can get shuffled into different
    -- blocks here purely because one of them happens to have an extra
    -- nonzero lower-order degree component (a "skew" degree) and the other
    -- does not.  This is exactly the defect tests/multigraded-skew-cartier.m2
    -- pins down: the permutation search above still succeeds and returns a
    -- self-consistent-looking B, but B's radical need not match the ring's
    -- true irrelevant ideal.  "verifiedBlockDiagonal" records whether every
    -- variable's winning-permutation degree vector has exactly one nonzero
    -- entry (true block DIAGONAL, not merely lower triangular); it is the
    -- one case where no such shuffling is possible, since each variable's
    -- degree pins down its block on its own with no other component to
    -- disagree about.  Callers that cannot supply their own known-correct
    -- irrelevant ideal should treat "irrelevantIdeal" as trustworthy only
    -- when this flag is true; see verifiedIrrelevantIdeal below.
    reorderedDegrees := apply(n, j -> apply(usedPermutation, i -> (degree avars#j)#i));
    verifiedBlockDiagonal := all(reorderedDegrees, dg -> #select(dg, x -> x != 0) == 1);
    new HashTable from {
        "ring" => R,
        "rank" => r,
        "permutation" => usedPermutation,
        "blockAssignment" => assignment,
        "blockVariableIndices" => blockIndices,
        "blockVariables" => blockVariables,
        "blockIdeals" => blockIdeals,
        "irrelevantIdeal" => B,
        "geometricDimension" => dim R - r,
        "verifiedBlockDiagonal" => verifiedBlockDiagonal
        }
    )

-- The irrelevant ideal to trust for R: a caller-supplied B (Ideal or null)
-- always wins.  Failing that, multigradedBlockData's own guess is used only
-- when it is "verifiedBlockDiagonal" -- i.e. no variable has a skew (mixed-
-- component) degree that its block-classification heuristic could get wrong
-- (see the comment on that field above, and tests/multigraded-skew-
-- cartier.m2 for a concrete ring where the heuristic succeeds but returns an
-- ideal with the wrong radical).  On a skew ring with no caller-supplied B,
-- this refuses to guess and errors instead, matching SteinFactorization's
-- own fail-fast behaviour on inputs its stricter block-diagonal convention
-- cannot classify, rather than silently returning a possibly-wrong ideal.
verifiedIrrelevantIdeal = (R,suppliedB) -> (
    if suppliedB =!= null then suppliedB
    else (
        bd := multigradedBlockData R;
        if not bd#"verifiedBlockDiagonal" then error(
            "verifiedIrrelevantIdeal: this ring has a skew (mixed-degree) "
            | "multigraded variable, so multigradedBlockData's block-"
            | "classification heuristic cannot reliably determine the "
            | "irrelevant ideal (it can return one with the wrong radical; "
            | "see tests/multigraded-skew-cartier.m2).  Supply the ring's "
            | "true irrelevant ideal explicitly, e.g. via IrrelevantIdeal=>B "
            | "or the (BasicDivisor,B2MProjection)/(BasicDivisor,GraphMorphism) "
            | "overloads.");
        bd#"irrelevantIdeal"
        )
    )

-- Lemma 3.6 of the paper: if X is presented in a weighted projective space
-- with coordinate weights c_i and l=lcm(c_i), then O_X(l) is ample and
-- invertible.  A nonzero coordinate power of weighted degree l supplies an
-- effective Cartier representative H.
weightedAmpleDivisorData = method()
weightedAmpleDivisorData Ring := R -> (
    S := ambient R;
    if degreeLength S != 1 then
        error "weightedAmpleDivisorData: expected a singly graded ring";
    ambientVars := flatten entries vars S;
    weights := apply(ambientVars,q -> (degree q)#0);
    if any(weights,c -> c <= 0) then
        error "weightedAmpleDivisorData: all coordinate weights must be positive";
    ell := 1;
    scan(weights,c -> ell = lcm(ell,c));
    candidates := select(#ambientVars,i -> sub(ambientVars#i,R) != 0);
    if #candidates == 0 then
        error "weightedAmpleDivisorData: every coordinate vanishes on X";
    coordinateIndex := first candidates;
    coordinate := sub(ambientVars#coordinateIndex,R);
    section := coordinate^(ell // weights#coordinateIndex);
    H := divisor section;
    new HashTable from {
        "ring" => R,
        "weights" => weights,
        "cartierDegree" => ell,
        "coordinateIndex" => coordinateIndex,
        "section" => section,
        "divisor" => H
        }
    )

-- Proposition 3.1: the effective base-point-free multiplier for
-- L=N(K_X+tH).  The improved threefold bound is ceil(2/N)+5, giving
-- 7 for N=1 and 6 for N>=2.  For other dimensions keep the older
-- Fujino/Kollar-type bound used by the paper revision this package pins.
effectiveNefMultiplier = method()
effectiveNefMultiplier (ZZ,ZZ) := (d,N) -> (
    if d < 0 then error "effectiveNefMultiplier: dimension must be nonnegative";
    if N <= 0 then error "effectiveNefMultiplier: N must be positive";
    if d == 3 then return ceiling(2/N)+5;
    2^(d+1) * (d+1)! * (ceiling(2/N) + d)
    )

-- Stage 1 (T2): saturated versions of the two WeilDivisors predicates
-- diagnosed in research-log/docs/STAGE1-MEASUREMENT-PLAN.md section 3.  Both compare a
-- cone ideal with the unit ideal; that comparison is only correct when the
-- irrelevant ideal is the maximal ideal, i.e. r = 1.  Multigraded, the cone
-- ideal must be saturated against B = B_1*...*B_r (T1) first.
--
-- Fast path for the common Cox-coordinate case.  If
--
--   D = sum_i c_i div(f_i)
--
-- with each support prime visibly equal to a homogeneous principal ideal
-- (f_i), then the corresponding sheaf on Proj is the free graded shift with
-- shift degree sum_i c_i*degree(f_i).  This is a certificate-producing
-- optimization: failure to recognize that form returns null and leaves the
-- general WeilDivisors construction unchanged.  In particular, this helper
-- does not infer Cartierness from an expensive or incomplete test.
principalHomogeneousShiftDegreeInternal = D -> (
    if not instance(D,WeilDivisor) then return null;
    R := ring D;
    if not isHomogeneous D then return null;
    n := degreeLength R;
    delta := toList(n : 0);
    P := primes D;
    C := coefficients D;
    ok := true;
    scan(getPrimeCount D, i -> if ok then (
        Pi := trim(P#i);
        if numgens Pi != 1 then ok = false
        else (
            gi := first entries gens Pi;
            if #gi != 1 or not isHomogeneous(gi#0) then ok = false
            else (
                di := degree(gi#0);
                if #di != n then ok = false
                else delta = apply(n,j -> delta#j + (C#i)*(di#j));
                )
            )
        ));
    if ok then delta else null
    )

principalHomogeneousShiftModule = D -> (
    R := ring D;
    delta := principalHomogeneousShiftDegreeInternal D;
    if delta === null then null else R^{delta}
    )

-- A Cartier H may be presented as a sum of principal divisors whose support
-- primes are not themselves principal in the quotient.  If its module is
-- nevertheless visibly a single homogeneous shift, recover the class degree
-- from the opposite sign of that module generator degree.  This is a cheap
-- fallback used only for H; K never goes through this route.
cartierClassDegreeInternal = H -> (
    d := principalHomogeneousShiftDegreeInternal H;
    if d =!= null then return d;
    M := null;
    try M = prune weilDivisorToModule H else return null;
    ds := degrees M;
    if #ds != 1 then return null;
    -first ds
    )

-- Build the same graded free module from a caller-supplied divisor-class
-- degree.  The extra list wrapper is required by M2 for one multidegree.
gradedShiftModuleFromDegree = (R,d) -> (
    shifts := {d};
    R^shifts
    )

-- Construct one canonical ideal together with the degree of the homogeneous
-- embedding omega_R -> R.  If I is the image of that embedding, then
--
--     O_X(mK_X+bH) ~= reflexivePower(m,I) ** R^{m*e+b*h}
--
-- whenever H is visibly principal of class degree h.  This replaces m
-- repeated module double-duals by one canonical-module Ext/Hom computation
-- plus ideal reflexive powers.  The data are cached on K because the nef
-- search asks for several multipliers of the same canonical divisor.
canonicalIdealSeedDataInternal = (R,K) -> (
    if instance(K,WeilDivisor) and K#cache#?mmpCanonicalIdealSeedData then
        return K#cache#mmpCanonicalIdealSeedData;
    S := ambient R;
    sourceVars := flatten entries vars S;
    degreeList := if degreeLength S == 1
        then apply(sourceVars,q -> (degree q)#0)
        else apply(sourceVars,q -> degree q);
    omegaShift := if degreeLength S == 1
        then -sum degreeList
        else -(sum degreeList);
    omegaShiftList := if degreeLength S == 1
        then {{omegaShift}}
        else {omegaShift};
    omegaShiftModule := S^omegaShiftList;
    omega := (Ext^(dim S-dim R)(S^1/(ideal R),omegaShiftModule)) ** R;
    dualOmega := Hom(omega,R^1);
    if numgens dualOmega == 0 then return null;
    -- Which generator of Hom(omega,R^1) is chosen matters enormously: an
    -- arbitrary generator can embed omega_R at a much higher degree than
    -- necessary, and the resulting ideal's generators (hence every downstream
    -- trim/reflexivePower call) inherit that degree.  third_party/flip-
    -- computation/FlipComputation/divisors.m2's canonicalIdeal already solved
    -- this for the monograded case (its own comment: "the whole computation
    -- drops from 'unfinished after seventeen minutes' to a twentieth of a
    -- second" from this alone) by picking the least-degree generator instead
    -- of an arbitrary one; this generalizes that choice to the multigraded
    -- case via sum-of-multidegree as the comparison key (identical to their
    -- criterion when degreeLength = 1).
    degreeSums := apply(numgens dualOmega, i -> sum (degrees dualOmega)#i);
    bestIndex := minPosition degreeSums;
    embeddingDegree := (degrees dualOmega)#bestIndex;
    embedding := homomorphism dualOmega_bestIndex;
    canonicalIdeal := trim ideal matrix embedding;
    if canonicalIdeal == ideal 0_R then return null;
    result := new HashTable from {
        "ring" => R,
        "ideal" => canonicalIdeal,
        "embeddingDegree" => embeddingDegree,
        "certificate" => "canonical module Ext/Hom embedding and ideal reflexive powers"
        };
    if instance(K,WeilDivisor) then
        K#cache#mmpCanonicalIdealSeedData = result;
    result
    )

-- Return null when the chart/principal hypotheses needed for this shortcut
-- are unavailable.  A non-null result is an exact BPF test under the normal
-- domain hypotheses already required by canonicalDivisor/reflexivePower.
canonicalIdealSeedBPFInternal = (R,K,kCoeff,hCoeff,H,B) -> (
    if kCoeff <= 0 then return null;
    hDegree := if hCoeff == 0
        then toList(degreeLength R : 0)
        else cartierClassDegreeInternal H;
    if hDegree === null then return null;
    seed := canonicalIdealSeedDataInternal(R,K);
    if seed === null then return null;
    answer := null;
    try (
        powerIdeal := reflexivePower(kCoeff,seed#"ideal");
        shiftedModule := (powerIdeal*R^1) **
            R^{kCoeff*(seed#"embeddingDegree") + hCoeff*hDegree};
        answer = basePointFreeModuleInternal(shiftedModule,B);
        ) else answer = null;
    answer
    )

-- Sufficient (not necessary) certificate that D is Cartier: if every support
-- prime of D is visibly homogeneous principal, O(D) is literally the free
-- rank-1 module principalHomogeneousShiftModule(D), hence Cartier
-- unconditionally -- no irrelevant ideal, no Hom/Ext call of any kind.
-- Returns a definite boolean only in the affirmative; use null (via the
-- caller's own dispatch) rather than false when the hypothesis fails, since
-- failing this cheap test says nothing about whether D is actually Cartier.
principalShiftCartierCertificateInternal = D ->
    principalHomogeneousShiftDegreeInternal D =!= null

-- Sufficient (not necessary) certificate that kCoeff*K is Cartier, found
-- while root-causing the canonicalIndexData/isCartier bottleneck (see
-- research-log/docs/CARTIER-INDEX-FASTPATH-AND-CYCLIC-COVER-INVESTIGATION.md):
-- if the kCoeff-th reflexive power
-- of the cached canonical-ideal seed (canonicalIdealSeedDataInternal) is
-- itself principal (a single generator after trim), the corresponding
-- module is free of rank 1, so kCoeff*K is Cartier -- again unconditionally,
-- via only reflexivePower and trim, no Hom(dualModule,R^1) double dual.
-- Returns null (meaning "unknown, fall back to a general test"), never
-- false, when the seed is unavailable or the power is not visibly
-- principal: not being visibly principal does not certify non-Cartier-ness.
canonicalIdealSeedInvertibleInternal = (R,K,kCoeff) -> (
    if kCoeff <= 0 then return null;
    seed := canonicalIdealSeedDataInternal(R,K);
    if seed === null then return null;
    answer := null;
    try (
        powerIdeal := trim reflexivePower(kCoeff,seed#"ideal");
        answer = (numgens powerIdeal == 1);
        ) else answer = null;
    answer
    )

-- BPF holds iff the degree-zero sections generate M away from V(B), i.e. iff
-- the cokernel of their evaluation map is killed by some power of B.  The
-- previous implementation tested this via
--     trim saturate(ann coker basis(zeroDegree,M),B) == ideal 1_R
-- which materializes ann(coker) as a standalone ideal of R before saturating
-- it -- on inputs where the degree-zero section space is large (e.g.
-- Xnatural, a non-toric cyclic-cover ring where H is not visibly principal
-- so no fastpath narrows the section space), that raw ann ideal can have
-- thousands of generators before trim (measured: 75/323/1859/12675 as the
-- section-space dimension itself grows), making both the ann computation and
-- the subsequent saturate expensive.
--
-- These two conditions are exactly equivalent, not merely similar: for
-- f: F -> M with N = image f,
--     saturate(ann(coker f),B) == R
--     <=> B^k subset ann(M/N) for some k       (definition of saturate)
--     <=> B^k * M subset N for some k          (definition of ann(M/N))
--     <=> M subset (N : B^k) for some k
--     <=> M == saturate(N,B)                   (N subset M always)
-- so testing "does the submodule generated by the sections saturate (by B)
-- to all of M" answers the identical question without ever forming ann(coker)
-- as a separate ideal.  Measured ~4.9x faster on Xnatural's 1859-generator
-- case (memory module-saturate-bypasses-ann-bottleneck), same answer in
-- every case tested (including the h^0 = 0 case, where the image is the zero
-- submodule and correctly fails to saturate to M).
basePointFreeModuleInternal = (M,B) -> (
    R := ring M;
    zeroDegree := toList(degreeLength R : 0);
    sections := basis(zeroDegree,M);
    saturate(image sections,B) == M
    )

-- isBasePointFreeDivisorInternal does NOT call WeilDivisors' baseLocus.  A
-- second, separate defect was found while testing the plan's stated fix
-- (saturating baseLocus's own output): baseLocus(Module) computes
-- "basis(0,M1)" with a bare integer, and on a ring with degreeLength > 1
-- that call does not reliably select the degree (0,...,0) piece of M1 -- it
-- can silently return a nonempty (wrong) answer where the correct
-- multidegree query basis(toList(r:0),M1) returns empty.  Confirmed
-- concretely: on bigraded P1xP2, for L = K+2H = O(0,-1) (which has no
-- sections at all, so is certainly not base-point-free), baseLocus(L)
-- already evaluates to ideal 1_R before any saturation is applied, purely
-- from this basis(0,-) defect, so saturating its output by B (as the plan's
-- 3.1 fix literally states) cannot recover correctness.  This is
-- independent of, and in addition to, the "compare with the wrong
-- irrelevant ideal" defect the plan diagnosed; the plan's own verified
-- examples (Div(s), -K) happen not to trigger it because both are
-- effective with a generator degree under which the bare-integer and
-- explicit-multidegree calls happen to agree.
--
-- The fix used here instead builds the evaluation cokernel directly with an
-- explicit full-length zero degree vector (matching
-- BOTTLENECKS-AND-MULTIGRADING.md's "Promising direction" item 4: test
-- base-point-freeness from the evaluation cokernel in the multigraded
-- module category, not via a monograded shortcut), then saturates by B
-- ourselves; WeilDivisors' own default saturation (against the monograded
-- maximal ideal) is bypassed entirely rather than only being supplemented,
-- since it cannot be relied on either way.  Confirmed by test to reproduce
-- the current predicate exactly for r = 1 (P3's O(1) and K+4H=O; the
-- weighted P(1,1,1,2) degree-2 ample class), so this is behaviour-preserving
-- for every existing (monograded) caller, and additionally correct on the
-- h^0 = 0 case above where the plan's literal fix is not.
isBasePointFreeDivisorInternal = (D,B) -> (
    R := ring D;
    -- A sum of homogeneous principal prime divisors has a certified Cox
    -- degree.  In that case O(D) is the corresponding free graded shift and
    -- constructing it does not require WeilDivisors' reflexive double dual.
    -- The helper returns null unless every support prime is visibly principal
    -- and homogeneous, so non-principal/non-Cartier divisors keep the exact
    -- historical construction below.
    M := principalHomogeneousShiftModule D;
    if M === null then M = weilDivisorToModule D;
    basePointFreeModuleInternal(M,B)
    )

isBasePointFreeDivisor = method()
isBasePointFreeDivisor BasicDivisor := D ->
    isBasePointFreeDivisorInternal(D,verifiedIrrelevantIdeal(ring D,null))

-- Stage 2 (T1) of docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md section 5: give a
-- caller holding a known-correct irrelevant ideal a way to bypass
-- multigradedBlockData's re-derivation entirely.  Verified necessary, not
-- hypothetical: on the bigraded ring Z of that plan's section 3 (the toric
-- flip target of canonical index 2), multigradedBlockData Z succeeds but
-- returns a B with a different radical from the ring's true irrelevant
-- ideal (P#irrelevantIdeal on the B2MProjection P that built Z), because Z's
-- fibre grading is "skew" -- see tests/multigraded-skew-cartier.m2.  These
-- overloads do not change multigradedBlockData or the plain BasicDivisor
-- overload above at all; they are purely additive.
isBasePointFreeDivisor (BasicDivisor,Ideal) := (D,B) ->
    isBasePointFreeDivisorInternal(D,B)
isBasePointFreeDivisor (BasicDivisor,B2MProjection) := (D,P) ->
    isBasePointFreeDivisorInternal(D,sub(P#irrelevantIdeal,ring D))
isBasePointFreeDivisor (BasicDivisor,GraphMorphism) := (D,G) ->
    isBasePointFreeDivisorInternal(D,sub(G#irrelevantIdeal,ring D))

-- 3.2's fix, kept as a separate (unexported) predicate rather than an
-- override of WeilDivisors' isCartier: isCartier(D,IsGraded=>true) is
-- hard-wired, inside nonCartierLocus's own IsGraded branch, to
-- getIrrelevantIdeal(R), the monograded maximal ideal, so it cannot be
-- corrected by an option and is not touched here.  Existing callers of
-- isCartier are therefore unaffected; new multigraded entry points (T3, T5)
-- call this instead.  nonCartierLocus only has a WeilDivisor method, so a
-- BasicDivisor/RWeilDivisor argument is converted first.
isCartierSaturatedInternal = (D,B) -> (
    R := ring D;
    WD := if instance(D,WeilDivisor) then D else toWeilDivisor D;
    if not isHomogeneous WD then
        error "isCartierSaturatedInternal: expected a homogeneous divisor";
    J := nonCartierLocus(WD,IsGraded=>true);
    trim saturate(J,B) == ideal 1_R
    )

-- Converted from a plain closure to a method (Stage 2 T1) solely to admit
-- the caller-supplied-B overloads below; isCartierMultigraded(D) alone is
-- unchanged behaviour for every existing (unexported, internal-only) caller
-- -- grep confirms it has none in this package or tests/, only mentions in
-- research-log/docs/STAGE1-MEASUREMENT-RESULTS.md's prose.
isCartierMultigraded = method()
isCartierMultigraded BasicDivisor := D ->
    isCartierSaturatedInternal(D,verifiedIrrelevantIdeal(ring D,null))
isCartierMultigraded (BasicDivisor,Ideal) := (D,B) ->
    isCartierSaturatedInternal(D,B)
isCartierMultigraded (BasicDivisor,B2MProjection) := (D,P) ->
    isCartierSaturatedInternal(D,sub(P#irrelevantIdeal,ring D))
isCartierMultigraded (BasicDivisor,GraphMorphism) := (D,G) ->
    isCartierSaturatedInternal(D,sub(G#irrelevantIdeal,ring D))

-- Search the projective components of a base locus for a curve on which D
-- has negative degree.  Components of dimension greater than one are cut by
-- deterministic coordinate hyperplanes until curves remain.  For a Cartier
-- divisor, the constant difference
--
--   HP(O(D)|_C) - HP(O_C)
--
-- is deg(D|_C).  A negative value is therefore an unconditional non-nef
-- certificate; failure to find one says nothing and the effective theorem
-- test must continue.
negativeBaseLocusCurveData = (D,B) -> (
    R := ring D;
    S := ambient R;
    if degreeLength S != 1
        or any(flatten entries vars S,x -> degree x != {1}) then return null;
    irrelevant := ideal vars R;
    projectiveBaseLocus := trim saturate(B,irrelevant);
    if projectiveBaseLocus == ideal 1_R then return null;
    components := minimalPrimes projectiveBaseLocus;
    coordinates := flatten entries vars R;
    curves := {};
    scan(components,P -> (
        pieces := {P};
        while any(pieces,Q -> dim(R/Q)-1 > 1) do (
            nextPieces := {};
            scan(pieces,Q -> (
                componentDimension := dim(R/Q)-1;
                if componentDimension <= 1 then
                    nextPieces = append(nextPieces,Q)
                else (
                    cuttingCoordinate := first select(coordinates,x -> x % Q != 0);
                    cutIdeal := trim saturate(Q+ideal cuttingCoordinate,irrelevant);
                    nextPieces = join(nextPieces,minimalPrimes cutIdeal);
                    );
                ));
            pieces = unique nextPieces;
            );
        curves = join(curves,select(pieces,Q -> dim(R/Q)-1 == 1));
        ));
    witness := null;
    scan(unique curves,C -> if witness === null then (
        curveModule := coker gens C;
        restriction := (weilDivisorToModule D) ** curveModule;
        regularityBound := max(regularity curveModule,regularity restriction);
        degree0 := hilbertFunction(regularityBound,restriction)
            - hilbertFunction(regularityBound,curveModule);
        degree1 := hilbertFunction(regularityBound+1,restriction)
            - hilbertFunction(regularityBound+1,curveModule);
        if degree0 == degree1 and degree0 < 0 then
            witness = new HashTable from {
                "curveIdeal" => C,
                "intersection" => degree0,
                "hilbertPolynomialDifference" =>
                    hilbertPolynomial restriction-hilbertPolynomial curveModule,
                "baseLocus" => projectiveBaseLocus
                };
        ));
    witness
    )

-- Iterated multigrading, Phase 4 idea (research-log/docs/ITERATED-MULTIGRADING-MMP-PLAN.md
-- section "Stein factorization との境界" and the 2026-08-15 discussion of
-- cheaper non-nef certificates): the multigraded generalization of
-- negativeBaseLocusCurveData above.  That function is hardcoded to
-- degreeLength(ambient R) == 1 (see its guard clause) because it leans on
-- Castelnuovo-Mumford regularity and hilbertFunction with a bare integer
-- degree, both single-graded notions.  Rediscovering the same "constant
-- Hilbert-polynomial difference along a curve is deg(D|_C)" certificate in a
-- genuinely multigraded (rank r) presentation turns out not to need any
-- regrading of the ambient ring at all: hilbertFunction accepts a full
-- multidegree (a length-r list), so probing along the ray n*h for the
-- caller's own ample class's multidegree h = (h_1,...,h_r) and watching the
-- difference stabilize as n grows plays exactly the same role that
-- regularity played in the single-graded version.  Verified concretely
-- (2026-08-15) on bigraded P1xP2 with the known witness curve C =
-- {pt}x{line in P2} and D = K+2H = O(0,-1): hilbertFunction(n*{1,1},-) gives
-- a difference of exactly -1 for every n = 1..6 tested, matching the known
-- deg(O(0,-1)|_C) = -1 -- no newRing/diagonal-subalgebra reduction needed.
--
-- h is taken as an explicit argument (not read off of an ample WeilDivisor)
-- because this package's WeilDivisor type has no degree method at all --
-- confirmed while designing this function, not assumed -- so a caller who
-- already built its ample class from specific homogeneous elements already
-- knows h and should simply pass it, rather than this function guessing.
--
-- Stabilization is a search (increase n until two consecutive values of the
-- difference agree), not a closed-form bound the way regularity is; this is
-- honestly a heuristic, exactly as the coordinate-hyperplane curve-cutting
-- above already is, and NegativeCurveSearchLimit bounds it.  A search that
-- exhausts the limit without stabilizing returns null (no witness), never a
-- wrong answer: this function only ever asserts a certificate once it has
-- actually observed the constant difference, mirroring the "failure to find
-- one says nothing" discipline of the single-graded version.
negativeCurveWitnessData = method(Options => {NegativeCurveSearchLimit => 8})
negativeCurveWitnessData (BasicDivisor,Ideal,Ideal,List) := o -> (D,candidateBaseLocus,B,h) -> (
    R := ring D;
    if ring candidateBaseLocus =!= R then
        error "negativeCurveWitnessData: candidateBaseLocus must be an ideal of ring D";
    if ring B =!= R then
        error "negativeCurveWitnessData: B must be an ideal of ring D";
    r := degreeLength R;
    if #h != r then
        error "negativeCurveWitnessData: h must have degreeLength R entries";
    limit := o.NegativeCurveSearchLimit;
    if not instance(limit,ZZ) or limit <= 0 then
        error "negativeCurveWitnessData: NegativeCurveSearchLimit must be a positive integer";
    projectiveBaseLocus := trim saturate(candidateBaseLocus,B);
    if projectiveBaseLocus == ideal 1_R then return null;
    components := minimalPrimes projectiveBaseLocus;
    coordinates := flatten entries vars R;
    curves := {};
    scan(components,P -> (
        pieces := {P};
        while any(pieces,Q -> dim(R/Q)-r > 1) do (
            nextPieces := {};
            scan(pieces,Q -> (
                componentDimension := dim(R/Q)-r;
                if componentDimension <= 1 then
                    nextPieces = append(nextPieces,Q)
                else (
                    -- Rank r > 1: unlike the monograded case, cutting with
                    -- the first available coordinate is not safe -- if that
                    -- coordinate shares a block with one already used, the
                    -- cut ideal can reconstruct an entire irrelevant-ideal
                    -- block (a locus already excluded from Proj) rather than
                    -- a genuine lower-dimensional piece, silently saturating
                    -- to the unit ideal.  Concretely reproduced on bigraded
                    -- P1xP2 (2026-08-15): cutting {s} then {t} (both degree
                    -- (1,0)) recreates exactly the block ideal (s,t) and
                    -- saturates away to nothing, even though the genuine
                    -- witness curve {pt in P1}x{line in P2} = (s,u) is found
                    -- immediately by preferring a coordinate from the other
                    -- block.  So try candidates in the given order and skip
                    -- any that collapse the cut to the unit ideal, rather
                    -- than committing to the first one unconditionally.
                    candidates := select(coordinates,x -> x % Q != 0);
                    cutIdeal := null;
                    scan(candidates,x -> if cutIdeal === null then (
                        candidate := trim saturate(Q+ideal x,B);
                        if candidate != ideal 1_R then cutIdeal = candidate;
                        ));
                    if cutIdeal =!= null then
                        nextPieces = join(nextPieces,minimalPrimes cutIdeal);
                    );
                ));
            pieces = unique nextPieces;
            );
        curves = join(curves,select(pieces,Q -> dim(R/Q)-r == 1));
        ));
    DModule := weilDivisorToModule D;
    witness := null;
    scan(unique curves,Q -> if witness === null then (
        curveModule := coker gens Q;
        restriction := DModule ** curveModule;
        n := 1;
        current := hilbertFunction(n*h,restriction) - hilbertFunction(n*h,curveModule);
        stabilized := false;
        while not stabilized and n < limit do (
            previous := current;
            n = n+1;
            current = hilbertFunction(n*h,restriction) - hilbertFunction(n*h,curveModule);
            if current == previous then stabilized = true;
            );
        if stabilized and current < 0 then
            witness = new HashTable from {
                "curveIdeal" => Q,
                "intersection" => current,
                "stabilizedAt" => n,
                "baseLocus" => projectiveBaseLocus
                };
        ));
    witness
    )

-- Normalize integration-layer and Stein graph tables to the GraphMorphism
-- representation used by FlipComputation.  Legacy tables remain accepted at
-- package boundaries, but all newly returned MMP morphism graphs use this type.
mmpGraphMorphism = method()
mmpGraphMorphism GraphMorphism := graph -> graph
mmpGraphMorphism HashTable := graph -> (
    P := if graph#?"jointRing" then graph#"jointRing"
        else if graph#?"productRing" then graph#"productRing"
        else error "mmpGraphMorphism: missing joint or product ring";
    if not graph#?"graphIdeal" or not graph#?"sourceVariableCount"
        or not graph#?"sourceRing" or not graph#?"targetRing" then
        error "mmpGraphMorphism: incomplete graph table";
    J := graph#"graphIdeal";
    if ring J =!= P then
        error "mmpGraphMorphism: graph ideal belongs to the wrong ring";
    ns := graph#"sourceVariableCount";
    if ns <= 0 or ns >= numgens P then
        error "mmpGraphMorphism: invalid source variable count";
    sourceCoordinateRing := graph#"sourceRing";
    targetCoordinateRing := graph#"targetRing";
    if numgens ambient sourceCoordinateRing != ns then
        error "mmpGraphMorphism: source coordinate count does not match its block";
    if numgens ambient targetCoordinateRing != numgens(P)-ns then
        error "mmpGraphMorphism: target coordinate count does not match its block";
    if dim(P/J)-2 != dim(sourceCoordinateRing)-1 then
        error "mmpGraphMorphism: graph and source dimensions do not match";
    allVariables := flatten entries vars P;
    sourceVariables := take(allVariables,ns);
    targetVariables := drop(allVariables,ns);
    new GraphMorphism from {
        ambientRing => P,
        definingIdeal => J,
        totalRing => P/J,
        sourceRing => sourceCoordinateRing,
        baseCoordinateRing => targetCoordinateRing,
        fiberVariables => sourceVariables,
        baseVariables => targetVariables,
        irrelevantIdeal => ideal flatten apply(sourceVariables,y ->
            apply(targetVariables,x -> y*x))
        }
    )

-- Stage 2 (T1, completing Stage 1's T1/T3): the trailing B argument is the
-- known-correct irrelevant ideal (an Ideal, or null), threaded through from
-- whichever entry point built this call.  This is genuinely completing
-- Stage 1's T1/T3, not new Stage 2 work: research-log/docs/STAGE1-MEASUREMENT-PLAN.md's
-- T1 already anticipated "prefer [a provenance] irrelevantIdeal field over
-- recomputing", but no caller-supplied-B entry point threaded that value
-- into this function's OWN base-point-free tests below -- every one of them
-- called the bare 1-argument isBasePointFreeDivisor, which re-derives B via
-- multigradedBlockData internally regardless of what a caller passed to the
-- outer entry point.  On a skew multigraded ring (docs/STAGE2-SINGULAR-
-- MEASUREMENT-PLAN.md section 2.3), that re-derivation is silently wrong, so
-- the outer Cartier gate could be correct while this search loop's own
-- "nef"/"basePointFree" verdict was not.  B = null reproduces the previous
-- behaviour (re-derive via multigradedBlockData) exactly, so every existing
-- caller that does not pass B is completely unaffected.
canonicalScaledNefDataInternal = (R,K,H,a,t,B,classDegrees) -> (
    if t <= 0 then
        error "canonicalScaledNefData: t must be a positive rational number";
    p := if instance(t,ZZ) then t else numerator t;
    q := if instance(t,ZZ) then 1 else denominator t;
    -- Stage 1 (T3): the geometric dimension of a rank-r presentation is
    -- dim R - r, not dim R - 1 (plan section 3.4); multigradedBlockData (T1)
    -- computes exactly this formula (dim R - degreeLength ambient R) as its
    -- "geometricDimension" field, but only after first successfully deriving
    -- a full block decomposition of the irrelevant ideal -- work this line
    -- does not need and, found this session, cannot always get: a genuinely
    -- non-block-decomposable multigraded ring (e.g. a VGIT/Cox-ring chamber
    -- whose irrelevant ideal is not a product of per-degree-component block
    -- ideals -- see research-log/docs/COMPACT-TORIC-FLIP-FAN-CONSTRUCTION-REPORT.md's
    -- chamber B) makes multigradedBlockData error out unconditionally, even
    -- when the caller has already supplied a correct B above and needs
    -- nothing else from multigradedBlockData here.  Computing the same
    -- arithmetic directly removes that unnecessary and, for such rings,
    -- fatal dependency; behaviour is unchanged for every existing (block-
    -- decomposable or monograded) caller since the formula is identical.
    d := dim R - degreeLength R;
    N := a*q;
    L := q*a*K + a*p*H;
    guaranteedMultiplier := effectiveNefMultiplier(d,N);
    -- A base-point-free positive multiple already proves that L is nef.  In
    -- the improved threefold case the guaranteed multiplier is at most 7, so
    -- simply test all multiples up to it.  For the older high-dimensional
    -- fallback, keep the negative-curve search as an optional shortcut before
    -- jumping to the guaranteed multiplier.
    trialBound := min(8,guaranteedMultiplier);
    useNegativeCurveShortcut := guaranteedMultiplier > trialBound;
    -- This flag is false whenever d = 3: effectiveNefMultiplier(3,N) is
    -- ceiling(2/N)+5 <= 7 for every N >= 1, so guaranteedMultiplier <= 7 = 8
    -- always makes trialBound = guaranteedMultiplier and the shortcut branch
    -- below dead code.  Every entry point in this package that reaches d = 3
    -- (canonicalNefData's own threefold gate) therefore never executes it;
    -- confirmed by test (tests/multigraded-skew-cartier.m2) rather than
    -- assumed, since canonicalScaledNefDataInternal has no dimension-3 gate
    -- of its own and a caller outside this package's own entry points could
    -- in principle reach it at d != 3.  It is threaded with the same B below
    -- regardless, since doing so is free and keeps the two branches equally
    -- correct.
    trialMultipliers := toList(1..trialBound);
    if useNegativeCurveShortcut then
        trialMultipliers = append(trialMultipliers,guaranteedMultiplier);
    multipliersTested := {};
    multiplier := null;
    testDivisor := null;
    bpf := false;
    negativeCurveWitness := null;
    scan(trialMultipliers,m -> if multiplier === null then (
        candidateDivisor := m*L;
        candidateBaseLocus := null;
        candidateBPF := false;
        candidateModule := null;
        if classDegrees =!= null then (
            candidateDegree := q*a*(classDegrees#0)
                + a*p*(classDegrees#1);
            candidateModule = gradedShiftModuleFromDegree(
                R,m*candidateDegree);
            );
        if useNegativeCurveShortcut then (
            candidateBaseLocus = trim baseLocus candidateDivisor;
            candidateBPF = if B =!= null
                then trim saturate(candidateBaseLocus,B) == ideal 1_R
                else candidateBaseLocus == ideal 1_R;
        )
        else if candidateModule =!= null then
            candidateBPF = if B =!= null
                then basePointFreeModuleInternal(candidateModule,B)
                else basePointFreeModuleInternal(candidateModule,
                    verifiedIrrelevantIdeal(R,null))
        else (
            -- When no class-degree certificate was supplied, use the
            -- canonical-ideal seed if H is visibly principal.  This tests
            -- the complete degree-zero section space of the exact
            -- reflexivePower ideal, so a false result is not accepted from
            -- a mere subset of sections; unavailable/failed seed data fall
            -- back to the historical divisorToModule path.
            seedBPF := canonicalIdealSeedBPFInternal(
                R,K,m*q*a,a*p,H,
                if B =!= null then B
                else verifiedIrrelevantIdeal(R,null));
            candidateBPF = if seedBPF === null then (
                if B =!= null
                    then isBasePointFreeDivisor(candidateDivisor,B)
                    else isBasePointFreeDivisor candidateDivisor
                ) else seedBPF;
            );
        multipliersTested = append(multipliersTested,m);
        if useNegativeCurveShortcut and not candidateBPF and m < guaranteedMultiplier then
            negativeCurveWitness = negativeBaseLocusCurveData(L,candidateBaseLocus);
        if candidateBPF or negativeCurveWitness =!= null
            or m == guaranteedMultiplier then (
            multiplier = m;
            testDivisor = candidateDivisor;
            bpf = candidateBPF;
            );
        ));
    new HashTable from {
        "nef" => bpf,
        "t" => t,
        "dimension" => d,
        "indexMultiple" => a,
        "N" => N,
        "multiplier" => multiplier,
        "guaranteedMultiplier" => guaranteedMultiplier,
        "multipliersTested" => multipliersTested,
        "certificateType" => if bpf then "base-point-free multiple"
            else if negativeCurveWitness =!= null then "negative curve intersection"
            else "effective base-point-free theorem",
        "negativeCurveWitness" => negativeCurveWitness,
        "cartierDivisor" => L,
        "testDivisor" => testDivisor,
        "basePointFree" => bpf
        }
    )

-- Decide nefness of K_X+tH for t>0, using H constructed from the weighted
-- projective presentation and Proposition 3.1.
-- Stage 2 (T1) of docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md section 5: the
-- IrrelevantIdeal option (added to every method below that has a multigraded
-- overload) lets a caller holding a known-correct irrelevant ideal bypass
-- multigradedBlockData's re-derivation for the Cartier gate.  An Ideal
-- 5th/4th positional argument was tried first but M2's method dispatch caps
-- out at 4 ordinary (non-Option) parameter types (newmethod1234c in
-- Core/methods.m2), which canonicalScaledNefData's and
-- canonicalContractionAtThresholdData's (Ring,ZZ,QQ-or-ZZ,BasicDivisor)
-- overloads already saturate; an Option sidesteps that cap uniformly for all
-- five entry points and is used here even where 4 types would have fit, for
-- one consistent calling convention.  Default null preserves the exact
-- previous re-derivation for every existing caller.
normalizeDivisorClassDegrees = (R,data,label) -> (
    if data === null then return null;
    if not instance(data,List) or #data != 2 then
        error (label | ": DivisorClassDegrees must be {degree(K),degree(H)}");
    n := degreeLength R;
    scan(0..1,i -> (
        di := data#i;
        if not instance(di,List) or #di != n then
            error (label | ": every divisor class degree must have degreeLength(R) entries");
        if any(di,x -> not instance(x,ZZ)) then
            error (label | ": divisor class degrees must be integral");
        ));
    data
    )

canonicalScaledNefData = method(Options => {
    IrrelevantIdeal => null, DivisorClassDegrees => null})
canonicalScaledNefData (Ring,ZZ,QQ) := o -> (R,a,t) -> (
    if a <= 0 then
        error "canonicalScaledNefData: the index multiple must be positive";
    K := canonicalDivisor(R,IsGraded=>true);
    if not isCartier(a*K,IsGraded=>true) then
        error "canonicalScaledNefData: a*K_X is not Cartier";
    H := (weightedAmpleDivisorData R)#"divisor";
    classDegrees := normalizeDivisorClassDegrees(
        R,o.DivisorClassDegrees,"canonicalScaledNefData");
    canonicalScaledNefDataInternal(R,K,H,a,t,null,classDegrees)
    )
canonicalScaledNefData (Ring,ZZ,ZZ) := o -> (R,a,t) ->
    canonicalScaledNefData(R,a,t/1,
        IrrelevantIdeal=>o.IrrelevantIdeal,
        DivisorClassDegrees=>o.DivisorClassDegrees)

-- Stage 1 (T3): multigraded entry points.  The caller supplies the ample
-- Cartier class H directly (plan section 3.5: deriving it automatically is
-- out of scope), verified here with the saturated Cartier test of T2 in
-- place of isCartier.  canonicalScaledNefDataInternal itself needs no other
-- change: it already takes H as an argument, its base-point-free test is
-- multigraded-correct since T2, and its geometric dimension is multigraded-
-- correct since the T3 edit above.
--
-- Stage 2 (T1): if o.IrrelevantIdeal is supplied, it is used verbatim for
-- the Cartier gate below instead of multigradedBlockData's re-derivation --
-- see docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md section 2.3/5.  The same B is
-- now also threaded into canonicalScaledNefDataInternal's own internal
-- search loop (Part 0 of the Stage 2 measurement work: this was flagged as a
-- known gap left open by the original Stage 2 T1 landing -- see that
-- function's own comment -- and is completed here, before it was ever
-- measured against).  Previously the search loop still called the bare
-- 1-argument isBasePointFreeDivisor regardless of what was passed here, so a
-- caller-supplied B fixed only the Cartier gate above and not the nef/
-- basePointFree verdict the search loop actually returns; on a skew
-- multigraded ring that made the returned "nef" answer silently wrong even
-- when this entry point's own gate was correct.
canonicalScaledNefData (Ring,ZZ,QQ,BasicDivisor) := o -> (R,a,t,H) -> (
    if a <= 0 then
        error "canonicalScaledNefData: the index multiple must be positive";
    if ring H =!= R then
        error "canonicalScaledNefData: H must be a divisor on R";
    K := canonicalDivisor(R,IsGraded=>true);
    B := if o.IrrelevantIdeal =!= null then (
        if ring o.IrrelevantIdeal =!= R then
            error "canonicalScaledNefData: IrrelevantIdeal must be an ideal of R";
        o.IrrelevantIdeal
        ) else verifiedIrrelevantIdeal(R,null);
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalScaledNefData: a*K_X is not Cartier";
    classDegrees := normalizeDivisorClassDegrees(
        R,o.DivisorClassDegrees,"canonicalScaledNefData");
    canonicalScaledNefDataInternal(R,K,H,a,t,B,classDegrees)
    )
canonicalScaledNefData (Ring,ZZ,ZZ,BasicDivisor) := o -> (R,a,t,H) ->
    canonicalScaledNefData(R,a,t/1,H,
        IrrelevantIdeal=>o.IrrelevantIdeal,
        DivisorClassDegrees=>o.DivisorClassDegrees)

-- Algorithm 1 of the paper.  First bracket the positive threshold by dyadic
-- rationals, then enumerate the finite set supplied by the rationality
-- theorem.  The threshold v/u in lowest terms has 1 <= v <= a(d+1).
--
-- Stage 1 (T3): the bracket-and-scan logic itself needs no change to work
-- multigraded (its only dimension-dependent step, the numerator bound
-- a*(d+1), is parameterized by d here); it is factored out so both the
-- existing monograded entry point and the new multigraded one share it
-- verbatim.  Does not include "ampleData" in its result -- callers add their
-- own, since the monograded and multigraded ampleData shapes differ.
--
-- Part 0 of the Stage 2 measurement work (completing Stage 1's T1/T3, not
-- new Stage 2 scope): the trailing B is threaded straight into every
-- canonicalScaledNefDataInternal call this makes, so a caller-supplied
-- irrelevant ideal reaches every trial multiple this search tests, not just
-- the Cartier gate of whichever entry point built this call.  B = null
-- reproduces the previous behaviour exactly.
canonicalNefThresholdDataCore = (R,a,K,H,d,limit,B) -> (
    tests := {};
    testsRun := 0;
    testCache := new MutableHashTable;
    testAt := t -> (
        if testCache#?t then return testCache#t;
        if limit =!= null and testsRun >= limit then return null;
        result := canonicalScaledNefDataInternal(R,K,H,a,t,B,null);
        testCache#t = result;
        tests = append(tests,result);
        testsRun = testsRun+1;
        result
        );

    beta := 1;
    betaTest := testAt(beta);
    while betaTest =!= null and not betaTest#"nef" do (
        beta = 2*beta;
        betaTest = testAt(beta);
        );
    if betaTest === null then
        return new HashTable from {
            "threshold" => null,
            "conclusive" => false,
            "phase" => "upper bound",
            "tests" => tests,
            "testsRun" => testsRun,
            "canonicalDivisor" => K,
            "warning" => "the optional threshold search limit was reached"
            };

    alpha := beta/2;
    alphaTest := testAt(alpha);
    while alphaTest =!= null and alphaTest#"nef" do (
        alpha = alpha/2;
        alphaTest = testAt(alpha);
        );
    if alphaTest === null then
        return new HashTable from {
            "threshold" => null,
            "conclusive" => false,
            "phase" => "lower bound",
            "upperBound" => beta,
            "tests" => tests,
            "testsRun" => testsRun,
            "canonicalDivisor" => K,
            "warning" => "the optional threshold search limit was reached"
            };

    numeratorBound := a*(d+1);
    candidates := {};
    scan(1..numeratorBound,v -> (
        u := 1;
        while v/u > alpha do (
            if v/u <= beta and gcd(v,u) == 1 then
                candidates = append(candidates,v/u);
            u = u+1;
            );
        ));
    candidates = unique sort candidates;
    testsRunBeforeCandidates := testsRun;

    -- Stage 1 (T4) originally put a binary search here, over the sorted
    -- candidate list, replacing a linear scan.  Phase C (docs/TORIC-
    -- HYPERSURFACE-FLIP-MMP-DESIGN.md section 5) replaces the binary search
    -- in turn: minimizing the *count* of tests silently assumes every test
    -- costs the same, but a candidate t = p/q's BPF test constructs L =
    -- q*a*K+a*p*H and tests N = a*q via the effective base-point-free
    -- theorem, so both the divisor's coefficients and N grow with p and q --
    -- large-denominator candidates can be far more expensive to test than
    -- small-denominator ones, and minimizing wall-clock time is not the same
    -- as minimizing test count.
    --
    -- The correctness argument for binary search is unchanged and is exactly
    -- what licenses replacing *which* candidate is tested next while keeping
    -- everything else: valid in dimension three (plan section 4.4),
    -- canonicalScaledNefDataInternal always sets trialBound =
    -- guaranteedMultiplier there (guaranteedMultiplier <= 8, see
    -- effectiveNefMultiplier) and tests every multiplier up to it, so "nef"
    -- is a genuine decision procedure rather than a one-sided certificate,
    -- and it is monotone in t; beta is itself always a candidate (v = beta,
    -- u = 1, gcd(beta,1) = 1) and is already known nef, so the candidate
    -- list always has a nef candidate at its top.  Monotonicity is what
    -- makes lo/hi a valid exclusion window regardless of which interior
    -- index is tested next: testing index i and getting non-nef excludes
    -- every index < i (all non-nef, since nef is upward-closed in t), and
    -- getting nef excludes every index > i from being the threshold (i is
    -- itself already at least as good a witness), so lo/hi converge to the
    -- threshold index whatever order the interior is probed in.  If
    -- canonicalScaledNefDataInternal's negative-curve shortcut is ever
    -- active instead (only possible outside dimension three, where
    -- guaranteedMultiplier can exceed 8), that decision-procedure property is
    -- not established and this search would not be valid; every entry point
    -- in this package is for dimension three, so that case does not arise
    -- here (see also the design note's section 5.3: connecting the negative-
    -- curve shortcut to the ordinary dimension-three path, so a single
    -- witness curve can rule out a whole sub-interval of high-denominator
    -- candidates at once instead of testing each one, remains open).
    --
    -- The cost model used to pick the next candidate is deliberately the
    -- simplest one the design note allows (section 5.2: "at least this
    -- lexicographic order is fine"): (denominator q, numerator p) in
    -- lexicographic order, packed into one integer via
    -- q*(numeratorBound+1)+p (numerator p is always < numeratorBound+1, so
    -- this preserves the lexicographic order exactly).  This needs no
    -- section-strand estimate up front -- only q and p, already in hand from
    -- the candidate list -- and a refined cost model (built from
    -- testLog's recorded actualCpuTime, per section 7's "record ... so
    -- future cost models can be improved") can replace it later without
    -- changing anything else here.
    threshold := null;
    thresholdTest := null;
    testLog := {};
    if #candidates > 0 then (
        lo := 0;
        hi := #candidates-1; -- candidates#hi is already known nef (see above)
        stalled := false;
        while lo < hi and not stalled do (
            remaining := toList(lo..hi-1);
            costOf := i -> (denominator candidates#i)*(numeratorBound+1)
                + numerator candidates#i;
            costs := apply(remaining,costOf);
            bestPos := position(costs,c -> c == min costs);
            mid := remaining#bestPos;
            midCost := costs#bestPos;
            elapsed := timing testAt(candidates#mid);
            midTest := elapsed#1;
            testLog = append(testLog,new HashTable from {
                "candidate" => candidates#mid,
                "denominator" => denominator candidates#mid,
                "estimatedCost" => midCost,
                "actualCpuTime" => elapsed#0,
                "nefCertificate" =>
                    if midTest === null then null else midTest#"certificateType"
                });
            if midTest === null then stalled = true
            else if midTest#"nef" then hi = mid
            else lo = mid+1;
            );
        if not stalled then (
            finalTest := testAt(candidates#lo);
            if finalTest =!= null and finalTest#"nef" then (
                threshold = candidates#lo;
                thresholdTest = finalTest;
                );
            );
        );
    -- The number of tests a linear scan of the same sorted candidate list
    -- would have needed to reach the same threshold, for direct comparison
    -- with testsRun (see research-log/docs/STAGE1-MEASUREMENT-RESULTS.md); null when no
    -- threshold was found.  Cost-aware search trades test *count* for lower
    -- test *cost* (see above), so unlike the binary search it replaces, it
    -- has no general guarantee of testsRun <= linearTestsRunEquivalent.
    linearTestsRunEquivalent := if threshold === null then null
        else testsRunBeforeCandidates + 1 + #(select(candidates,t -> t < threshold));
    if threshold === null and limit === null then
        error "canonicalNefThresholdData: no nef candidate; input hypotheses may fail";
    if threshold === null then
        return new HashTable from {
            "threshold" => null,
            "conclusive" => false,
            "phase" => "candidate search",
            "lowerBound" => alpha,
            "upperBound" => beta,
            "numeratorBound" => numeratorBound,
            "candidates" => candidates,
            "tests" => tests,
            "testsRun" => testsRun,
            "linearTestsRunEquivalent" => linearTestsRunEquivalent,
            "testLog" => testLog,
            "canonicalDivisor" => K,
            "warning" => "the optional threshold search limit was reached"
            };
    new HashTable from {
        "threshold" => threshold,
        "conclusive" => true,
        "lowerBound" => alpha,
        "upperBound" => beta,
        "numeratorBound" => numeratorBound,
        "candidates" => candidates,
        "thresholdTest" => thresholdTest,
        "tests" => tests,
        "testsRun" => testsRun,
        "linearTestsRunEquivalent" => linearTestsRunEquivalent,
        "testLog" => testLog,
        "canonicalDivisor" => K
        }
    )

canonicalNefThresholdData = method(Options => {
    ThresholdSearchLimit => null, IrrelevantIdeal => null})
canonicalNefThresholdData (Ring,ZZ) := o -> (R,a) -> (
    if a <= 0 then
        error "canonicalNefThresholdData: the index multiple must be positive";
    limit := o.ThresholdSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalNefThresholdData: ThresholdSearchLimit must be null or positive";
    K := canonicalDivisor(R,IsGraded=>true);
    if not isCartier(a*K,IsGraded=>true) then
        error "canonicalNefThresholdData: a*K_X is not Cartier";
    ampleData := weightedAmpleDivisorData R;
    H := ampleData#"divisor";
    d := dim R - 1;
    result := canonicalNefThresholdDataCore(R,a,K,H,d,limit,null);
    new HashTable from join(pairs result,{"ampleData" => ampleData})
    )

-- Stage 1 (T3): the multigraded entry point.  The caller supplies the ample
-- Cartier class H (plan section 3.5); the geometric dimension and the
-- irrelevant ideal come from T1, and the Cartier gate uses T2's saturated
-- test.  The bracket-and-scan logic is otherwise identical to the
-- monograded path, via canonicalNefThresholdDataCore.  The result carries
-- the same keys as the monograded entry point (plus "blockData"), so the
-- measurement harness and any later code can read either uniformly.
--
-- Stage 2 (T1): if o.IrrelevantIdeal is supplied, multigradedBlockData is
-- bypassed entirely -- including for the geometric dimension.
-- docs/STAGE2-SINGULAR-MEASUREMENT-PLAN.md section 5's T1 flags that
-- "dim R - degreeLength R equals multigradedBlockData's geometricDimension"
-- is a claim to verify, not assume; it was checked directly against the
-- plan's own ring Z (degreeLength 2, dim 5): multigradedBlockData Z succeeds
-- (despite its wrong block partition) and its "geometricDimension" field
-- agrees exactly with dim Z - degreeLength Z (both 3), so computing d this
-- way is safe here and avoids depending on multigradedBlockData succeeding
-- at all when a caller-supplied ideal is in hand.
--
-- Part 0 of the Stage 2 measurement work (completing Stage 1's T1/T3): B is
-- now also threaded into canonicalNefThresholdDataCore, so every scaled-nef
-- test the threshold search runs (not just this entry point's own Cartier
-- gate above) honors a caller-supplied irrelevant ideal.
canonicalNefThresholdData (Ring,ZZ,BasicDivisor) := o -> (R,a,H) -> (
    if a <= 0 then
        error "canonicalNefThresholdData: the index multiple must be positive";
    if ring H =!= R then
        error "canonicalNefThresholdData: H must be a divisor on R";
    limit := o.ThresholdSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalNefThresholdData: ThresholdSearchLimit must be null or positive";
    K := canonicalDivisor(R,IsGraded=>true);
    suppliedB := o.IrrelevantIdeal;
    if suppliedB =!= null and ring suppliedB =!= R then
        error "canonicalNefThresholdData: IrrelevantIdeal must be an ideal of R";
    blockData := if suppliedB === null then multigradedBlockData R else null;
    if blockData =!= null and not blockData#"verifiedBlockDiagonal" then error(
        "this ring has a skew (mixed-degree) multigraded variable, so "
        | "multigradedBlockData's block-classification heuristic cannot "
        | "reliably determine the irrelevant ideal (see "
        | "tests/multigraded-skew-cartier.m2).  Supply the ring's true "
        | "irrelevant ideal explicitly via IrrelevantIdeal=>B.");
    B := if suppliedB =!= null then suppliedB else blockData#"irrelevantIdeal";
    d := if suppliedB =!= null then dim R - degreeLength R
        else blockData#"geometricDimension";
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalNefThresholdData: a*K_X is not Cartier";
    result := canonicalNefThresholdDataCore(R,a,K,H,d,limit,B);
    extraKeys := if suppliedB =!= null then {
        "irrelevantIdeal" => B, "irrelevantIdealSource" => "caller-supplied"}
        else {"blockData" => blockData};
    new HashTable from join(pairs result,join({
        "ampleData" => new HashTable from {"ring" => R,"divisor" => H}},
        extraKeys))
    )

canonicalNefThreshold = method(Options => options canonicalNefThresholdData)
canonicalNefThreshold (Ring,ZZ) := o -> (R,a) -> (
    result := canonicalNefThresholdData(
        R,a,ThresholdSearchLimit=>o.ThresholdSearchLimit);
    if not result#"conclusive" then
        error "canonicalNefThreshold: the optional search limit was reached";
    result#"threshold"
    )

-- Construct the graph of the complete linear system of a base-point-free
-- Cartier divisor.  mapToProjectiveSpaceInternal represents its sections in
-- a common rational trivialization; their polynomial representatives can
-- therefore have an artificial common zero divisor (see that function's own
-- comment for the multigraded D = 0 defense bug this avoids).  The kernel
-- into R[t] is the Rees graph closure and is insensitive to that choice of
-- trivialization.
completeLinearSystemGraphData = method()
completeLinearSystemGraphData BasicDivisor := D -> (
    if not isBasePointFreeDivisor D then
        error "completeLinearSystemGraphData: the divisor is not base-point-free";
    R := ring D;
    S := ambient R;
    if degreeLength S != 1 then
        error "completeLinearSystemGraphData: expected a singly graded ring";
    sourceIdeal := ideal R;
    sectionMap := mapToProjectiveSpaceInternal(D,Variable=>"mmpLinearSystemTarget");
    sectionImages := first entries sectionMap.matrix;
    if #sectionImages == 0 then
        error "completeLinearSystemGraphData: the complete linear system has no sections";
    liftedImages := apply(sectionImages,q -> lift(q,S));
    sourceVars := flatten entries vars S;
    sourceDegrees := apply(sourceVars,q -> {(degree q)#0,0});
    kk := coefficientRing S;
    productRing := kk[Variables=>#sourceVars+#sectionImages,
        Degrees=>join(sourceDegrees,apply(#sectionImages,i -> {0,1}))];
    target := R[getSymbol "mmpGraphParameter",Degrees=>{{0,1}}];
    graphParameter := target_(numgens target-1);
    graphMap := map(target,productRing,
        join(apply(sourceVars,q -> sub(q,R)),
            apply(sectionImages,q -> q*graphParameter)));
    graphIdeal := kernel graphMap;
    targetRing := (source sectionMap)/(kernel sectionMap);
    graphData := new HashTable from {
        "productRing" => productRing,
        "graphIdeal" => graphIdeal,
        "graphMap" => graphMap,
        "sourceRing" => R,
        "targetRing" => targetRing,
        "sourcePolynomialRing" => S,
        "sourceIdeal" => sourceIdeal,
        "sourceVariableCount" => #sourceVars,
        "targetVariableCount" => #sectionImages,
        "sectionMap" => sectionMap,
        "sectionImages" => sectionImages,
        "liftedSectionImages" => liftedImages,
        "basePointFree" => true,
        "graphConstruction" => "kernel of the Rees parametrization"
        };
    new HashTable from join(pairs graphData,{
        "graph" => mmpGraphMorphism graphData
        })
    )

-- Stage 1 (T5): flatten a multigraded ring to the diagonal subalgebra of a
-- caller-supplied ample Cartier class w, i.e. the subring generated by the
-- degree-w strand.  mapToProjectiveSpaceInternal(w) already builds exactly
-- that subring as the image of its rational map (a singly graded polynomial
-- ring modulo the kernel of the map sending its variables to a chosen
-- spanning set of sections of w); this reuses it rather than re-deriving it,
-- and its basis(degree sub(1,R),-) call (not a bare integer) is not subject
-- to the basis(0,-) defect found while implementing T2.  When w is very
-- ample -- true for both of this plan's measurement inputs, where w is
-- literally the polarization the multigraded presentation was built from --
-- the result is an isomorphic (as varieties) singly graded presentation of
-- the same X; this is not verified in general (see
-- research-log/docs/STAGE1-MEASUREMENT-RESULTS.md).
diagonalSubalgebraData = (R,w) -> (
    if ring w =!= R then
        error "diagonalSubalgebraData: w must be a divisor on R";
    wSectionMap := mapToProjectiveSpaceInternal(w,Variable=>"mmpFlatteningVariable");
    Sflat := source wSectionMap;
    if degreeLength Sflat != 1 then
        error "diagonalSubalgebraData: flattening did not produce a singly graded ring";
    Rflat := Sflat/(kernel wSectionMap);
    new HashTable from {
        "ring" => R,
        "ampleClass" => w,
        "sectionMap" => wSectionMap,
        "flatRing" => Rflat,
        "flatAmbientRing" => Sflat,
        "sectionImages" => first entries wSectionMap.matrix
        }
    )

-- Stage 1 (T5): the multigraded companion of completeLinearSystemGraphData.
-- SteinFactorization's blockDegreeData requires the graph ring to be
-- bigraded, block *diagonal* (every variable (positive,0) or (0,positive));
-- a multigraded source of rank r would give rank r+1, which it cannot
-- accept, and generalizing it is explicitly out of scope (plan section 4.5).
-- So the source side of the graph is built from the flattened
-- (diagonalSubalgebraData) ring instead of from R directly -- deliberately
-- reintroducing a monograded presentation, and with it the cost that
-- motivated keeping the multigraded presentation through the nef/threshold
-- stages; measuring that cost is the point (plan section 5.2, stage 5).
-- Otherwise this mirrors completeLinearSystemGraphData exactly: D's own
-- sections still come from mapToProjectiveSpaceInternal(D) on the original
-- (multigraded) R, unaffected by the flattening.  D's embedding shift d1 is
-- exactly where the multigraded D = 0 defense bug of
-- mapToProjectiveSpaceInternal's own comment was found (a threshold divisor
-- with d1 = {0,1}), which is why this call site uses the Internal version
-- rather than WeilDivisors' own mapToProjectiveSpace.
--
-- Part 0 of the Stage 2 measurement work (completing Stage 1's T1/T3, not
-- new Stage 2 scope): this method's own base-point-free re-check of D was
-- flagged, when Stage 2's T1 landed, as a call site that still used the bare
-- 1-argument isBasePointFreeDivisor even when the caller building D already
-- held a known-correct irrelevant ideal (canonicalContractionAtThresholdData-
-- Core's own loop tests D for base-point-freeness before ever handing it to
-- this function, so this was a second, redundant test using a possibly wrong
-- B, capable of erroring "not base-point-free" on a divisor the caller had
-- already correctly verified was).  The IrrelevantIdeal option added here
-- lets that B be passed through instead of re-derived; default null
-- reproduces the previous behaviour exactly.
completeLinearSystemGraphDataMultigraded = method(Options => {IrrelevantIdeal => null})
completeLinearSystemGraphDataMultigraded (BasicDivisor,BasicDivisor) := o -> (D,w) -> (
    R := ring D;
    suppliedB := o.IrrelevantIdeal;
    if suppliedB =!= null and ring suppliedB =!= R then
        error "completeLinearSystemGraphDataMultigraded: IrrelevantIdeal must be an ideal of R";
    bpf := if suppliedB =!= null then isBasePointFreeDivisor(D,suppliedB)
        else isBasePointFreeDivisor D;
    if not bpf then
        error "completeLinearSystemGraphDataMultigraded: the divisor is not base-point-free";
    if ring w =!= R then
        error "completeLinearSystemGraphDataMultigraded: D and w must be divisors on the same ring";
    flattening := diagonalSubalgebraData(R,w);
    Sflat := flattening#"flatAmbientRing";
    flatVars := flatten entries vars Sflat;
    flatSectionImages := flattening#"sectionImages";
    sectionMap := mapToProjectiveSpaceInternal(D,Variable=>"mmpLinearSystemTarget");
    sectionImages := first entries sectionMap.matrix;
    if #sectionImages == 0 then
        error "completeLinearSystemGraphDataMultigraded: the complete linear system has no sections";
    liftedImages := apply(sectionImages,q -> lift(q,ambient R));
    flatDegrees := apply(flatVars,q -> {(degree q)#0,0});
    kk := coefficientRing Sflat;
    productRing := kk[Variables=>#flatVars+#sectionImages,
        Degrees=>join(flatDegrees,apply(#sectionImages,i -> {0,1}))];
    r := degreeLength R;
    target := R[getSymbol "mmpGraphParameter",Degrees=>{toList(r:0)|{1}}];
    graphParameter := target_(numgens target-1);
    graphMap := map(target,productRing,
        join(apply(flatSectionImages,q -> sub(q,R)),
            apply(sectionImages,q -> q*graphParameter)));
    graphIdeal := kernel graphMap;
    targetRing := (source sectionMap)/(kernel sectionMap);
    graphData := new HashTable from {
        "productRing" => productRing,
        "graphIdeal" => graphIdeal,
        "graphMap" => graphMap,
        "sourceRing" => flattening#"flatRing",
        "targetRing" => targetRing,
        "sourcePolynomialRing" => Sflat,
        "sourceVariableCount" => #flatVars,
        "targetVariableCount" => #sectionImages,
        "sectionMap" => sectionMap,
        "sectionImages" => sectionImages,
        "liftedSectionImages" => liftedImages,
        "basePointFree" => true,
        "flatteningData" => flattening,
        "graphConstruction" =>
            "kernel of the Rees parametrization, source flattened to the diagonal subalgebra of w"
        };
    new HashTable from join(pairs graphData,{
        "graph" => mmpGraphMorphism graphData
        })
    )

-- A connected-fibre contraction is birational exactly when source and target
-- have the same dimension; otherwise it is of fibre type.
contractionTypeData = method()
contractionTypeData (ZZ,ZZ) := (sourceDimension,targetDimension) -> (
    if sourceDimension < 0 then
        error "contractionTypeData: the source dimension must be nonnegative";
    if targetDimension < 0 then
        error "contractionTypeData: the target dimension must be nonnegative";
    if targetDimension > sourceDimension then
        error "contractionTypeData: target dimension exceeds source dimension";
    birational := targetDimension == sourceDimension;
    new HashTable from {
        "sourceDimension" => sourceDimension,
        "targetDimension" => targetDimension,
        "dimensionDrop" => sourceDimension-targetDimension,
        "contractionType" => if birational then "birational" else "fibration",
        "isBirational" => birational,
        "isFibreType" => not birational
        }
    )

-- Stage 1 (T5): shared core.  buildLinearSystemGraph is the one step that
-- differs between the monograded and multigraded paths (completeLinear-
-- SystemGraphData vs completeLinearSystemGraphDataMultigraded); everything
-- else -- the multiplier search, the trivial-point-target shortcut, and the
-- Stein factorization call -- is identical, so it is factored out and
-- parameterized by d (T1's geometric dimension) and by that one builder.
-- Does not include "ampleData"; callers add their own.
--
-- Part 0 of the Stage 2 measurement work (completing Stage 1's T1/T3): the
-- trailing B threads a caller-supplied irrelevant ideal into this loop's OWN
-- base-point-free test of morphismDivisor, not only into whatever B
-- buildLinearSystemGraph's own closure was built with.  B = null reproduces
-- the previous behaviour exactly.
canonicalContractionAtThresholdDataCore = (R,a,lambda,K,H,d,limit,buildLinearSystemGraph,B) -> (
    p := numerator lambda;
    q := denominator lambda;
    N := a*q;
    cartierThresholdDivisor := q*a*K+a*p*H;
    guaranteedMultiplier := effectiveNefMultiplier(d,N);
    maximum := if limit === null then guaranteedMultiplier
        else min(limit,guaranteedMultiplier);
    multiplier := 1;
    morphismDivisor := cartierThresholdDivisor;
    isMorphismDivisorBasePointFree := () -> if B =!= null
        then isBasePointFreeDivisor(morphismDivisor,B)
        else isBasePointFreeDivisor morphismDivisor;
    while multiplier <= maximum
        and not isMorphismDivisorBasePointFree() do (
            multiplier = multiplier+1;
            morphismDivisor = multiplier*cartierThresholdDivisor;
            );
    if multiplier > maximum then
        return new HashTable from {
            "conclusive" => false,
            "threshold" => lambda,
            "cartierThresholdDivisor" => cartierThresholdDivisor,
            "guaranteedMultiplier" => guaranteedMultiplier,
            "multipliersTested" => maximum,
            "canonicalDivisor" => K,
            "warning" => "the optional contraction multiple limit was reached"
            };
    linearSystemGraph := buildLinearSystemGraph morphismDivisor;
    if linearSystemGraph#"targetVariableCount" == 1 then
        return new HashTable from join({
            "conclusive" => true,
            "threshold" => lambda,
            "N" => N,
            "cartierThresholdDivisor" => cartierThresholdDivisor,
            "multiplier" => multiplier,
            "guaranteedMultiplier" => guaranteedMultiplier,
            "morphismDivisor" => morphismDivisor,
            "linearSystemGraph" => linearSystemGraph,
            "steinFactorizationType" => "trivial point target",
            "contractionGraph" => linearSystemGraph#"graph",
            "canonicalDivisor" => K
            },pairs contractionTypeData(d,0));
    homData := steinHomData(
        linearSystemGraph#"productRing",linearSystemGraph#"graphIdeal");
    algebraData := steinCoordinateAlgebra homData;
    rawContractionGraph := directSteinGraph(homData,algebraData);
    contractionGraphData := new HashTable from join(pairs rawContractionGraph,{
        "sourceRing" => linearSystemGraph#"sourceRing",
        "targetRing" => algebraData#"ring"
        });
    contractionGraph := mmpGraphMorphism contractionGraphData;
    targetDimension := dim(algebraData#"ring")-1;
    new HashTable from join({
        "conclusive" => true,
        "threshold" => lambda,
        "N" => N,
        "cartierThresholdDivisor" => cartierThresholdDivisor,
        "multiplier" => multiplier,
        "guaranteedMultiplier" => guaranteedMultiplier,
        "morphismDivisor" => morphismDivisor,
        "linearSystemGraph" => linearSystemGraph,
        "steinHomData" => homData,
        "steinAlgebraData" => algebraData,
        "steinFactorizationType" => "computed",
        "contractionGraphData" => contractionGraphData,
        "contractionGraph" => contractionGraph,
        "canonicalDivisor" => K
        },pairs contractionTypeData(d,targetDimension))
    )

canonicalContractionAtThresholdData = method(
    Options => {ContractionMultipleLimit => null, IrrelevantIdeal => null})
canonicalContractionAtThresholdData (Ring,ZZ,QQ) := o -> (R,a,lambda) -> (
    if a <= 0 then
        error "canonicalContractionAtThresholdData: the index multiple must be positive";
    if lambda <= 0 then
        error "canonicalContractionAtThresholdData: the threshold must be positive";
    limit := o.ContractionMultipleLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalContractionAtThresholdData: ContractionMultipleLimit must be null or positive";
    K := canonicalDivisor(R,IsGraded=>true);
    if not isCartier(a*K,IsGraded=>true) then
        error "canonicalContractionAtThresholdData: a*K_X is not Cartier";
    ampleData := weightedAmpleDivisorData R;
    H := ampleData#"divisor";
    d := dim R - 1;
    result := canonicalContractionAtThresholdDataCore(R,a,lambda,K,H,d,limit,
        morphismDivisor -> completeLinearSystemGraphData morphismDivisor,null);
    new HashTable from join(pairs result,{"ampleData" => ampleData})
    )
canonicalContractionAtThresholdData (Ring,ZZ,ZZ) := o -> (R,a,lambda) ->
    canonicalContractionAtThresholdData(R,a,lambda/1,
        ContractionMultipleLimit=>o.ContractionMultipleLimit)

-- Stage 1 (T5): the multigraded entry point.  H is the caller-supplied
-- ample Cartier class (plan section 3.5); it is used both as the H in
-- K+lambda*H and, per plan section 4.5, as the class the source ring is
-- flattened along at the Stein interface (completeLinearSystemGraphData-
-- Multigraded).  The Cartier gate uses T2's saturated test, and the
-- dimension bookkeeping uses T1's geometric dimension.
--
-- Stage 2 (T1): if o.IrrelevantIdeal is supplied, multigradedBlockData is
-- bypassed entirely for both the Cartier gate and the geometric dimension
-- (dim R - degreeLength R; see canonicalNefThresholdData's comment for the
-- verification this equals multigradedBlockData's own field on the plan's
-- Z).
--
-- Part 0 of the Stage 2 measurement work (completing Stage 1's T1/T3): B is
-- now threaded both into canonicalContractionAtThresholdDataCore's own
-- base-point-free loop and into completeLinearSystemGraphDataMultigraded's
-- IrrelevantIdeal option, so the caller-supplied ideal reaches every
-- base-point-free test this entry point triggers, not only its own Cartier
-- gate above.
canonicalContractionAtThresholdData (Ring,ZZ,QQ,BasicDivisor) := o -> (R,a,lambda,H) -> (
    if a <= 0 then
        error "canonicalContractionAtThresholdData: the index multiple must be positive";
    if lambda <= 0 then
        error "canonicalContractionAtThresholdData: the threshold must be positive";
    if ring H =!= R then
        error "canonicalContractionAtThresholdData: H must be a divisor on R";
    limit := o.ContractionMultipleLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalContractionAtThresholdData: ContractionMultipleLimit must be null or positive";
    K := canonicalDivisor(R,IsGraded=>true);
    suppliedB := o.IrrelevantIdeal;
    if suppliedB =!= null and ring suppliedB =!= R then
        error "canonicalContractionAtThresholdData: IrrelevantIdeal must be an ideal of R";
    blockData := if suppliedB === null then multigradedBlockData R else null;
    if blockData =!= null and not blockData#"verifiedBlockDiagonal" then error(
        "this ring has a skew (mixed-degree) multigraded variable, so "
        | "multigradedBlockData's block-classification heuristic cannot "
        | "reliably determine the irrelevant ideal (see "
        | "tests/multigraded-skew-cartier.m2).  Supply the ring's true "
        | "irrelevant ideal explicitly via IrrelevantIdeal=>B.");
    B := if suppliedB =!= null then suppliedB else blockData#"irrelevantIdeal";
    d := if suppliedB =!= null then dim R - degreeLength R
        else blockData#"geometricDimension";
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalContractionAtThresholdData: a*K_X is not Cartier";
    result := canonicalContractionAtThresholdDataCore(R,a,lambda,K,H,d,limit,
        morphismDivisor -> completeLinearSystemGraphDataMultigraded(
            morphismDivisor,H,IrrelevantIdeal=>B),B);
    extraKeys := if suppliedB =!= null then {
        "irrelevantIdeal" => B, "irrelevantIdealSource" => "caller-supplied"}
        else {"blockData" => blockData};
    new HashTable from join(pairs result,join({
        "ampleData" => new HashTable from {"ring" => R,"divisor" => H}},
        extraKeys))
    )
canonicalContractionAtThresholdData (Ring,ZZ,ZZ,BasicDivisor) := o -> (R,a,lambda,H) ->
    canonicalContractionAtThresholdData(R,a,lambda/1,H,
        ContractionMultipleLimit=>o.ContractionMultipleLimit,
        IrrelevantIdeal=>o.IrrelevantIdeal)

canonicalContractionData = method(Options => {
    ThresholdSearchLimit => null,
    ContractionMultipleLimit => null,
    IrrelevantIdeal => null})
canonicalContractionData (Ring,ZZ) := o -> (R,a) -> (
    thresholdData := canonicalNefThresholdData(
        R,a,ThresholdSearchLimit=>o.ThresholdSearchLimit);
    if not thresholdData#"conclusive" then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "threshold",
            "thresholdData" => thresholdData,
            "warning" => "the optional threshold search limit was reached"
            };
    result := canonicalContractionAtThresholdData(
        R,a,thresholdData#"threshold",
        ContractionMultipleLimit=>o.ContractionMultipleLimit);
    new HashTable from join(pairs result,{"thresholdData" => thresholdData})
    )

-- Stage 1 (T5): the multigraded entry point.
--
-- Stage 2 (T1): o.IrrelevantIdeal, if supplied, is forwarded verbatim to
-- both canonicalNefThresholdData and canonicalContractionAtThresholdData;
-- this function adds no Cartier or dimension logic of its own.
canonicalContractionData (Ring,ZZ,BasicDivisor) := o -> (R,a,H) -> (
    thresholdData := canonicalNefThresholdData(
        R,a,H,ThresholdSearchLimit=>o.ThresholdSearchLimit,
        IrrelevantIdeal=>o.IrrelevantIdeal);
    if not thresholdData#"conclusive" then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "threshold",
            "thresholdData" => thresholdData,
            "warning" => "the optional threshold search limit was reached"
            };
    result := canonicalContractionAtThresholdData(
        R,a,thresholdData#"threshold",H,
        ContractionMultipleLimit=>o.ContractionMultipleLimit,
        IrrelevantIdeal=>o.IrrelevantIdeal);
    new HashTable from join(pairs result,{"thresholdData" => thresholdData})
    )

-- Algorithm 4, applied to the base W of a birational contraction.  If the
-- canonical module already embeds as the unit ideal, its relative canonical
-- Proj is W itself; otherwise FlipComputation constructs the model as a graph.
relativeCanonicalModelFromBaseData = method(Options => {
    RelativeCanonicalMultipliers => null,
    RelativeCanonicalMaxMultiplier => 24,
    RelativeCanonicalVerbose => false})
relativeCanonicalModelFromBaseData Ring := o -> W -> (
    if dim W-1 != 3 then
        error "relativeCanonicalModelFromBaseData: expected a projective threefold";
    if canonicalIdeal W == ideal 1_W then
        return new HashTable from {
            "conclusive" => true,
            "baseRing" => W,
            "relativeModelRing" => W,
            "relativeModelGraph" => null,
            "relativeModelProjection" => null,
            "relativeModelType" => "identity",
            "isIdentity" => true,
            "identityCertificate" => "canonical module embeds as the unit ideal",
            "sourceDimension" => dim W-1,
            "targetDimension" => dim W-1
            };
    -- computeRelativeCanonicalModel raises an error when no multiplier it
    -- tried produced a small projection with an S_2 source: Lemma 6.6's test is sufficient, not
    -- necessary, so exhausting the schedule means "not settled here", not "no
    -- relative canonical model exists".  That is a bounded search coming up
    -- empty, exactly like the threshold and canonical-index searches above, so
    -- report it the same structured way instead of letting a raw error escape
    -- through threefoldMMPData.  A genuinely divisorial relative canonical
    -- model -- neither the identity nor small -- also lands here, since
    -- computeRelativeCanonicalModel only ever accepts a small one.
    modelProjection := try computeRelativeCanonicalModel(W,
        Multipliers=>o.RelativeCanonicalMultipliers,
        MaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
        ReturnGraph=>false,
        BaseIsProjective=>true,
        Verbose=>o.RelativeCanonicalVerbose)
        else null;
    if modelProjection === null then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "relative canonical model",
            "baseRing" => W,
            "multipliersTried" => if o.RelativeCanonicalMultipliers =!= null
                then o.RelativeCanonicalMultipliers
                else toList(1..o.RelativeCanonicalMaxMultiplier),
            "warning" => "no multiplier tried gave a small projection with an "
                | "S_2 source; raise RelativeCanonicalMaxMultiplier, or the "
                | "relative canonical model may not be small (FlipComputation "
                | "only accepts a small one)"
            };
    baseCanonicalIdeal := restrictToBase(
        modelProjection,modelProjection#blownUpIdeal);
    nonFreeLocus := fittingIdeal(1,module baseCanonicalIdeal);
    irrelevant := ideal flatten entries vars W;
    modelIsIdentity := saturate(nonFreeLocus,irrelevant) == ideal 1_W;
    if modelIsIdentity then
        return new HashTable from {
            "conclusive" => true,
            "baseRing" => W,
            "relativeModelRing" => W,
            "relativeModelGraph" => null,
            "relativeModelProjection" => modelProjection,
            "canonicalBlowupIdeal" => baseCanonicalIdeal,
            "nonInvertibleLocus" => nonFreeLocus,
            "relativeModelType" => "identity",
            "isIdentity" => true,
            "identityCertificate" => "the canonical blow-up ideal is locally free of rank one on Proj",
            "sourceDimension" => dim W-1,
            "targetDimension" => dim W-1
            };
    modelGraph := b2mToGraphMorphism(
        modelProjection,Verbose=>o.RelativeCanonicalVerbose);
    modelRing := modelGraph#sourceRing;
    new HashTable from {
        "conclusive" => true,
        "baseRing" => W,
        "relativeModelRing" => modelRing,
        "relativeModelGraph" => modelGraph,
        "relativeModelProjection" => modelProjection,
        "canonicalBlowupIdeal" => baseCanonicalIdeal,
        "nonInvertibleLocus" => nonFreeLocus,
        "relativeModelType" => "computed",
        "isIdentity" => false,
        "identityCertificate" => "the canonical blow-up ideal is not locally free on Proj",
        "sourceDimension" => dim(modelRing)-1,
        "targetDimension" => dim(W)-1
        }
    )

relativeCanonicalModelData = method(Options => options relativeCanonicalModelFromBaseData)
relativeCanonicalModelData HashTable := o -> contraction -> (
    if not contraction#?"conclusive" or not contraction#"conclusive" then
        error "relativeCanonicalModelData: expected a conclusive contraction";
    if not contraction#?"isBirational" or not contraction#"isBirational" then
        error "relativeCanonicalModelData: the contraction is not birational";
    if not contraction#?"steinAlgebraData" then
        error "relativeCanonicalModelData: the contraction has no Stein target ring";
    result := relativeCanonicalModelFromBaseData(
        contraction#"steinAlgebraData"#"ring",
        RelativeCanonicalMultipliers=>o.RelativeCanonicalMultipliers,
        RelativeCanonicalMaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
        RelativeCanonicalVerbose=>o.RelativeCanonicalVerbose);
    new HashTable from join(pairs result,{"contractionData" => contraction})
    )

relativeCanonicalModelIsomorphismData = method()
relativeCanonicalModelIsomorphismData HashTable := model -> (
    if not model#?"conclusive" or not model#"conclusive" then
        error "relativeCanonicalModelIsomorphismData: expected a conclusive model";
    if not model#?"isIdentity" then
        error "relativeCanonicalModelIsomorphismData: missing identity data";
    new HashTable from {
        "isIsomorphism" => model#"isIdentity",
        "relativeModelType" => model#"relativeModelType",
        "certificate" => model#"identityCertificate"
        }
    )

-- The inverse rational map from the base of a nonidentity relative model to
-- the model itself.  If Z=Proj_W Rees(I), its fibre coordinates are the
-- generators of I.  Substituting those generators into the Segre monomials
-- used by b2mToGraphMorphism gives homogeneous coordinates for W -->> Z.
relativeModelInverseRationalMapData = method()
relativeModelInverseRationalMapData HashTable := model -> (
    if not model#?"conclusive" or not model#"conclusive" then
        error "relativeModelInverseRationalMapData: expected a conclusive model";
    if not model#?"isIdentity" or model#"isIdentity" then
        error "relativeModelInverseRationalMapData: expected a nonidentity relative model";
    if not model#?"relativeModelProjection" or not model#?"relativeModelGraph" then
        error "relativeModelInverseRationalMapData: missing projection or graph data";
    P := model#"relativeModelProjection";
    G := model#"relativeModelGraph";
    if not instance(P,B2MProjection) or not instance(G,GraphMorphism) then
        error "relativeModelInverseRationalMapData: expected B2M and graph data";
    baseRing := model#"baseRing";
    modelRing := model#"relativeModelRing";
    us := P#fiberVariables;
    xs := P#baseVariables;
    diagonalData := b2mDiagonalData P;
    HB := diagonalData#"hilbertBasis";
    projectionToBase := map(baseRing,P#ambientRing,
        toList(#us:0_baseRing) | gens baseRing);
    idealGenerators := apply(first entries gens P#blownUpIdeal,
        f -> projectionToBase f);
    baseVariables := flatten entries vars baseRing;
    coordinateImages := apply(HB,v ->
        product apply(#us,j -> idealGenerators#j^(v#j))
        * product apply(#xs,i -> baseVariables#i^(v#(#us+i))));
    if #coordinateImages != numgens ambient modelRing then
        error "relativeModelInverseRationalMapData: Segre coordinates do not match the model ring";
    coordinateMap := map(baseRing,ambient modelRing,coordinateImages);
    modelRelationsVanish := coordinateMap(ideal modelRing) == ideal 0_baseRing;
    graphSubstitution := map(baseRing,G#ambientRing,
        coordinateImages | baseVariables);
    graphRelationsVanish := graphSubstitution(G#definingIdeal) == ideal 0_baseRing;
    if not modelRelationsVanish or not graphRelationsVanish then
        error "relativeModelInverseRationalMapData: inverse coordinates fail the graph equations";
    imageDegrees := apply(coordinateImages,f -> (degree f)#0);
    modelDegrees := apply(flatten entries vars modelRing,z -> (degree z)#0);
    degreeScales := unique apply(#coordinateImages,i ->
        imageDegrees#i // modelDegrees#i);
    if #degreeScales != 1 or any(#coordinateImages,i ->
        imageDegrees#i != first(degreeScales)*modelDegrees#i) then
        error "relativeModelInverseRationalMapData: inverse coordinates have incompatible degrees";
    coordinateBaseIdeal := ideal coordinateImages;
    irrelevant := ideal baseVariables;
    expectedBaseIdeal := ideal idealGenerators;
    baseLocusCertified := saturate(radical coordinateBaseIdeal,irrelevant)
        == saturate(radical expectedBaseIdeal,irrelevant);
    if not baseLocusCertified then
        error "relativeModelInverseRationalMapData: could not certify the indeterminacy locus";
    new HashTable from {
        "sourceRing" => baseRing,
        "targetRing" => modelRing,
        "coordinateImages" => coordinateImages,
        "coordinateMap" => coordinateMap,
        "degreeScale" => first degreeScales,
        "diagonalData" => diagonalData,
        "baseIdeal" => coordinateBaseIdeal,
        "expectedBaseIdeal" => expectedBaseIdeal,
        "baseLocusCertified" => true,
        "modelRelationsVanish" => true,
        "graphRelationsVanish" => true,
        "graphSubstitution" => graphSubstitution,
        "certificate" => "substitution of the Rees ideal generators into the Segre graph coordinates"
        }
    )

contractionGraphSmallnessInternal = (P,J,ns,sourceDimension) -> (
    if ring J =!= P then
        error "contractionGraphSmallnessData: graph ideal belongs to the wrong ring";
    if ns <= 0 or ns >= numgens P then
        error "contractionGraphSmallnessData: invalid source variable count";
    G := P/J;
    relativeJacobian := submatrix(jacobian J,toList(0..ns-1),);
    relativeDifferentials := prune coker sub(relativeJacobian,G);
    if rank relativeDifferentials != 1 then
        error "contractionGraphSmallnessData: expected generic relative cone dimension one";
    -- On the integral graph, a generic-rank-one module is locally free of rank
    -- one exactly where its second exterior power vanishes.  Its annihilator
    -- therefore cuts out the same rank-jump support as Fitt_1, without forming
    -- the usually enormous maximal minors of a presentation.
    rankJumpModule := exteriorPower(2,relativeDifferentials);
    rankJumpIdeal := ann rankJumpModule;
    graphVars := flatten entries vars G;
    sourceIrrelevant := ideal take(graphVars,ns);
    targetIrrelevant := ideal drop(graphVars,ns);
    biprojectiveIrrelevant := sourceIrrelevant*targetIrrelevant;
    exceptionalIdeal := saturate(rankJumpIdeal,biprojectiveIrrelevant);
    empty := exceptionalIdeal == ideal 1_G;
    exceptionalDimension := if empty then -1 else dim(G/exceptionalIdeal)-2;
    exceptionalCodimension := if empty then sourceDimension+1
        else sourceDimension-exceptionalDimension;
    new HashTable from {
        "isSmall" => exceptionalCodimension >= 2,
        "sourceDimension" => sourceDimension,
        "exceptionalDimension" => exceptionalDimension,
        "exceptionalCodimension" => exceptionalCodimension,
        "exceptionalLocusEmpty" => empty,
        "relativeDifferentials" => relativeDifferentials,
        "rankJumpModule" => rankJumpModule,
        "rankJumpIdeal" => rankJumpIdeal,
        "exceptionalIdeal" => exceptionalIdeal,
        "criterion" => "codimension of support of exterior^2 of relative differentials",
        "assumptions" => "integral separable birational graph between normal projective varieties"
        }
    )

contractionGraphSmallnessData = method()
contractionGraphSmallnessData HashTable := graph -> (
    if not graph#?"jointRing" or not graph#?"graphIdeal"
        or not graph#?"sourceVariableCount" then
        error "contractionGraphSmallnessData: expected a Stein graph table";
    P := graph#"jointRing";
    J := graph#"graphIdeal";
    ns := graph#"sourceVariableCount";
    contractionGraphSmallnessInternal(P,J,ns,dim(P/J)-2)
    )
contractionGraphSmallnessData GraphMorphism := graph -> (
    P := graph#ambientRing;
    J := graph#definingIdeal;
    ns := #(graph#fiberVariables);
    contractionGraphSmallnessInternal(P,J,ns,dim(graph#sourceRing)-1)
    )

contractionSmallnessData = method()
contractionSmallnessData HashTable := contraction -> (
    if not contraction#?"conclusive" or not contraction#"conclusive" then
        error "contractionSmallnessData: expected a conclusive contraction";
    if not contraction#?"isBirational" or not contraction#"isBirational" then
        error "contractionSmallnessData: expected a birational contraction";
    if not contraction#?"contractionGraph" then
        error "contractionSmallnessData: missing contraction graph";
    contractionGraphSmallnessData contraction#"contractionGraph"
    )

-- Record one MMP step without discarding either graph.  A nonidentity relative
-- model is flipping when the original contraction is small and mixed when it
-- is not; until that independent smallness test is supplied, retain the honest
-- combined classification.
mmpStepRecordData = method(Options => {ContractionIsSmall => null})
mmpStepRecordData HashTable := o -> contraction -> (
    if not contraction#?"conclusive" or not contraction#"conclusive" then
        error "mmpStepRecordData: expected a conclusive contraction";
    if contraction#?"isFibreType" and contraction#"isFibreType" then
        if not contraction#?"contractionGraph"
            or not instance(contraction#"contractionGraph",GraphMorphism) then
            error "mmpStepRecordData: expected a GraphMorphism contraction graph";
        return new HashTable from {
            "stepType" => "fibration",
            "terminal" => true,
            "contractionData" => contraction,
            "contractionGraph" => contraction#"contractionGraph",
            "relativeModelData" => null,
            "relativeModelGraph" => null,
            "inverseRelativeModelData" => null,
            "inverseRelativeModelRequired" => false,
            "nextRing" => null
            };
    error "mmpStepRecordData: a birational contraction also requires relative model data"
    )
mmpStepRecordData (HashTable,HashTable) := o -> (contraction,model) -> (
    if not contraction#?"conclusive" or not contraction#"conclusive" then
        error "mmpStepRecordData: expected a conclusive contraction";
    if not contraction#?"isBirational" or not contraction#"isBirational" then
        error "mmpStepRecordData: expected a birational contraction";
    if not contraction#?"contractionGraph"
        or not instance(contraction#"contractionGraph",GraphMorphism) then
        error "mmpStepRecordData: expected a GraphMorphism contraction graph";
    if not model#?"conclusive" or not model#"conclusive" then
        error "mmpStepRecordData: expected a conclusive relative model";
    small := o.ContractionIsSmall;
    if small =!= null and not instance(small,Boolean) then
        error "mmpStepRecordData: ContractionIsSmall must be null or Boolean";
    smallnessData := null;
    if small === null then (
            smallnessData = contractionSmallnessData contraction;
            small = smallnessData#"isSmall";
            );
    identity := model#"isIdentity";
    inverseData := if identity then null
        else relativeModelInverseRationalMapData model;
    stepType := if identity then "divisorial"
        else if small === true then "flipping"
        else if small === false then "mixed"
        else "flipping-or-mixed";
    new HashTable from {
        "stepType" => stepType,
        "terminal" => false,
        "stepTypeConclusive" => identity or small =!= null,
        "contractionIsSmall" => small,
        "contractionSmallnessData" => smallnessData,
        "contractionData" => contraction,
        "contractionGraph" => contraction#"contractionGraph",
        "relativeModelData" => model,
        "relativeModelGraph" => model#"relativeModelGraph",
        "inverseRelativeModelData" => inverseData,
        "inverseRelativeModelRequired" => not identity,
        "nextRing" => model#"relativeModelRing"
        }
    )

-- The IrrelevantIdeal option (added while extending the BPF fastpath's
-- canonical-ideal-seed idea to isCartier itself; see
-- research-log/docs/CARTIER-INDEX-FASTPATH-AND-CYCLIC-COVER-INVESTIGATION.md)
-- is purely additive: when null (every existing caller), the fallback below
-- is the exact original isCartier(i*K,IsGraded=>true) call, so behaviour is
-- unchanged wherever the new cheap certificates below do not apply.  When
-- supplied, the fallback uses isCartierSaturatedInternal(i*K,B) instead of
-- the generic isCartier, which also fixes a separate, independently
-- documented correctness gap (WeilDivisors' own getIrrelevantIdeal(R) can be
-- wrong on mixed-sign multigraded rings; same report) for any caller that
-- does supply a known-correct B.
canonicalIndexData = method(Options => {
    CanonicalIndexSearchLimit => null, IrrelevantIdeal => null})
canonicalIndexData Ring := o -> R -> (
    limit := o.CanonicalIndexSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalIndexData: CanonicalIndexSearchLimit must be null or positive";
    B := o.IrrelevantIdeal;
    if B =!= null and ring B =!= R then
        error "canonicalIndexData: IrrelevantIdeal must be an ideal of R";
    K := canonicalDivisor(R,IsGraded=>true);
    -- Try the two cheap, certificate-producing sufficient conditions for
    -- Cartier-ness first (no Hom/Ext call); only fall back to the original,
    -- expensive general test when neither applies.  Both certificates can
    -- only return true or null, never false, so this can only find a
    -- correct "yes" earlier -- it never changes any "no" verdict the
    -- original loop would have produced.
    isCartierAtIndex := m -> (
        candidate := m*K;
        if principalShiftCartierCertificateInternal candidate then true
        else (
            seedCert := canonicalIdealSeedInvertibleInternal(R,K,m);
            if seedCert =!= null then seedCert
            else if B =!= null then isCartierSaturatedInternal(candidate,B)
            else isCartier(candidate,IsGraded=>true)
            )
        );
    i := 1;
    while (limit === null or i <= limit)
        and not isCartierAtIndex i do i = i+1;
    if limit =!= null and i > limit then
        return new HashTable from {
            "conclusive" => false,
            "index" => null,
            "multiplesTested" => limit,
            "canonicalDivisor" => K
            };
    new HashTable from {
        "conclusive" => true,
        "index" => i,
        "multiplesTested" => i,
        "canonicalDivisor" => K
        }
    )

threefoldMMPData = method(Options => {
    MMPMaxSteps => null,
    CanonicalIndexSearchLimit => null,
    NefSearchLimit => null,
    ThresholdSearchLimit => null,
    ContractionMultipleLimit => null,
    RelativeCanonicalMultipliers => null,
    RelativeCanonicalMaxMultiplier => 24,
    RelativeCanonicalVerbose => false,
    IrrelevantIdeal => null})
threefoldMMPData (Ring,ZZ) := o -> (initialRing,initialIndex) ->
    threefoldMMPData(initialRing,initialIndex,{},
        MMPMaxSteps=>o.MMPMaxSteps,
        CanonicalIndexSearchLimit=>o.CanonicalIndexSearchLimit,
        NefSearchLimit=>o.NefSearchLimit,
        ThresholdSearchLimit=>o.ThresholdSearchLimit,
        ContractionMultipleLimit=>o.ContractionMultipleLimit,
        RelativeCanonicalMultipliers=>o.RelativeCanonicalMultipliers,
        RelativeCanonicalMaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
        RelativeCanonicalVerbose=>o.RelativeCanonicalVerbose)
threefoldMMPData (Ring,ZZ,List) := o -> (initialRing,initialIndex,initialSteps) -> (
    if initialIndex <= 0 then
        error "threefoldMMPData: the initial index multiple must be positive";
    if any(initialSteps,entry -> not instance(entry,HashTable)) then
        error "threefoldMMPData: initial steps must be hash tables";
    if any(initialSteps,entry -> not entry#?"stepType" or not entry#?"terminal") then
        error "threefoldMMPData: each initial step needs stepType and terminal fields";
    if any(initialSteps,entry -> entry#"terminal") then
        error "threefoldMMPData: cannot continue after a terminal initial step";
    if any(initialSteps,entry -> not entry#?"nextRing") then
        error "threefoldMMPData: each initial step needs a nextRing field";
    if #initialSteps > 0 and (last initialSteps)#"nextRing" =!= initialRing then
        error "threefoldMMPData: the last initial step does not lead to the current ring";
    maxSteps := o.MMPMaxSteps;
    if maxSteps =!= null and (not instance(maxSteps,ZZ) or maxSteps <= 0) then
        error "threefoldMMPData: MMPMaxSteps must be null or positive";
    currentRing := initialRing;
    currentIndex := initialIndex;
    records := initialSteps;
    iteration := 0;
    while maxSteps === null or iteration < maxSteps do (
        nefData := canonicalNefData(
            currentRing,currentIndex,NefSearchLimit=>o.NefSearchLimit);
        if not nefData#"conclusive" then
            return new HashTable from {
                "conclusive" => false,
                "phase" => "nefness",
                "currentRing" => currentRing,
                "currentIndex" => currentIndex,
                "steps" => records,
                "nefData" => nefData
                };
        if nefData#"nef" then
            return new HashTable from {
                "conclusive" => true,
                "terminationType" => "minimal model",
                "finalRing" => currentRing,
                "finalIndex" => currentIndex,
                "steps" => records,
                "numberOfSteps" => #records,
                "finalNefData" => nefData
                };
        contraction := canonicalContractionData(
            currentRing,currentIndex,
            ThresholdSearchLimit=>o.ThresholdSearchLimit,
            ContractionMultipleLimit=>o.ContractionMultipleLimit);
        if not contraction#"conclusive" then
            return new HashTable from {
                "conclusive" => false,
                "phase" => "contraction",
                "currentRing" => currentRing,
                "currentIndex" => currentIndex,
                "steps" => records,
                "contractionData" => contraction
                };
        if contraction#"isFibreType" then (
            record := mmpStepRecordData contraction;
            records = append(records,record);
            return new HashTable from {
                "conclusive" => true,
                "terminationType" => "K-negative fibration",
                "finalRing" => currentRing,
                "finalIndex" => currentIndex,
                "steps" => records,
                "numberOfSteps" => #records,
                "finalContraction" => contraction
                };
            );
        model := relativeCanonicalModelData(
            contraction,
            RelativeCanonicalMultipliers=>o.RelativeCanonicalMultipliers,
            RelativeCanonicalMaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
            RelativeCanonicalVerbose=>o.RelativeCanonicalVerbose);
        if not model#"conclusive" then
            return new HashTable from {
                "conclusive" => false,
                "phase" => "relative canonical model",
                "currentRing" => currentRing,
                "currentIndex" => currentIndex,
                "steps" => records,
                "finalContraction" => contraction,
                "relativeModelData" => model,
                "warning" => model#"warning"
                };
        record = mmpStepRecordData(contraction,model);
        records = append(records,record);
        currentRing = record#"nextRing";
        indexData := canonicalIndexData(
            currentRing,CanonicalIndexSearchLimit=>o.CanonicalIndexSearchLimit);
        if not indexData#"conclusive" then
            return new HashTable from {
                "conclusive" => false,
                "phase" => "canonical index",
                "currentRing" => currentRing,
                "steps" => records,
                "indexData" => indexData
                };
        currentIndex = indexData#"index";
        iteration = iteration+1;
        );
    new HashTable from {
        "conclusive" => false,
        "phase" => "MMP step limit",
        "currentRing" => currentRing,
        "currentIndex" => currentIndex,
        "steps" => records,
        "stepsRun" => iteration,
        "warning" => "the optional MMP step limit was reached"
        }
    )

-- Iterated multigrading, Phase 1 (research-log/docs/ITERATED-MULTIGRADING-MMP-PLAN.md):
-- the top-level multigraded entry point.  The caller supplies the ample
-- Cartier class H and irrelevant ideal B for the *current* multigraded
-- presentation, so this first iteration's nefness test and contraction reuse
-- canonicalNefData/canonicalContractionData's existing (Ring,ZZ,BasicDivisor)
-- overloads verbatim -- no flattening to a monograded presentation is done
-- here, and no contraction graph or post-flip ring is supplied by the caller.
--
-- relativeCanonicalModelFromBaseData (and hence the Stein-factorization
-- target it builds on) still assumes a monograded base ring today, so once a
-- birational step is recorded, the resulting nextRing is monograded and
-- subsequent iterations fall back to the existing (Ring,ZZ,List) loop.  That
-- boundary is Phase 3/4 of the plan, not this phase; recording it here rather
-- than papering over it is deliberate.
threefoldMMPData (Ring,ZZ,BasicDivisor) := o -> (initialRing,initialIndex,H) -> (
    if initialIndex <= 0 then
        error "threefoldMMPData: the initial index multiple must be positive";
    if ring H =!= initialRing then
        error "threefoldMMPData: H must be a divisor on the initial ring";
    maxSteps := o.MMPMaxSteps;
    if maxSteps =!= null and (not instance(maxSteps,ZZ) or maxSteps <= 0) then
        error "threefoldMMPData: MMPMaxSteps must be null or positive";
    B := o.IrrelevantIdeal;
    if B =!= null and ring B =!= initialRing then
        error "threefoldMMPData: IrrelevantIdeal must be an ideal of the initial ring";
    nefData := canonicalNefData(initialRing,initialIndex,H,
        NefSearchLimit=>o.NefSearchLimit,IrrelevantIdeal=>B);
    if not nefData#"conclusive" then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "nefness",
            "currentRing" => initialRing,
            "currentIndex" => initialIndex,
            "steps" => {},
            "nefData" => nefData
            };
    if nefData#"nef" then
        return new HashTable from {
            "conclusive" => true,
            "terminationType" => "minimal model",
            "finalRing" => initialRing,
            "finalIndex" => initialIndex,
            "steps" => {},
            "numberOfSteps" => 0,
            "finalNefData" => nefData
            };
    contraction := canonicalContractionData(
        initialRing,initialIndex,H,
        ThresholdSearchLimit=>o.ThresholdSearchLimit,
        ContractionMultipleLimit=>o.ContractionMultipleLimit,
        IrrelevantIdeal=>B);
    if not contraction#"conclusive" then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "contraction",
            "currentRing" => initialRing,
            "currentIndex" => initialIndex,
            "steps" => {},
            "contractionData" => contraction
            };
    if contraction#"isFibreType" then (
        record := mmpStepRecordData contraction;
        return new HashTable from {
            "conclusive" => true,
            "terminationType" => "K-negative fibration",
            "finalRing" => initialRing,
            "finalIndex" => initialIndex,
            "steps" => {record},
            "numberOfSteps" => 1,
            "finalContraction" => contraction
            };
        );
    model := relativeCanonicalModelData(
        contraction,
        RelativeCanonicalMultipliers=>o.RelativeCanonicalMultipliers,
        RelativeCanonicalMaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
        RelativeCanonicalVerbose=>o.RelativeCanonicalVerbose);
    if not model#"conclusive" then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "relative canonical model",
            "currentRing" => initialRing,
            "currentIndex" => initialIndex,
            "steps" => {},
            "finalContraction" => contraction,
            "relativeModelData" => model,
            "warning" => model#"warning"
            };
    record = mmpStepRecordData(contraction,model);
    nextRing := record#"nextRing";
    indexData := canonicalIndexData(
        nextRing,CanonicalIndexSearchLimit=>o.CanonicalIndexSearchLimit);
    if not indexData#"conclusive" then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "canonical index",
            "currentRing" => nextRing,
            "steps" => {record},
            "indexData" => indexData
            };
    remainingSteps := if maxSteps === null then null else maxSteps-1;
    if maxSteps =!= null and remainingSteps <= 0 then
        return new HashTable from {
            "conclusive" => false,
            "phase" => "MMP step limit",
            "currentRing" => nextRing,
            "currentIndex" => indexData#"index",
            "steps" => {record},
            "stepsRun" => 1,
            "warning" => "the optional MMP step limit was reached"
            };
    threefoldMMPData(nextRing,indexData#"index",{record},
        MMPMaxSteps=>remainingSteps,
        CanonicalIndexSearchLimit=>o.CanonicalIndexSearchLimit,
        NefSearchLimit=>o.NefSearchLimit,
        ThresholdSearchLimit=>o.ThresholdSearchLimit,
        ContractionMultipleLimit=>o.ContractionMultipleLimit,
        RelativeCanonicalMultipliers=>o.RelativeCanonicalMultipliers,
        RelativeCanonicalMaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
        RelativeCanonicalVerbose=>o.RelativeCanonicalVerbose)
    )

-- Proposition 3.8 for threefolds.  Run the two terminating searches in
-- parallel: global generation of a reflexive pluricanonical sheaf proves nef,
-- while failure of nefness for K_X+2^{-j}H proves non-nef.  NefSearchLimit is
-- an optional practical bound; null means the mathematical unbounded search.
--
-- Stage 1 (T3): factored into a shared core (no dimension-dependent step of
-- its own, so nothing here needed the T1 geometric dimension except the
-- "expected a projective threefold" gate each entry point checks itself)
-- so the multigraded entry point below can reuse it verbatim.
--
-- Part 0 of the Stage 2 measurement work (completing Stage 1's T1/T3): the
-- trailing B threads a caller-supplied irrelevant ideal into both of this
-- loop's own base-point-free tests (the pluricanonical divisor's, and the one
-- inside canonicalScaledNefDataInternal), not only into whichever entry
-- point's own Cartier/threefold gate built this call.  B = null reproduces
-- the previous behaviour exactly.
canonicalNefDataCore = (R,a,K,H,limit,B,classDegrees) -> (
    i := 1;
    while limit === null or i <= limit do (
        pluricanonical := i*a*K;
        pluricanonicalModule := if classDegrees =!= null
            then gradedShiftModuleFromDegree(R,
                i*a*(classDegrees#0))
            else null;
        pluricanonicalBPF := if pluricanonicalModule =!= null
            then basePointFreeModuleInternal(pluricanonicalModule,
                if B =!= null then B
                else verifiedIrrelevantIdeal(R,null))
        else (
            seedBPF := canonicalIdealSeedBPFInternal(
                R,K,i*a,0,H,
                if B =!= null then B
                else verifiedIrrelevantIdeal(R,null));
            if seedBPF === null then (
                if B =!= null
                    then isBasePointFreeDivisor(pluricanonical,B)
                    else isBasePointFreeDivisor pluricanonical
                ) else seedBPF
            );
        if pluricanonicalBPF then
            return new HashTable from {
                "nef" => true,
                "conclusive" => true,
                "witnessType" => "base-point-free pluricanonical divisor",
                "iteration" => i,
                "witnessDivisor" => pluricanonical,
                "canonicalDivisor" => K
                };
        scaledData := canonicalScaledNefDataInternal(
            R,K,H,a,1/(2^i),B,classDegrees);
        if not scaledData#"nef" then
            return new HashTable from {
                "nef" => false,
                "conclusive" => true,
                "witnessType" => "non-nef positive perturbation",
                "iteration" => i,
                "witnessT" => 1/(2^i),
                "scaledTest" => scaledData,
                "canonicalDivisor" => K
                };
        i = i+1;
        );
    new HashTable from {
        "nef" => null,
        "conclusive" => false,
        "iterationsRun" => limit,
        "canonicalDivisor" => K,
        "warning" => "the optional search limit was reached"
        }
    )

canonicalNefData = method(Options => {
    NefSearchLimit => null,
    IrrelevantIdeal => null,
    DivisorClassDegrees => null})
canonicalNefData (Ring,ZZ) := o -> (R,a) -> (
    if dim R - 1 != 3 then
        error "canonicalNefData: expected a projective threefold";
    if a <= 0 then
        error "canonicalNefData: the index multiple must be positive";
    limit := o.NefSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalNefData: NefSearchLimit must be null or positive";
    K := canonicalDivisor(R,IsGraded=>true);
    if not isCartier(a*K,IsGraded=>true) then
        error "canonicalNefData: a*K_X is not Cartier";
    ampleData := weightedAmpleDivisorData R;
    H := ampleData#"divisor";
    classDegrees := normalizeDivisorClassDegrees(
        R,o.DivisorClassDegrees,"canonicalNefData");
    result := canonicalNefDataCore(R,a,K,H,limit,null,classDegrees);
    new HashTable from join(pairs result,{"ampleData" => ampleData})
    )

-- Stage 1 (T3): the multigraded entry point, using T1's geometric dimension
-- for the threefold gate, a caller-supplied ample Cartier class (plan
-- section 3.5), and T2's saturated Cartier test.
--
-- Stage 2 (T1): if o.IrrelevantIdeal is supplied, multigradedBlockData is
-- bypassed entirely, including for the threefold gate's dimension check
-- (dim R - degreeLength R; see canonicalNefThresholdData's comment for the
-- verification this agrees with multigradedBlockData's own field on the
-- plan's Z).
--
-- Part 0 of the Stage 2 measurement work (completing Stage 1's T1/T3, not
-- new Stage 2 scope -- see canonicalNefDataCore's own comment): B is now
-- threaded into canonicalNefDataCore, so its internal base-point-free search
-- (both the pluricanonical-divisor test and the nested scaled-nef test)
-- honors the caller-supplied ideal too, not only this entry point's own
-- threefold and Cartier gates.
canonicalNefData (Ring,ZZ,BasicDivisor) := o -> (R,a,H) -> (
    if a <= 0 then
        error "canonicalNefData: the index multiple must be positive";
    if ring H =!= R then
        error "canonicalNefData: H must be a divisor on R";
    limit := o.NefSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalNefData: NefSearchLimit must be null or positive";
    suppliedB := o.IrrelevantIdeal;
    if suppliedB =!= null and ring suppliedB =!= R then
        error "canonicalNefData: IrrelevantIdeal must be an ideal of R";
    blockData := if suppliedB === null then multigradedBlockData R else null;
    if blockData =!= null and not blockData#"verifiedBlockDiagonal" then error(
        "this ring has a skew (mixed-degree) multigraded variable, so "
        | "multigradedBlockData's block-classification heuristic cannot "
        | "reliably determine the irrelevant ideal (see "
        | "tests/multigraded-skew-cartier.m2).  Supply the ring's true "
        | "irrelevant ideal explicitly via IrrelevantIdeal=>B.");
    geometricDimension := if suppliedB =!= null then dim R - degreeLength R
        else blockData#"geometricDimension";
    if geometricDimension != 3 then
        error "canonicalNefData: expected a projective threefold";
    K := canonicalDivisor(R,IsGraded=>true);
    B := if suppliedB =!= null then suppliedB else blockData#"irrelevantIdeal";
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalNefData: a*K_X is not Cartier";
    classDegrees := normalizeDivisorClassDegrees(
        R,o.DivisorClassDegrees,"canonicalNefData");
    result := canonicalNefDataCore(R,a,K,H,limit,B,classDegrees);
    extraKeys := if suppliedB =!= null then {
        "irrelevantIdeal" => B, "irrelevantIdealSource" => "caller-supplied"}
        else {"blockData" => blockData};
    new HashTable from join(pairs result,join({
        "ampleData" => new HashTable from {"ring" => R,"divisor" => H}},
        extraKeys))
    )

isCanonicalNef = method(Options => options canonicalNefData)
isCanonicalNef (Ring,ZZ) := o -> (R,a) -> (
    result := canonicalNefData(R,a,
        NefSearchLimit=>o.NefSearchLimit,
        DivisorClassDegrees=>o.DivisorClassDegrees);
    if not result#"conclusive" then
        error "isCanonicalNef: the optional search limit was reached";
    result#"nef"
    )

beginDocumentation()
doc ///
Node
  Key
    MMPComputation
  Headline
    computations for the minimal model program in dimension three
  Description
    Text
      This research package implements the integration-layer algorithms in
      Takehiko Yasuda, {em An algorithm for the minimal model program in
      dimension three}.  It can test canonical nefness, find the nef
      threshold, construct the associated contraction and relative canonical
      model, and iterate these operations until it reaches a minimal model or
      a $K_X$-negative fibration.

      For a first computation, load the package, define the homogeneous
      coordinate ring @TT "R"@, and call @TO threefoldMMPData@.  Its second
      argument is a known positive integer @TT "a"@ for which $aK_X$ is
      Cartier.  Use @TO canonicalIndexData@ first if this integer is unknown.
      For example:
    Example
      needsPackage("MMPComputation", FileName => "MMPComputation.m2");
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      segreResult = threefoldMMPData(X,1);
      segreResult#"terminationType"
      segreResult#"finalContraction"#"threshold"
      segreResult#"finalContraction"#"targetDimension"
    Text
      Here is a nontrivial quotient-ring example.  Let $X$ be the Segre
      embedding of $\mathbb{P}^1\times\mathbb{P}^2$ in $\mathbb{P}^5$.
      Its canonical divisor is $\mathcal{O}_X(-2,-3)$ and the hyperplane
      class is $H=\mathcal{O}_X(1,1)$.  The package finds the threshold 3;
      the threshold divisor $K_X+3H=\mathcal{O}_X(1,0)$ gives the projection
      to $\mathbb{P}^1$.
    Text
      All main entry points assume that $\operatorname{Proj}(R)$ is a normal
      log terminal projective threefold; they do not prove these hypotheses.
      Since a projective threefold has a four-dimensional homogeneous
      coordinate ring, the package checks @TT "dim R - 1 == 3"@.

      A returned table with @TT "conclusive"@ set to @TT "true"@ contains a
      certified answer.  If an optional search bound is reached, the value is
      false, @TT "phase"@ says where computation stopped, and the table retains
      the partial results.  This is not a mathematical counterexample.

      Most users need only @TO threefoldMMPData@: read its
      @TT "terminationType"@ and @TT "numberOfSteps"@ fields first.  To ask
      just one question, use @TO isCanonicalNef@ for a Boolean answer or,
      after obtaining false, @TO canonicalNefThreshold@ for the rational
      threshold.

      Functions whose names end in @TT "Data"@ return a @TO HashTable@ of
      intermediate objects and certificates.  They are intended for checking
      how an answer was obtained, not as the first introduction to the
      package.  @TO canonicalIndexData@ is the one setup exception: when
      @TT "a"@ is unknown, call it and read its @TT "index"@ field.
  Subnodes
    :Start here: run the program
    threefoldMMPData
    canonicalIndexData
    :Short answers
    isCanonicalNef
    canonicalNefThreshold
    isBasePointFreeDivisor
    :Detailed results and certificates
    canonicalNefData
    canonicalNefThresholdData
    canonicalContractionData
    :Individual pipeline stages
    weightedAmpleDivisorData
    effectiveNefMultiplier
    canonicalScaledNefData
    canonicalContractionAtThresholdData
    contractionTypeData
    completeLinearSystemGraphData
    mmpGraphMorphism
    :Relative canonical model and flips
    relativeCanonicalModelData
    relativeCanonicalModelFromBaseData
    relativeCanonicalModelIsomorphismData
    relativeModelInverseRationalMapData
    :Smallness and step records
    contractionSmallnessData
    contractionGraphSmallnessData
    mmpStepRecordData
    :Multigraded (non-flattened) presentations
    diagonalSubalgebraData
    completeLinearSystemGraphDataMultigraded
    negativeCurveWitnessData

Node
  Key
    mmpGraphMorphism
    (mmpGraphMorphism,GraphMorphism)
    (mmpGraphMorphism,HashTable)
  Headline
    normalize a morphism graph to the common representation
  Usage
    normalized = mmpGraphMorphism graph
  Description
    Text
      Return a @TO GraphMorphism@ unchanged, or adapt a legacy integration or
      Stein graph table carrying its source and target coordinate rings.  New
      contraction and relative-model results expose their public graphs in
      this representation, while retaining raw computation tables separately
      as certificates.
  SeeAlso
    canonicalContractionData
    relativeCanonicalModelData

Node
  Key
    threefoldMMPData
    (threefoldMMPData,Ring,ZZ)
    (threefoldMMPData,Ring,ZZ,List)
    (threefoldMMPData,Ring,ZZ,BasicDivisor)
  Headline
    run the three-dimensional minimal model program
  Usage
    result = threefoldMMPData(R,a)
    result = threefoldMMPData(R,a,steps)
    result = threefoldMMPData(R,a,H)
  Inputs
    R:Ring
      the homogeneous coordinate ring of the current projective threefold
    a:ZZ
      a positive integer such that $aK_X$ is Cartier
    steps:List
      optional certified, nonterminal step records from an earlier run
    H:BasicDivisor
      optional ample Cartier divisor for a multigraded presentation
  Outputs
    :HashTable
      the termination status, final ring, and ordered list of MMP step records
  Description
    Text
      Starting with a positive Cartier index multiple for $K_X$, iterate the
      nefness, threshold, contraction, relative-model, smallness, and index
      computations.  Return the graph-preserving step sequence and stop at a
      minimal model or a $K_X$-negative fibration.  The three-argument form with a
      @TO List@ continues from a current model while retaining certified
      preceding nonterminal step records; the last record must lead to the
      supplied current ring.  The three-argument form with a
      @TO BasicDivisor@ runs the first iteration on the caller-supplied
      multigraded presentation directly, using @TT "H"@ as the ample Cartier
      class and the optional @TT "IrrelevantIdeal=>B"@ as the irrelevant
      ideal of that presentation, without flattening it to a monograded ring
      first; once a birational step is recorded the resulting ring is
      monograded (a current limitation of @TO relativeCanonicalModelData@,
      not of this entry point), so later iterations fall back to the
      @TO List@ form automatically.

      In a conclusive result, @TT "terminationType"@ is either
      @TT "minimal model"@ or @TT "K-negative fibration"@, and @TT "steps"@ is
      the complete ordered step list.  @TT "finalRing"@ and
      @TT "finalIndex"@ describe the terminal presentation.  In an
      inconclusive result, @TT "phase"@ identifies the search limit that was
      reached and @TT "steps"@ still contains every completed step.

      The fibration conclusion means that the final morphism is surjective
      with connected fibres, its target has smaller dimension, and $-K_X$ is
      relatively ample.  The package does not compute the relative Picard
      number and therefore makes no relative-Picard-number-one conclusion.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      result = threefoldMMPData(X,1);
      result#"terminationType"
      result#"numberOfSteps"

Node
  Key
    canonicalIndexData
    (canonicalIndexData,Ring)
  Headline
    find the Cartier index of the canonical divisor
  Usage
    result = canonicalIndexData R
  Inputs
    R:Ring
      the homogeneous coordinate ring of a normal projective variety
  Outputs
    :HashTable
      a table whose @TT "index"@ field is the least positive integer $r$ for
      which $rK_X$ is Cartier
  Description
    Text
      Search increasing multiples of $K_X$ for the first one that is
      Cartier, using cheap sufficient certificates before falling back to
      the general test.  A smooth variety always has index 1.
    Example
      S = QQ[y0,y1,y2,y3,y4];
      X = S/ideal(y0^5+y1^5+y2^5+y3^5+y4^5);
      (canonicalIndexData X)#"index"

Node
  Key
    relativeModelInverseRationalMapData
    (relativeModelInverseRationalMapData,HashTable)
  Headline
    recover the rational inverse of a relative-model projection
  Usage
    result = relativeModelInverseRationalMapData model
  Description
    Text
      For a nonidentity relative canonical model $Z \longrightarrow W$
      constructed as a relative $\operatorname{Proj}$ of a Rees algebra,
      substitute the Rees-ideal generators for the
      fibre variables in the Segre coordinates.  The result records homogeneous
      coordinates for $W \dashrightarrow Z$, verifies the model and graph
      equations, and certifies that their base locus is the Rees centre after
      saturation.  Skew weighted fibre coordinates use the positive diagonal
      selected internally by {tt b2mDiagonalData}.
    Example
      needsPackage "Polyhedra";
      rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
      HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
          v -> flatten entries v);
      L = QQ[t1,t2,t3];
      S0 = QQ[y_1 .. y_(#HB)];
      I0 = ker map(L,S0,apply(HB,h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
      S = QQ[y_1 .. y_(#HB),w];
      W = S/sub(I0,S);
      flipModel = relativeCanonicalModelFromBaseData(W,RelativeCanonicalMultipliers=>{1});
      inverseModel = relativeModelInverseRationalMapData flipModel;
      inverseModel#"modelRelationsVanish"
  SeeAlso
    relativeCanonicalModelData
    mmpStepRecordData

Node
  Key
    contractionGraphSmallnessData
    (contractionGraphSmallnessData,HashTable)
    (contractionGraphSmallnessData,GraphMorphism)
  Headline
    test smallness from a birational contraction graph
  Usage
    result = contractionGraphSmallnessData graph
  Description
    Text
      The affine cone over a birational biprojective graph has generic relative
      differential rank one, coming from source scaling.  The support of its
      second exterior power is the rank-jump locus.  After biprojective
      saturation, the contraction is small precisely when that locus has
      codimension at least two in the source.  The graph is assumed integral
      and the birational extension separable.
    Example
      ODP = QQ[o0,o1,o2,o3,o4]/ideal(o0*o1-o2*o3);
      smallGraph = b2mToGraphMorphism bigradedReesProjection ideal(o0,o2);
      smallness = contractionGraphSmallnessData smallGraph;
      {smallness#"isSmall",smallness#"exceptionalCodimension"}

Node
  Key
    contractionSmallnessData
    (contractionSmallnessData,HashTable)
  Headline
    test smallness of a computed birational contraction
  Usage
    result = contractionSmallnessData contraction
  Description
    Text
      Apply @TO contractionGraphSmallnessData@ to the graph stored in a
      conclusive birational contraction result.
    Example
      ODP = QQ[o0,o1,o2,o3,o4]/ideal(o0*o1-o2*o3);
      smallGraph = b2mToGraphMorphism bigradedReesProjection ideal(o0,o2);
      contraction = new HashTable from {
          "conclusive" => true, "isBirational" => true,
          "contractionGraph" => smallGraph};
      (contractionSmallnessData contraction)#"isSmall"
  SeeAlso
    contractionGraphSmallnessData

Node
  Key
    mmpStepRecordData
    (mmpStepRecordData,HashTable)
    (mmpStepRecordData,HashTable,HashTable)
  Headline
    record a graph-preserving MMP step
  Usage
    record = mmpStepRecordData contraction
    record = mmpStepRecordData(contraction,model)
  Description
    Text
      Fibre-type and divisorial steps are determined directly.  A nonidentity
      relative model is recorded as flipping or mixed when the smallness of the
      original contraction is supplied, and otherwise as flipping-or-mixed.
      Both the contraction graph and relative-model graph remain in the record.
    Example
      S = QQ[y1,y2,y3,y4,y5,w];
      W = S/ideal(y4^2-y2*y5,y3*y4-y1*y5,y2*y3-y1*y4);
      model = relativeCanonicalModelFromBaseData(
          W,RelativeCanonicalMultipliers=>{1});
      contraction = new HashTable from {
          "conclusive" => true,
          "isBirational" => true,
          "contractionGraph" => model#"relativeModelGraph"
          };
      stepResult = mmpStepRecordData(
          contraction,model,ContractionIsSmall=>true);
      {stepResult#"stepType",stepResult#"inverseRelativeModelRequired"}

Node
  Key
    relativeCanonicalModelIsomorphismData
    (relativeCanonicalModelIsomorphismData,HashTable)
  Headline
    decide whether a relative canonical model is the identity
  Usage
    result = relativeCanonicalModelIsomorphismData model
  Description
    Text
      The relative model is an isomorphism precisely when its canonical
      blow-up ideal is locally free of rank one.  The model computation tests
      this using the first Fitting ideal and saturation by the irrelevant ideal.
    Example
      S = QQ[y1,y2,y3,y4,y5,w];
      W = S/ideal(y4^2-y2*y5,y3*y4-y1*y5,y2*y3-y1*y4);
      model = relativeCanonicalModelFromBaseData(
          W,RelativeCanonicalMultipliers=>{1});
      relativeCanonicalModelIsomorphismData model

Node
  Key
    relativeCanonicalModelFromBaseData
    (relativeCanonicalModelFromBaseData,Ring)
  Headline
    compute the relative canonical model over a contraction base
  Usage
    result = relativeCanonicalModelFromBaseData W
  Description
    Text
      If the canonical module of the projective threefold $W$ embeds as the
      unit ideal, return the identity model.  Otherwise run the relative
      canonical algebra computation and return its graph morphism.  In the
      example below, @TT "W"@ is a non-$\mathbb{Q}$-Gorenstein projective
      toric threefold.  Thus its relative canonical model is genuinely
      computed, rather than returned as an identity model.
    Example
      S = QQ[y1,y2,y3,y4,y5,w];
      W = S/ideal(y4^2-y2*y5,y3*y4-y1*y5,y2*y3-y1*y4);
      model = relativeCanonicalModelFromBaseData(
          W,RelativeCanonicalMultipliers=>{1});
      model#"relativeModelType"
      dim model#"relativeModelRing"-1

Node
  Key
    relativeCanonicalModelData
    (relativeCanonicalModelData,HashTable)
  Headline
    compute the next model from a birational contraction result
  Usage
    result = relativeCanonicalModelData contraction
  Description
    Text
      Extract the contraction target from @TT "contraction"@ and delegate to
      @TO relativeCanonicalModelFromBaseData@.  This is the form used by
      @TO threefoldMMPData@ between successive birational steps.  The example
      supplies the relevant fields of a birational contraction whose target
      is the same non-$\mathbb{Q}$-Gorenstein toric threefold used in
      @TO relativeCanonicalModelFromBaseData@.
    Example
      S = QQ[y1,y2,y3,y4,y5,w];
      W = S/ideal(y4^2-y2*y5,y3*y4-y1*y5,y2*y3-y1*y4);
      contraction = new HashTable from {
          "conclusive" => true,
          "isBirational" => true,
          "steinAlgebraData" => new HashTable from {"ring" => W}
          };
      model = relativeCanonicalModelData(
          contraction,RelativeCanonicalMultipliers=>{1});
      {model#"relativeModelType",model#"isIdentity"}
  SeeAlso
    relativeCanonicalModelFromBaseData
    canonicalContractionData

Node
  Key
    contractionTypeData
    (contractionTypeData,ZZ,ZZ)
  Headline
    classify a connected-fibre contraction by dimension
  Usage
    result = contractionTypeData(sourceDimension,targetDimension)
  Description
    Text
      Return birational when the two dimensions agree and fibration when the
      target has smaller dimension.  Contraction results include the same
      classification fields automatically.
    Example
      contractionTypeData(3,3)
      contractionTypeData(3,1)

Node
  Key
    completeLinearSystemGraphData
    (completeLinearSystemGraphData,BasicDivisor)
  Headline
    construct the graph of a complete base-point-free linear system
  Usage
    graphData = completeLinearSystemGraphData D
  Description
    Text
      Construct the closure of the graph of the morphism defined by the
      complete linear system of @TT "D"@.  The returned @TT "graph"@ uses the
      package-wide @TO GraphMorphism@ representation.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      H = (weightedAmpleDivisorData X)#"divisor";
      graphData = completeLinearSystemGraphData H;
      {graphData#"targetVariableCount",dim graphData#"graph"#totalRing}

Node
  Key
    diagonalSubalgebraData
  Headline
    flatten a multigraded ring to the diagonal subalgebra of an ample class
  Usage
    data = diagonalSubalgebraData(R,w)
  Inputs
    R:Ring
      a multigraded ring
    w:BasicDivisor
      a very ample divisor class on R
  Outputs
    :HashTable
      the singly graded diagonal subalgebra of R and its section map from R
  Description
    Text
      Build the subring generated by the degree-@TT "w"@ strand of $R$, i.e.
      the image of the rational map given by a spanning set of sections of
      @TT "w"@.  When @TT "w"@ is very ample this is an isomorphic singly
      graded presentation of the same variety; used internally to bridge
      multigraded presentations into {tt SteinFactorization}'s
      block-diagonal bigraded requirement.
    Example
      needsPackage "WeilDivisors";
      S = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
      H = divisor(s) + divisor(u);
      flattening = diagonalSubalgebraData(S,H);
      degreeLength flattening#"flatRing"
  SeeAlso
    completeLinearSystemGraphDataMultigraded

Node
  Key
    completeLinearSystemGraphDataMultigraded
    (completeLinearSystemGraphDataMultigraded,BasicDivisor,BasicDivisor)
  Headline
    construct the graph of a base-point-free system on a multigraded ring
  Usage
    graphData = completeLinearSystemGraphDataMultigraded(D,w)
  Inputs
    D:BasicDivisor
      a base-point-free divisor on a multigraded ring R
    w:BasicDivisor
      a very ample divisor class on R, used to flatten the source
  Outputs
    :HashTable
      the graph data of D's complete linear system
  Description
    Text
      The multigraded companion of @TO completeLinearSystemGraphData@: the
      source side of the graph is built from @TO diagonalSubalgebraData@'s
      flattened ring, since {tt SteinFactorization} requires a block-diagonal
      bigraded presentation, while D's own sections still come from R
      directly.
    Example
      needsPackage "WeilDivisors";
      S = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
      D = divisor u;
      H = divisor(s) + divisor(u);
      g = completeLinearSystemGraphDataMultigraded(D,H);
      g#"sectionImages"
  SeeAlso
    diagonalSubalgebraData

Node
  Key
    canonicalContractionAtThresholdData
    (canonicalContractionAtThresholdData,Ring,ZZ,QQ)
    (canonicalContractionAtThresholdData,Ring,ZZ,ZZ)
  Headline
    construct the contraction at a known canonical nef threshold
  Usage
    result = canonicalContractionAtThresholdData(R,a,lambda)
  Description
    Text
      Find a base-point-free multiple of $K_X+\lambda H$, construct its
      complete-linear-system graph, and compute its Stein factorization.  The
      function tests small multiples first and is guaranteed to stop at the
      effective multiplier from the scaled nefness theorem.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      contraction = canonicalContractionAtThresholdData(X,1,3);
      {contraction#"sourceDimension",contraction#"targetDimension"}

Node
  Key
    canonicalContractionData
    (canonicalContractionData,Ring,ZZ)
  Headline
    compute the canonical nef threshold and its extremal-face contraction
  Usage
    result = canonicalContractionData(R,a)
  Inputs
    R:Ring
      the homogeneous coordinate ring of a normal log terminal threefold
    a:ZZ
      a positive integer such that $aK_X$ is Cartier
  Outputs
    :HashTable
      the threshold, contraction graph, dimensions, and contraction type
  Description
    Text
      Compute the canonical nef threshold with @TO canonicalNefThresholdData@,
      then construct the contraction at that threshold.  Assumes $K_X$ is not
      already nef.  In a conclusive result, inspect @TT "threshold"@,
      @TT "contractionType"@, @TT "sourceDimension"@,
      @TT "targetDimension"@, and @TT "contractionGraph"@.  The example is
      the Segre threefold $\mathbb{P}^1\times\mathbb{P}^2$: the computed
      threshold is 3 and $K_X+3H=\mathcal{O}_X(1,0)$ contracts it to
      $\mathbb{P}^1$.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      contraction = canonicalContractionData(X,1);
      {contraction#"threshold",contraction#"contractionType",
          contraction#"targetDimension"}
  SeeAlso
    canonicalNefThresholdData
    canonicalContractionAtThresholdData

Node
  Key
    canonicalNefThresholdData
    (canonicalNefThresholdData,Ring,ZZ)
  Headline
    compute the canonical nef threshold and its search data
  Usage
    result = canonicalNefThresholdData(R,a)
  Inputs
    R:Ring
      the homogeneous coordinate ring of a normal log terminal threefold
    a:ZZ
      a positive integer such that $aK_X$ is Cartier
  Outputs
    :HashTable
      the rational threshold in @TT "threshold"@ and its search certificates
  Description
    Text
      Assuming that $K_X$ is not nef, compute the first positive rational
      $t$ for which $K_X+tH$ is nef.  The function implements Algorithm 1:
      dyadic searches bracket the threshold and the rationality theorem gives
      a finite candidate list.  The ample Cartier divisor $H$ is the one
      returned by {tt weightedAmpleDivisorData}.  Call this only after
      @TO canonicalNefData@ has shown that $K_X$ is not nef.  If a search
      bound is reached, @TT "threshold"@ is null and @TT "phase"@
      identifies the unfinished part of the search.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      thresholdData = canonicalNefThresholdData(X,1);
      {thresholdData#"threshold",thresholdData#"testsRun"}
  SeeAlso
    canonicalNefThreshold
    canonicalScaledNefData

Node
  Key
    canonicalNefThreshold
    (canonicalNefThreshold,Ring,ZZ)
  Headline
    return the canonical nef threshold
  Usage
    lambda = canonicalNefThreshold(R,a)
  Description
    Text
      Return only the rational number stored in the @TT "threshold"@ field
      of @TO canonicalNefThresholdData@.  Use the data-returning form when
      search diagnostics or certificates are needed.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      canonicalNefThreshold(X,1)
  SeeAlso
    canonicalNefThresholdData

Node
  Key
    canonicalNefData
    (canonicalNefData,Ring,ZZ)
  Headline
    decide whether the canonical divisor of a threefold is nef
  Usage
    result = canonicalNefData(R,a)
  Inputs
    R:Ring
      the homogeneous coordinate ring of a normal log terminal threefold
    a:ZZ
      a positive integer such that $aK_X$ is Cartier
  Outputs
    :HashTable
      @TT "nef"@, @TT "conclusive"@, and the base-point-free or non-nef
      witness supporting the answer
  Description
    Text
      The function alternates the two searches in Proposition 3.8.  It tests
      reflexive pluricanonical divisors for base-point-freeness and tests the
      positive perturbations $K_X+2^{-j}H$ by the effective multiplier of
      Proposition 3.1.  The hypotheses that $X$ is normal and log terminal are
      mathematical input requirements and are not certified by this function.
      When @TT "conclusive"@ is true, @TT "nef"@ is the Boolean answer and
      @TT "witnessType"@ explains its certificate.  A null @TT "nef"@
      means only that the optional search limit was reached.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      nefData = canonicalNefData(X,1);
      {nefData#"nef",nefData#"witnessType"}
  Caveat
    With no search limit the algorithm terminates under the stated threefold
    hypotheses by abundance.  Passing {	t NefSearchLimit} makes the computation
    practically bounded but may return an inconclusive table.

Node
  Key
    isCanonicalNef
    (isCanonicalNef,Ring,ZZ)
  Headline
    return the Boolean canonical-nefness answer
  Usage
    answer = isCanonicalNef(R,a)
  Description
    Text
      Convenience wrapper returning only the Boolean @TT "nef"@ value from
      @TO canonicalNefData@.  With a bounded search it raises an error instead
      of returning an inconclusive value; use @TO canonicalNefData@ to retain
      partial search information.
    Example
      Q = QQ[y0,y1,y2,y3,y4]/ideal(y0^5+y1^5+y2^5+y3^5+y4^5);
      isCanonicalNef(Q,1)
  SeeAlso
    canonicalNefData

Node
  Key
    canonicalScaledNefData
    (canonicalScaledNefData,Ring,ZZ,QQ)
    (canonicalScaledNefData,Ring,ZZ,ZZ)
  Headline
    decide whether K_X+tH is nef for positive rational t
  Usage
    result = canonicalScaledNefData(R,a,t)
  Description
    Text
      Test small positive multiples first.  A base-point-free multiple proves
      nefness; a negative intersection with a curve obtained from its base
      locus proves non-nefness.  If neither short certificate is found, use the
      effective base-point-free multiplier from Proposition 3.1.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      scaled = canonicalScaledNefData(X,1,3);
      {scaled#"nef",scaled#"certificateType"}
  SeeAlso
    effectiveNefMultiplier
    weightedAmpleDivisorData

Node
  Key
    negativeCurveWitnessData
    (negativeCurveWitnessData,BasicDivisor,Ideal,Ideal,List)
  Headline
    find a curve witnessing that a multigraded divisor is not nef
  Usage
    witness = negativeCurveWitnessData(D,candidateBaseLocus,B,h)
  Inputs
    D:BasicDivisor
      a divisor on a multigraded ring R
    candidateBaseLocus:Ideal
      an ideal of R containing D's base locus (before saturation)
    B:Ideal
      the irrelevant ideal of R
    h:List
      the multidegree of an ample class, one entry per grading component
  Outputs
    :HashTable
      a curve and its negative intersection number with D, or @TO null@ if
      no witness was found
  Description
    Text
      The multigraded generalization of the package's single-graded
      negative-curve shortcut: cut components of the saturated base locus
      down to a curve, then read off $D \cdot C$ from the eventual (constant)
      difference of @TO hilbertFunction@ values at multiples of $h$.  Returns
      @TO null@, never a wrong answer, when no witness stabilizes within
      @TT "NegativeCurveSearchLimit"@ attempts.

      This is a candidate cheaper alternative to
      @TO isBasePointFreeDivisor@'s own non-nefness test and is not yet used
      by any other function in this package; @TT "candidateBaseLocus"@ must
      be supplied by the caller (for instance from bookkeeping already done
      while searching for @TT "D"@), since WeilDivisors' own
      @TT "baseLocus"@ is not reliable for every divisor.

Node
  Key
    weightedAmpleDivisorData
    (weightedAmpleDivisorData,Ring)
  Headline
    construct the ample Cartier divisor from the coordinate weights
  Usage
    data = weightedAmpleDivisorData R
  Description
    Text
      Read the generator weights of $R$'s single grading and return the
      corresponding weighted-homogeneous ample divisor together with its
      Cartier degree.
    Example
      W = QQ[z0,z1,z2,z3,Degrees=>{1,1,1,2}];
      ample = weightedAmpleDivisorData W;
      {ample#"weights",ample#"cartierDegree"}

Node
  Key
    effectiveNefMultiplier
    (effectiveNefMultiplier,ZZ,ZZ)
  Headline
    compute the effective base-point-free multiplier
  Usage
    m = effectiveNefMultiplier(d,N)
  Description
    Text
      The effective multiplier of Proposition 3.1 for a $d$-dimensional
      variety and denominator $N$ of the tested rational multiple.
    Example
      effectiveNefMultiplier(3,1)
      effectiveNefMultiplier(3,2)

Node
  Key
    isBasePointFreeDivisor
    (isBasePointFreeDivisor,BasicDivisor)
  Headline
    test whether a complete divisor linear system is base-point-free
  Usage
    answer = isBasePointFreeDivisor D
  Description
    Text
      Return true precisely when the base locus of the complete linear system
      is empty on the projective variety.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      ample = weightedAmpleDivisorData X;
      isBasePointFreeDivisor ample#"divisor"

Node
  Key
    NefSearchLimit
  Headline
    optional iteration bound for the canonical-nefness search

Node
  Key
    MMPMaxSteps
  Headline
    optional iteration bound for the top-level MMP driver

Node
  Key
    CanonicalIndexSearchLimit
  Headline
    optional bound when searching for a canonical Cartier index

Node
  Key
    ContractionIsSmall
  Headline
    supply a smallness certificate when recording an MMP step

Node
  Key
    RelativeCanonicalMultipliers
  Headline
    optional explicit multiplier list for relative canonical models

Node
  Key
    RelativeCanonicalMaxMultiplier
  Headline
    largest Rees multiplier tried for relative canonical models
  Description
    Text
      Passed through to {\tt FlipComputation}'s {\tt MaxMultiplier}, which caps
      the consecutive search $m = 1, 2, 3, \dots$ of the paper's Algorithm 4.
      The default is 24.

Node
  Key
    RelativeCanonicalVerbose
  Headline
    display progress from the relative canonical model computation

Node
  Key
    ContractionMultipleLimit
  Headline
    optional bound on multiples tested when constructing a contraction

Node
  Key
    ThresholdSearchLimit
  Headline
    optional bound on scaled-nefness tests in the threshold search

Node
  Key
    DivisorClassDegrees
  Headline
    caller-supplied {degree(K),degree(H)}, bypassing recomputation
  Description
    Text
      Pass @TT "{degree(K),degree(H)}"@ to @TO canonicalScaledNefData@ (and
      its multigraded overload) when the caller already holds the canonical
      and ample divisor classes' degrees, to skip re-deriving them.  Default
      null preserves the previous behaviour exactly.

Node
  Key
    NegativeCurveSearchLimit
  Headline
    optional iteration bound for the multigraded negative-curve search
  Description
    Text
      Bounds the number of dimension-reducing cuts @TO negativeCurveWitnessData@
      tries before giving up and returning @TO null@.

Node
  Key
    IrrelevantIdeal
  Headline
    caller-supplied irrelevant ideal, bypassing multigradedBlockData
  Description
    Text
      On a multigraded ring with a "skew" fibre grading (as produced by
      FlipComputation's bigradedReesProjection whenever the ideal being
      blown up is not equigenerated), multigradedBlockData's own
      block-classification heuristic can return an irrelevant ideal with the
      wrong radical.  Every entry point below refuses to trust that guess by
      default in exactly this situation (it is not "verifiedBlockDiagonal";
      see multigradedBlockData) and errors instead of silently reporting a
      false Cartier or base-point-free positive built on it -- see
      tests/multigraded-skew-cartier.m2.  Passing
      {tt IrrelevantIdeal=>B} to canonicalScaledNefData,
      canonicalNefThresholdData, canonicalNefData,
      canonicalContractionAtThresholdData, or canonicalContractionData uses
      B verbatim for that entry point's own Cartier gate instead of
      re-deriving one, when a caller already holds a known-correct ideal
      (for instance a B2MProjection's or GraphMorphism's own irrelevantIdeal
      field).  Default null preserves the previous re-derivation exactly.

Node
  Key
    [canonicalNefThresholdData, ThresholdSearchLimit]
  Headline
    bound the nef-threshold search
  Usage
    canonicalNefThresholdData(R,a,ThresholdSearchLimit=>n)

Node
  Key
    [canonicalNefThreshold, ThresholdSearchLimit]
  Headline
    bound the scalar nef-threshold search
  Usage
    canonicalNefThreshold(R,a,ThresholdSearchLimit=>n)

Node
  Key
    [canonicalNefData, NefSearchLimit]
  Headline
    bound the alternating canonical-nefness search
  Usage
    canonicalNefData(R,a,NefSearchLimit=>n)
  Description
    Text
      Stop after at most n alternations.  If neither a globally generated
      pluricanonical divisor nor a non-nef positive perturbation has been found,
      the returned data has conclusive set to false.

Node
  Key
    [isCanonicalNef, NefSearchLimit]
  Headline
    bound the Boolean canonical-nefness search
  Usage
    isCanonicalNef(R,a,NefSearchLimit=>n)
  Description
    Text
      Stop after at most n alternations.  An error is raised if the bounded
      search is inconclusive.
///

endPackage "MMPComputation"
