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
protect mmpNoetherCanonicalDivisor;
protect mmpAffineBaseIrrelevantIdeal;
protect mmpAffineBaseRing;
protect mmpAffineExceptionalIdeal;
protect mmpAffineFibreCurves;
protect mmpAffineCurveDegrees;

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
    "VariableBlocks",
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
    -- A variable whose degree vector is entirely zero is not a badly
    -- classified block variable: it is a coordinate on the base.  Its
    -- coordinate lies in R_0, so R_0 is not k and X = Proj R is a projective
    -- scheme over the affine Spec R_0 rather than over a point.  The
    -- irrelevant ideal is then the product of the block ideals of the
    -- *positively graded* variables and nothing else -- a base variable
    -- generates no relevant ideal and is not excluded from Proj -- so such
    -- variables are assigned block 0 here and dropped before B is formed.
    -- Rejecting them, as this did before, made the whole relative setting
    -- unreachable; nothing changes when every variable carries a nonzero
    -- degree, where no variable is ever assigned block 0.
    baseIndices := select(n, j -> all(degree avars#j, c -> c == 0));
    tryOrder := perm -> (
        assignment := new MutableList from toList(n:null);
        ok := true;
        scan(n, j -> if ok then (
            if member(j,baseIndices) then assignment#j = 0
            else (
                dg := degree avars#j;
                reordered := apply(perm, i -> dg#i);
                lastNonzero := 0;
                scan(#reordered, k -> if reordered#k != 0 then lastNonzero = k+1);
                if reordered#(lastNonzero-1) <= 0 then
                    ok = false
                else assignment#j = lastNonzero;
                );
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
    -- Base variables are excluded from the block-diagonality check: they are
    -- unambiguous (they belong to no block at all), so they cannot be the
    -- source of the misclassification this flag guards against.
    nonBaseIndices := select(n, j -> not member(j,baseIndices));
    reorderedDegrees := apply(nonBaseIndices,
        j -> apply(usedPermutation, i -> (degree avars#j)#i));
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
        "baseVariables" => apply(baseIndices, j -> Rvars#j),
        "geometricDimension" => dim R - r,
        "verifiedBlockDiagonal" => verifiedBlockDiagonal,
        "blocksSupplied" => false
        }
    )

-- The variable blocks given, instead of guessed.  This is the datum the paper
-- carries and the code above throws away: Definition 2.5 writes the ambient as
-- k[y,x], so which variables are y's and which are x's is part of the
-- presentation, and S_dagger = <y_j x_i> S follows from it.  The revision made
-- recovering it from the degrees impossible in general -- Section 2.2 now sets
-- deg(y_j) = (d_j,0) but deg(x_i) = (a_i,c_i) with a "a further datum", so a
-- second-block variable may be nonzero in the first component and the
-- last-nonzero-entry heuristic above cannot tell it from a first-block one.
-- tests/multigraded-skew-cartier.m2's u_2, of degree (1,1), is exactly that.
--
-- Blocks are lists of variables (of R or of its ambient) and must partition
-- the variables exactly, one block per degree component.  Their order is not
-- used: the irrelevant ideal is the product of the block ideals, which is
-- symmetric, and the geometric dimension depends only on how many there are.
multigradedBlockData (Ring,List) := (R,blocks) -> (
    r := degreeLength R;
    if r <= 0 then
        error "multigradedBlockData: expected a graded ring";
    if not instance(blocks,List) or any(blocks,blk -> not instance(blk,List)) then
        error "multigradedBlockData: the blocks must be a list of lists of variables";
    if #blocks != r then
        error("multigradedBlockData: expected " | toString r
            | " blocks, one per degree component, but received "
            | toString(#blocks));
    if any(blocks,blk -> #blk == 0) then
        error "multigradedBlockData: every block must be nonempty";
    Rvars := flatten entries vars R;
    names := new HashTable from apply(Rvars, v -> toString v => v);
    inR := blk -> apply(blk, v -> (
        nm := toString v;
        if not names#?nm then
            error("multigradedBlockData: " | nm | " is not a variable of R");
        names#nm));
    blockVariables := apply(blocks,inR);
    flattened := flatten blockVariables;
    if #flattened != #Rvars then
        error("multigradedBlockData: the blocks name " | toString(#flattened)
            | " variables but R has " | toString(#Rvars)
            | "; they must partition the variables exactly");
    if #(set apply(flattened,toString)) != #Rvars then
        error "multigradedBlockData: the blocks overlap, or repeat a variable";
    blockIdeals := apply(blockVariables, vs -> ideal vs);
    new HashTable from {
        "ring" => R,
        "rank" => r,
        "permutation" => null,
        "blockAssignment" => null,
        "blockVariableIndices" => apply(blockVariables, vs ->
            apply(vs, v -> position(Rvars, w -> w == v))),
        "blockVariables" => blockVariables,
        "blockIdeals" => blockIdeals,
        "irrelevantIdeal" => product blockIdeals,
        "geometricDimension" => dim R - r,
        "verifiedBlockDiagonal" => null,
        "blocksSupplied" => true
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

-- The irrelevant ideal of a multigraded presentation is the product of its
-- variable blocks' ideals and nothing else: multigradedBlockData's own
-- B := product blockIdeals above, and FlipComputation's
-- bigradedIrrelevantIdeal(ys,xs) = ideal{y*x}, are the same formula.  The
-- datum that determines B is therefore the *partition* of the variables into
-- blocks, not an ideal in any one ring -- and misclassifying that partition
-- is the whole of the skew-grading defect.  Measured on
-- tests/multigraded-skew-cartier.m2's ring Z: the provenance and heuristic
-- partitions there differ in the placement of exactly one variable (u_2, of
-- skew degree {1,1}), each B is verifiably the product of its own
-- partition's block ideals, and only the radicals then differ.
--
-- B2MProjection and GraphMorphism already carry that partition, in
-- fiberVariables/baseVariables, and the B it determines in their
-- irrelevantIdeal field.  Accepting one of them as the value of
-- IrrelevantIdeal removes the step a caller previously had to perform by
-- hand, sub(P#irrelevantIdeal,R).  The stored field is read rather than the
-- two blocks re-multiplied, because a B2MProjection built with
-- BaseIsProjective=>false has an affine base, whose irrelevant ideal is the
-- fibre block alone (FlipComputation's affineIrrelevantIdeal) and not a
-- product of two; the field already accounts for that and re-deriving from
-- the partition would not.
--
-- The variable-name guard matters: substitute between two rings with the
-- same number of generators maps by position, so without it an unrelated
-- provenance object would silently produce a wrong ideal rather than fail.
normalizeIrrelevantIdealOption = (methodName,R,supplied) -> (
    if supplied === null then null
    else if instance(supplied,Ideal) then (
        if ring supplied =!= R then
            error(methodName | ": IrrelevantIdeal must be an ideal of R");
        supplied
        )
    else if instance(supplied,B2MProjection) or instance(supplied,GraphMorphism)
        then (
            suppliedAmbient := supplied#ambientRing;
            if apply(flatten entries vars ambient R,toString)
                != apply(flatten entries vars suppliedAmbient,toString) then
                error(methodName | ": the B2MProjection or GraphMorphism "
                    | "supplied as IrrelevantIdeal was not built for this "
                    | "ring -- its ambient variables differ, so its "
                    | "irrelevant ideal cannot be transferred.  Supply an "
                    | "Ideal of R instead.");
            sub(supplied#irrelevantIdeal,R)
            )
    else error(methodName | ": IrrelevantIdeal must be an Ideal, or a "
        | "B2MProjection or GraphMorphism carrying the ring's own irrelevant "
        | "ideal")
    )

-- One place where the irrelevant ideal and the geometric dimension are
-- decided.  Precedence: VariableBlocks, the datum the paper's presentation
-- carries, beats an ideal supplied directly, which beats the degree
-- heuristic; the heuristic is trusted only when it is verifiably block
-- diagonal, the one case in which no variable's degree can be misread.
-- Supplying both blocks and an ideal is a caller error rather than a silent
-- precedence rule.
irrelevantIdealDataInternal = (methodName,R,suppliedBlocks,suppliedIdeal) -> (
    if suppliedBlocks =!= null and suppliedIdeal =!= null then
        error(methodName | ": supply VariableBlocks or IrrelevantIdeal, not "
            | "both -- the blocks already determine the ideal");
    if suppliedBlocks =!= null then (
        bd := multigradedBlockData(R,suppliedBlocks);
        new HashTable from {
            "irrelevantIdeal" => bd#"irrelevantIdeal",
            "geometricDimension" => bd#"geometricDimension",
            "source" => "variable blocks",
            "blockData" => bd}
        )
    else (
        B := normalizeIrrelevantIdealOption(methodName,R,suppliedIdeal);
        if B =!= null then new HashTable from {
            "irrelevantIdeal" => B,
            "geometricDimension" => dim R - degreeLength R,
            "source" => "caller-supplied",
            "blockData" => null}
        else (
            guessed := multigradedBlockData R;
            if not guessed#"verifiedBlockDiagonal" then error(
                methodName | ": this ring has a skew (mixed-degree) "
                | "multigraded variable, so the block-classification "
                | "heuristic cannot reliably determine the irrelevant ideal "
                | "(see tests/multigraded-skew-cartier.m2).  Name the "
                | "variable blocks with VariableBlocks=>{{...},{...}}, or "
                | "supply the ideal itself with IrrelevantIdeal=>B.");
            new HashTable from {
                "irrelevantIdeal" => guessed#"irrelevantIdeal",
                "geometricDimension" => guessed#"geometricDimension",
                "source" => "derived",
                "blockData" => guessed}
            )
        )
    )

-- The result keys each multigraded entry point adds about its irrelevant
-- ideal.  The two pre-existing shapes are kept exactly: a derived ideal
-- reports only "blockData", a caller-supplied one only the ideal and its
-- source.  Named variable blocks report both, since both are available.
irrelevantIdealResultKeysInternal = idealData -> (
    src := idealData#"source";
    if src == "derived" then {"blockData" => idealData#"blockData"}
    else if src == "variable blocks" then {
        "irrelevantIdeal" => idealData#"irrelevantIdeal",
        "irrelevantIdealSource" => src,
        "blockData" => idealData#"blockData"}
    else {
        "irrelevantIdeal" => idealData#"irrelevantIdeal",
        "irrelevantIdealSource" => src}
    )

-- The irrelevant ideal of a presentation that has an affine base, or null.
--
-- "Has an affine base" is read syntactically, from the presence of a variable
-- whose degree vector is entirely zero -- the same reading multigradedBlockData
-- and affineBaseDimensionInternal use.  With no such variable R_0 = k, X lies
-- over a point, and this returns null so that every caller keeps the exact
-- classical behaviour without computing anything at all.
--
-- The ideal itself is multigradedBlockData's, which already excludes the base
-- variables from every block.  Failure to derive it is reported as null rather
-- than raised: the callers below all have a classical fallback, and turning a
-- ring this package can otherwise handle into an error would be a regression.
affineBaseIrrelevantIdealInternal = R -> (
    if R.cache#?mmpAffineBaseIrrelevantIdeal then
        return R.cache#mmpAffineBaseIrrelevantIdeal;
    S := ambient R;
    answer := null;
    if any(flatten entries vars S, q -> all(degree q, c -> c == 0)) then
        try answer = (multigradedBlockData R)#"irrelevantIdeal";
    R.cache#mmpAffineBaseIrrelevantIdeal = answer;
    answer
    )

-- Section 9.1 of references/AlgoMMP/RELATIVE-SETTING-AUDIT.md.  Classically
-- B = R_+ is the homogeneous maximal ideal, so ht(B) = dim R >= 2 and V(B)
-- carries no divisor: every height-one prime of R is a divisor on X = Proj R
-- and there is nothing to normalize.  Over an affine base
--
--     ht(B) = (generic fibre dimension of X -> Spec R_0) + 1,
--
-- so a generically finite -- that is, birational -- structure morphism gives
-- ht(B) = 1, and then a Weil divisor on Spec R may have prime components
-- supported inside V(B).  Those components are invisible on X, since V(B) is
-- exactly what Proj removes, but they still change the graded module
-- divisorToModule builds from the divisor, and with it every section count and
-- base-point-free verdict taken from that module.  Drop them.
--
-- In degree zero this is not an approximation but the exact answer.  When
-- ht(B) = 1 the map X -> Spec R_0 is birational, R_0 injects into R/B, and
-- K(X) = Frac(R_0), so every nonzero degree-zero element of Frac(R) is a ratio
-- of elements of R_0 and has order zero along a ghost prime P.  The condition
-- ord_P(f) + c_P >= 0 that the component imposes therefore reads c_P >= 0: it
-- is vacuous when c_P >= 0 and satisfied by nothing when c_P < 0.  Removing it
-- makes the degree-zero part of the module equal to H^0(X, O_X(D)) in both
-- cases, where leaving it in gives that group only when the sign happens to be
-- favourable.  Measured on Bl_0(A^3), where the code's own canonical divisor
-- carries the component -1*[B]: the degree-zero sections of K + 2H are 4 with
-- it and 1 without, and 1 is the right answer, K + 2H being trivial there.
--
-- Inert in the classical setting, and cheaply so.  A divisor's primes have
-- height one and cannot contain a B of height two or more, so the height test
-- alone settles it and no prime is ever examined.
dropIrrelevantComponentsInternal = (D,B) -> (
    if B === null or D === null then return D;
    if codim B > 1 then return D;
    ghosts := select(getPrimeCount D, i -> isSubset(B,(primes D)#i));
    if #ghosts == 0 then return D;
    P := primes D;
    C := coefficients D;
    D - divisor(apply(ghosts, i -> C#i), apply(ghosts, i -> P#i))
    )

-- Lemma 3.6 of the paper: if X is presented in a weighted projective space
-- with coordinate weights c_i and l=lcm(c_i), then O_X(l) is ample and
-- invertible.  A nonzero coordinate power of weighted degree l supplies an
-- effective Cartier representative H.
--
-- Weight zero is allowed, and means something specific: the paper's
-- Definition 2.1 has R_0 = k, but a variable of degree zero puts its
-- coordinate in R_0 instead, presenting X = Proj R as a projective scheme
-- over the affine base Spec R_0 rather than over a point.  The lemma still
-- holds there, over that base: l is the lcm of the *positive* weights, the
-- degree-zero variables contribute nothing to it, and O_X(l) is invertible
-- and f-ample by the same Veronese argument applied to the positively graded
-- part.  The Cartier representative must then be built from a coordinate of
-- positive weight -- a degree-zero coordinate is a unit in the relevant
-- sense and its divisor is not a fibre-direction divisor at all -- so the
-- candidate search is restricted accordingly.  Negative weights remain an
-- error: there Proj is not the object the paper's algorithms address.
--
-- This changes nothing for a caller whose weights are all positive, where
-- the lcm and the candidate list are exactly what they were.
weightedAmpleDivisorData = method()
weightedAmpleDivisorData Ring := R -> (
    S := ambient R;
    if degreeLength S != 1 then
        error "weightedAmpleDivisorData: expected a singly graded ring";
    ambientVars := flatten entries vars S;
    weights := apply(ambientVars,q -> (degree q)#0);
    if any(weights,c -> c < 0) then
        error "weightedAmpleDivisorData: coordinate weights must be nonnegative";
    positiveIndices := select(#ambientVars,i -> weights#i > 0);
    if #positiveIndices == 0 then
        error("weightedAmpleDivisorData: no coordinate has positive weight, "
            | "so Proj R is empty");
    ell := 1;
    scan(positiveIndices,i -> ell = lcm(ell,weights#i));
    candidates := select(positiveIndices,i -> sub(ambientVars#i,R) != 0);
    if #candidates == 0 then
        error "weightedAmpleDivisorData: every coordinate vanishes on X";
    coordinateIndex := first candidates;
    coordinate := sub(ambientVars#coordinateIndex,R);
    section := coordinate^(ell // weights#coordinateIndex);
    -- div(section) is a divisor of Spec R.  Over an affine base with an
    -- irrelevant ideal of height one it acquires a component supported inside
    -- V(B) -- on Bl_0(A^3) the code's own H is 1*[B] + 1*[(x,a)] -- which is
    -- not a divisor on X.  Drop it here so that every combination m*K + n*H a
    -- caller later forms is normalized too; inert when R_0 = k.
    H := dropIrrelevantComponentsInternal(
        divisor section,affineBaseIrrelevantIdealInternal R);
    new HashTable from {
        "ring" => R,
        "weights" => weights,
        "cartierDegree" => ell,
        "coordinateIndex" => coordinateIndex,
        "section" => section,
        "divisor" => H
        }
    )

-- The dimension of the affine base.  The paper's Definition 2.1 has R_0 = k,
-- so X = Proj R sits over a point and this is 0; a presentation with
-- degree-zero ambient variables puts their coordinates in R_0 instead and
-- X = Proj R is projective over the affine Spec R_0.
--
-- R_0 = S_0/(I cap S_0) where S_0 is the polynomial ring on the degree-zero
-- ambient variables, and for a homogeneous I in a ring with no negative
-- degrees the intersection is generated by I's own degree-zero generators:
-- writing an element of I cap S_0 as sum h_i g_i forces deg h_i = -deg g_i,
-- which is only available when deg g_i = 0.  So no elimination is needed.
--
-- With no degree-zero variables S_0 = k and this returns 0, which is what
-- every caller written for the R_0 = k case already assumes.
-- Written for any degree length, not only 1: a base variable is one whose
-- degree vector is entirely zero, the same reading multigradedBlockData uses
-- to keep such a variable out of every block.  The multigraded entry points
-- share canonicalContractionAtThresholdDataCore with the monograded ones, so
-- this has to answer for them too, and it answers 0, since a presentation
-- with no all-zero degree vector has R_0 = k.
-- The base ring R_0 itself, or null when R_0 = k.  This is the target of the
-- structure morphism X -> Spec R_0, so a relative contraction needs the ring
-- and not only its dimension.  Cached on R: the driver asks for it once per
-- entry point and the quotient is not free to form.
affineBaseRingInternal = R -> (
    if R.cache#?mmpAffineBaseRing then return R.cache#mmpAffineBaseRing;
    S := ambient R;
    baseVars := select(flatten entries vars S, q -> all(degree q, c -> c == 0));
    answer := null;
    if #baseVars > 0 then (
        kk := coefficientRing S;
        S0 := kk(monoid [baseVars]);
        degreeZeroGenerators := select(flatten entries gens ideal R,
            g -> g != 0 and all(degree g, c -> c == 0));
        answer = if #degreeZeroGenerators == 0 then S0
            else S0/sub(ideal degreeZeroGenerators,S0);
        );
    R.cache#mmpAffineBaseRing = answer;
    answer
    )

affineBaseDimensionInternal = R -> (
    R0 := affineBaseRingInternal R;
    if R0 === null then 0 else dim R0
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

-- The Noether-normalization route to the same canonical ideal, used when the
-- Ext/Hom route below is out of reach.  On the cyclic cover's flip target
-- Xminus (29 variables, codim 25) that route's Ext exceeds 8GB and M2's
-- Hom(omega,R) exceeds 9GB for every presentation size and coefficient
-- density tried; this one returns in about thirteen minutes.
--
-- For a homogeneous system of parameters theta_1..theta_d, A = k[theta] -> R
-- is finite and omega_R = Hom_A(R, omega_A) with no CM hypothesis needed.
-- When R is Cohen-Macaulay it is moreover free over A, with a basis lifting
-- any k-basis of the Artinian reduction R/(theta) -- far cheaper than
-- PushForward's pushFwd, which is itself what dies at this codimension.
-- dim_k R/(theta) = deg R certifies both that theta is a system of parameters
-- and that R is CM, so this returns null when it fails and the caller falls
-- back to the Ext route.
--
-- Everything after that stays over k.  Writing R = ⊕_i A e_i with deg e_i =
-- a_i, the multiplication matrices C_j of the variables come from one change
-- of basis per degree, since R_m = ⊕_i A_{m-a_i} e_i means the products
-- theta^alpha e_i are a second k-basis of R_m.  The R-action on omega is
-- their transpose, and then the same reduction applies three times:
--
--   * omega/m*omega = k^rank / sum_j colspace(C_j^T mod theta) gives omega's
--     minimal generators w_1..w_t over R (124 -> 5 on Xminus);
--   * ker(psi: R^t -> omega) is free over A -- psi surjects onto the free
--     A^rank, so the sequence splits -- so its A-generators are a basis, and
--     its R-minimal generators come from the same quotient one level up
--     (496 -> 96 on Xminus);
--   * a map phi: omega -> R of degree e is determined by phi(w_k) in
--     R_{deg w_k + e} subject to those relations, a linear system over k with
--     sum_k dim R_{deg w_k + e} unknowns (89 at e = 0 on Xminus).
--
-- omega is rank-one torsion-free, being the canonical module of a normal
-- domain, so any nonzero phi is injective and its image is a canonical ideal.
noetherCanonicalIdealSeedInternal = R -> (
    S := ambient R;
    if degreeLength S != 1 then return null;
    varList := flatten entries vars S;
    if #varList == 0 then return null;
    if any(varList, q -> (degree q)#0 != 1) then return null;
    kk := coefficientRing S;
    d := dim R;
    if d <= 0 then return null;
    targetDegree := degree R;

    -- A homogeneous system of parameters and the A-basis of R.  basis failing
    -- means the quotient is not Artinian, i.e. theta is not a system of
    -- parameters; a length other than deg R means R is not Cohen-Macaulay.
    thetas := apply(d, i -> random(1,R));
    Rbar := R/ideal thetas;
    basBarTry := try (first entries basis Rbar) else null;
    if basBarTry === null then return null;
    if #basBarTry != targetDegree then return null;
    es := apply(basBarTry, q -> sub(q,R));
    as := apply(basBarTry, q -> first degree q);
    rank0 := #es;

    basisCache := new MutableHashTable;
    degBasis := m -> (
        if not basisCache#?m then basisCache#m = basis(m,R);
        basisCache#m);
    Apoly := kk(monoid [Variables => d,
        VariableBaseName => getSymbol "mmpNoetherParameter"]);
    thetaMonos := e -> (if e < 0 then {} else first entries basis(e,Apoly));
    toR := q -> product apply(d, i -> thetas#i ^ ((exponents q)#0#i));
    coordsBatch := (fs,m) -> (
        if #fs == 0 then map(kk^0,kk^0,0)
        else lift(last coefficients(matrix{fs}, Monomials => degBasis m), kk));

    -- One change of basis per degree: theta^alpha e_i against the monomial
    -- basis of R_m.  Degrees only need to reach max(a_i) + 1.
    maxDeg := max as + 1;
    basisMatrix := new MutableHashTable;
    for m from 0 to maxDeg do (
        elts := {};
        for i from 0 to rank0-1 do
            for q in thetaMonos(m - as#i) do elts = append(elts,(toR q) * es#i);
        basisMatrix#m = coordsBatch(elts,m));

    -- Multiplication matrices, batched by degree: one coefficients call and
    -- one solve for each, with the A-coefficients kept in Apoly rather than
    -- in R (doing this elementwise, or in R, is what makes it intractable).
    vs := flatten entries vars R;
    cmat := new MutableHashTable;
    for m from 1 to maxDeg do (
        prods := {}; keysm := {};
        for j from 0 to (#vs)-1 do for i from 0 to rank0-1 do
            if as#i + 1 == m then (
                prods = append(prods, vs#j * es#i);
                keysm = append(keysm,{j,i}));
        if #prods > 0 then (
            V := solve(basisMatrix#m, coordsBatch(prods,m));
            nn := #keysm; rowsSoFar := 0; blocks := {};
            for l from 0 to rank0-1 do (
                ml := thetaMonos(m - as#l);
                if #ml == 0 then blocks = append(blocks, map(Apoly^1,Apoly^nn,0))
                else (
                    blocks = append(blocks, (matrix{ml}) *
                        sub(V^(toList(rowsSoFar..rowsSoFar+(#ml)-1)),Apoly));
                    rowsSoFar = rowsSoFar + #ml));
            M := fold(blocks,(a,b) -> a||b);
            for p from 0 to nn-1 do cmat#(keysm#p) = M_{p}));

    toK := map(kk,Apoly,toList(d:0_kk));
    Cmatrix := j -> fold(apply(rank0, i ->
        if cmat#?{j,i} then cmat#{j,i} else map(Apoly^rank0,Apoly^1,0)),
        (a,b) -> a|b);

    -- omega's minimal generators over R, by linear algebra over k.
    degF := apply(as, a -> d - a);
    Bfull := fold(apply(#vs, j -> toK transpose Cmatrix(j)),(a,b) -> a|b);
    genVecs := {};
    for g in sort unique degF do (
        rows := select(toList(0..rank0-1), l -> degF#l == g);
        mg := mingens coker (Bfull^rows);
        for c from 0 to (numcols mg)-1 do (
            v := new MutableList from toList(rank0 : 0_kk);
            for r from 0 to (#rows)-1 do v#(rows#r) = mg_(r,c);
            genVecs = append(genVecs,{g,toList v})));
    ng := #genVecs;
    if ng == 0 then return null;

    -- psi: R^ng -> omega as a map of free A-modules.  Each column e_i * w_k is
    -- at most max(a_i) matrix-vector products.
    Tcache := new MutableHashTable;
    Tmat := j -> (
        if not Tcache#?j then Tcache#j = transpose Cmatrix(j);
        Tcache#j);
    cols := {};
    for pr in genVecs do (
        w0 := sub(transpose matrix {pr#1}, Apoly);
        for i from 0 to rank0-1 do (
            v := w0;
            ev := (exponents basBarTry#i)#0;
            for j from 0 to (#vs)-1 do
                for c from 1 to ev#j do v = (Tmat j) * v;
            cols = append(cols,v)));
    psiMat := fold(cols,(a,b) -> a|b);
    srcDeg := flatten apply(genVecs, pr -> apply(as, a -> -(a + pr#0)));
    psiMap := map(Apoly^(apply(degF, g -> -g)), Apoly^srcDeg, psiMat);
    Ksyz := gens ker psiMap;
    kdegs := apply(degrees source Ksyz, dg -> first dg);
    nsyz := numcols Ksyz;

    -- The relations, minimized over R by the same argument one level up.
    relVecs := {};
    if nsyz > 0 then (
        K0 := toK Ksyz;
        zeroBlock := map(kk^rank0,kk^rank0,0);
        blockC := j -> (
            Cj := toK Cmatrix(j);
            matrix apply(ng, a -> apply(ng, b -> if a == b then Cj else zeroBlock)));
        B2 := fold(apply(#vs, j -> ((blockC j) * K0) // K0),(a,b) -> a|b);
        for g in sort unique kdegs do (
            rows := select(toList(0..nsyz-1), r -> kdegs#r == g);
            mg := mingens coker (B2^rows);
            for c from 0 to (numcols mg)-1 do (
                v := new MutableList from toList(nsyz : 0_kk);
                for r from 0 to (#rows)-1 do v#(rows#r) = mg_(r,c);
                relVecs = append(relVecs,{g,toList v}))));
    Kred := (if #relVecs == 0 then map(Apoly^(numrows Ksyz),Apoly^0,0)
        else Ksyz * sub(fold(apply(relVecs, pr -> transpose matrix {pr#1}),
            (a,b) -> a|b), Apoly));
    toRfromA := map(R,Apoly,thetas);
    relMat := (if numcols Kred == 0 then map(R^ng,R^0,0)
        else fold(apply(numcols Kred, c -> transpose matrix {
            apply(ng, k -> sum apply(rank0, i ->
                (toRfromA (Kred_(k*rank0+i,c))) * es#i))}),
            (a,b) -> a|b));

    -- phi: omega -> R of degree e, as a linear system over k.
    gdeg := apply(genVecs, pr -> pr#0);
    reldeg := apply(relVecs, pr -> pr#0);
    nrel := #relVecs;
    unknownCount := e -> sum apply(gdeg, g -> numcols degBasis (g+e));
    constraintsAt := e -> (
        if nrel == 0 then map(kk^0, kk^(unknownCount e), 0)
        else fold(apply(nrel, sidx -> (
            tgt := degBasis (reldeg#sidx + e);
            fold(apply(ng, k -> (
                src := degBasis (gdeg#k + e);
                if numcols src == 0 then map(kk^(numcols tgt),kk^0,0)
                else lift(last coefficients(relMat_(k,sidx) * src,
                    Monomials => tgt), kk))),(a,b) -> a|b))),(a,b) -> a||b));
    embDeg := null; phis := null;
    for e from -(max gdeg) to (max gdeg) + 4 do (
        if embDeg === null then (
            M := constraintsAt e;
            if numcols M > 0 then (
                Ksol := if numrows M == 0 then id_(kk^(numcols M)) else gens ker M;
                sizes := apply(gdeg, g -> numcols degBasis (g+e));
                for c from 0 to (numcols Ksol)-1 do (
                    if embDeg === null then (
                        o := 0;
                        cand := apply(ng, k -> (
                            src := degBasis (gdeg#k + e);
                            val := if sizes#k == 0 then 0_R
                                else (src * (Ksol^(toList(o..o+sizes#k-1)))_{c})_(0,0);
                            o = o + sizes#k;
                            val));
                        if any(cand, q -> q != 0) then (
                            embDeg = e; phis = cand))))));
    if embDeg === null then return null;
    canonicalIdeal := trim ideal select(phis, q -> q != 0);
    if canonicalIdeal == ideal 0_R then return null;
    new HashTable from {
        "ring" => R,
        "ideal" => canonicalIdeal,
        "embeddingDegree" => {embDeg},
        "certificate" =>
            "canonical module via Noether normalization, embedding solved over the base field"
        }
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
-- Past this codimension the Ext below is not worth attempting: it resolves R
-- over S to homological degree dim S - dim R, and on Xminus (29 variables,
-- codim 25) that exceeds 8GB, where the Noether route returns in about
-- thirteen minutes.  Every ring the existing tests exercise has codimension at
-- most six, so nothing already working changes route.
mmpNoetherCodimThreshold = 12;

-- The seed is an embedding of the canonical *module* of the graded ring R,
-- omega_R = Ext^c(R,omega_S), which is O_{Spec R}(K) for the divisor
-- canonicalDivisor returns -- ghost component and all.  Over an affine base
-- with an irrelevant ideal of height one that divisor and the divisor on X
-- differ by a multiple of a prime supported inside V(B), so the seed's degree
-- bookkeeping answers about the wrong module and its fastpaths give wrong
-- verdicts, not merely conservative ones.  Measured on the toric flip's target
-- Z: omega_R embeds as (u_7,u_6,u_3) at degree -1, so its degree-zero part is
-- empty and canonicalIdealSeedBPFInternal reports K_Z not base-point-free,
-- where H^0(Z,O(K_Z)) in fact has two generators over R_0 and K_Z is
-- base-point-free.  Refuse the seed there and let every caller fall back to
-- the divisorToModule path, which normalizes the divisor first.
canonicalIdealSeedDataInternal = (R,K) -> (
    if instance(K,WeilDivisor) and K#cache#?mmpCanonicalIdealSeedData then
        return K#cache#mmpCanonicalIdealSeedData;
    affineB := affineBaseIrrelevantIdealInternal R;
    if affineB =!= null and codim affineB <= 1 then return null;
    S := ambient R;
    -- Only in the regime where the Ext is hopeless, and only as an attempt:
    -- the Noether route returns null on any ring it cannot handle (multigraded,
    -- non-standard weights, theta not a system of parameters, R not
    -- Cohen-Macaulay), so the Ext route below remains the default.
    if dim S - dim R >= mmpNoetherCodimThreshold then (
        noetherSeed := noetherCanonicalIdealSeedInternal R;
        if noetherSeed =!= null then (
            if instance(K,WeilDivisor) then
                K#cache#mmpCanonicalIdealSeedData = noetherSeed;
            return noetherSeed;
            );
        );
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

-- canonicalDivisor(R,IsGraded=>true) stops with
--
--     error: no method for binary operator - applied to objects:
--         -infinity (of class InfiniteNumber) - {0} (of class List)
--
-- on some perfectly ordinary rings.  WeilDivisors' internalModuleToIdeal
-- embeds omega as an ideal by walking the columns of
-- syz transpose presentation omega -- each one a homogeneous map omega -> R --
-- until it finds an injective one, and then reads the degree of the embedding
-- as
--
--     degree(t#0) - (degrees omega)#0
--
-- (WeilDivisors.m2:1808).  That is the right difference only when the section's
-- *first* component is nonzero.  The map is homogeneous, so every index j with
-- t#j != 0 gives the same difference and any one of them will do -- but when
-- t#0 = 0 the degree of the zero element is -infinity and the subtraction has
-- no meaning.  It is not an exotic situation: on the toric threefold
-- S3 x A^1 over A^3 of tests/three-step-relative-mmp.m2, omega has four
-- generators and all three candidate sections start with a zero,
--
--     {0, u_5, -u_6, -u_7},  {0, -u_3, u_2*u_5, u_4*u_5},
--     {0, u_2^3, -u_2*u_4, -u_4^2},
--
-- so the very first candidate crashes it.
--
-- This is the same construction with the shift read off the first nonzero
-- component instead, and is used only where WeilDivisors' own function fails,
-- so nothing that works today changes answer.  The rest of the function body
-- is WeilDivisors' canonicalDivisor and divisor(Module,IsGraded=>true) in
-- sequence, with their Ext and their findElementOfDegree.  Checked against
-- canonicalDivisor on the rings where that one does return: identical divisor,
-- not merely a linearly equivalent one.
gradedCanonicalDivisorRetryInternal = R -> (
    S := ambient R;
    ambientVariables := flatten entries vars S;
    if #ambientVariables == 0 then return null;
    degreeList := if #(degree first ambientVariables) == 1
        then apply(ambientVariables, q -> (degree q)#0)
        else apply(ambientVariables, q -> degree q);
    omega := (Ext^(dim S - dim R)(
        S^1/(ideal R), S^{-(sum degreeList)})) ** R;
    if omega == 0 then return null;
    omegaDegrees := degrees omega;
    section := null;
    shift := null;
    scan(entries transpose syz transpose presentation omega,
        candidate -> if section === null then (
            j := position(candidate, entry -> entry != 0);
            if j =!= null and isInjective map(R^1,omega,{candidate}) then (
                section = candidate;
                shift = degree(candidate#j) - omegaDegrees#j;
                );
            ));
    if section === null then return null;
    correction := findElementOfDegree((-1)*shift,R);
    -divisor(trim ideal section) - divisor(correction#0)
        + divisor(correction#1)
    )

-- WeilDivisors' graded canonical divisor, with the retry above standing in
-- where it stops on the degree bug the retry documents.
mmpGradedCanonicalDivisorInternal = R -> (
    answer := try canonicalDivisor(R,IsGraded=>true) else null;
    if answer =!= null then return answer;
    answer = gradedCanonicalDivisorRetryInternal R;
    if answer === null then
        error("mmpCanonicalDivisorInternal: WeilDivisors' canonicalDivisor "
            | "failed on this ring and the graded embedding retry found no "
            | "homogeneous section of the canonical module");
    answer
    )

-- canonicalDivisor(R,IsGraded=>true) is WeilDivisors' own function, and it runs
-- the same Ext over the ambient that the seed above exists to avoid.  So on a
-- ring where that Ext is out of reach the seed never gets its chance, because
-- every caller needs K first.  This closes that gap: past the same threshold,
-- K is assembled from the Noether seed instead of from the Ext.
--
-- The seed gives phi: omega -> R of degree e with image I, so omega = I(e) as
-- graded modules and hence, as sheaves, O_X(K) = Ĩ(e) = O_X(-div I + e*H).
-- H is the class of O(1), which for a standard graded ring is div(f) for any
-- nonzero linear form -- and the Noether route accepts nothing else, so f is
-- always available here.  The seed is cached on the divisor produced, so the
-- caller's later canonicalIdealSeedDataInternal(R,K) reuses it instead of
-- recomputing the whole construction.
--
-- Verified against canonicalDivisor on P^3, the 2-uple Veronese of P^3 and the
-- quintic threefold: linearly equivalent in each case, which is all that is
-- ever asked of K -- Cartier-ness, base-point-freeness and the index are
-- properties of the class.
-- Cached on the ring, not only on the divisor: every entry point recomputes K
-- from scratch, and threefoldMMPData goes through several of them, so without
-- this the Noether construction would be paid again at each step -- about
-- thirteen minutes apiece on the cyclic cover's flip target.  Any divisor with
-- O_X(K) = omega will do, so reusing one across calls is sound.
-- Over an affine base whose irrelevant ideal has height one the divisor
-- canonicalDivisor returns is a divisor of Spec R and may carry a component
-- supported inside V(B), which is not on X (section 9.1 of
-- references/AlgoMMP/RELATIVE-SETTING-AUDIT.md).  Normalize once here, at the
-- source, rather than at each of the many places K is later combined with H:
-- dropping ghost components is additive, so a normalized K and a normalized H
-- make every m*K + n*H the caller forms normalized too.
--
-- The Noether branch is skipped in that case, not normalized after the fact.
-- It caches a canonical-ideal seed on the divisor it returns, and that seed is
-- built from the unnormalized ideal, so it would have to be discarded anyway;
-- and the branch cannot fire over an affine base regardless, since
-- noetherCanonicalIdealSeedInternal requires every ambient variable to have
-- degree one and a base variable has degree zero.
mmpCanonicalDivisorInternal = R -> (
    if R.cache#?mmpNoetherCanonicalDivisor then
        return R.cache#mmpNoetherCanonicalDivisor;
    affineB := affineBaseIrrelevantIdealInternal R;
    if affineB =!= null then
        return dropIrrelevantComponentsInternal(
            mmpGradedCanonicalDivisorInternal R,affineB);
    S := ambient R;
    if dim S - dim R >= mmpNoetherCodimThreshold then (
        seed := noetherCanonicalIdealSeedInternal R;
        if seed =!= null then (
            linearForms := select(flatten entries vars R, q -> q != 0_R);
            if #linearForms > 0 then (
                f := first linearForms;
                canonicalIdeal := seed#"ideal";
                shiftDegree := first (seed#"embeddingDegree");
                base := (if canonicalIdeal == ideal 1_R then 0*divisor(f)
                    else -divisor(canonicalIdeal));
                K := base + shiftDegree*divisor(f);
                K#cache#mmpCanonicalIdealSeedData = seed;
                R.cache#mmpNoetherCanonicalDivisor = K;
                return K;
                );
            );
        );
    mmpGradedCanonicalDivisorInternal R
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
isBasePointFreeDivisorInternal = (D0,B) -> (
    -- Components supported inside V(B) change the graded module without
    -- changing the sheaf on X; drop them first.  Inert unless ht(B) = 1, so
    -- every classical caller reaches the identical code below with D = D0.
    D := dropIrrelevantComponentsInternal(D0,B);
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
    -- Components supported inside V(B) are not on X and must not be allowed
    -- to decide where O_X(D) is invertible; inert unless ht(B) = 1.
    WD := dropIrrelevantComponentsInternal(D,B);
    WD = if instance(WD,WeilDivisor) then WD else toWeilDivisor WD;
    if not isHomogeneous WD then
        error "isCartierSaturatedInternal: expected a homogeneous divisor";
    -- IsGraded=>true would first saturate the locus by getIrrelevantIdeal(R),
    -- the homogeneous maximal ideal.  Classically that is harmless -- it is
    -- absorbed by the saturation against B below, since B is generated by
    -- variables and so B is contained in m, whence
    -- saturate(saturate(J,m),B) = saturate(J,B) exactly.  Over an affine base
    -- it is not harmless but wrong: m contains the base coordinates, so
    -- saturating by it discards the point of X lying over the origin of
    -- Spec R_0, which is precisely where a relative contraction's singularity
    -- sits.  Measured on the toric flip's source Y, whose canonical index is 2:
    -- with the m-saturation K_Y is reported Cartier and the index comes back 1.
    -- Doing the saturation only against B gives the identical answer for every
    -- classical caller and the right one here.
    J := nonCartierLocus WD;
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

-- The Cartier test the monograded entry points want.  isCartier(D,IsGraded=>
-- true) is hard-wired, inside nonCartierLocus's own IsGraded branch, to
-- WeilDivisors' getIrrelevantIdeal(R), the homogeneous maximal ideal.  Over an
-- affine base that ideal contains the base coordinates and so is not the
-- irrelevant ideal of X at all: it excludes points of X that are genuinely
-- there.  Fall through to the historical call verbatim whenever there is no
-- affine base, which is every classical caller.
mmpIsCartierInternal = D -> (
    B := affineBaseIrrelevantIdealInternal ring D;
    if B === null then isCartier(D,IsGraded=>true)
    else isCartierSaturatedInternal(D,B)
    )

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

-- The exceptional locus of the structure morphism X = Proj R -> Spec R_0, or
-- null when the presentation has no affine base or the morphism is not
-- generically finite.
--
-- Omega_{Spec R / R_0} is the cokernel of the Jacobian of I taken only with
-- respect to the positively graded variables; the degree-zero variables are the
-- coordinates of R_0 and are exactly the ones held fixed.  Its generic rank is
-- the relative dimension dim R - dim R_0, which is 1 for a birational structure
-- morphism: the cone direction and nothing else.  Where that rank jumps, the
-- morphism is not etale, and for a birational morphism of normal varieties in
-- characteristic zero that locus -- once V(B), which Proj removes, is saturated
-- away -- is the exceptional locus.
--
-- Cached on R: both the smallness test and the negative-curve shortcut want it,
-- and the driver runs each of them more than once per ring.
affineExceptionalIdealInternal = R -> (
    if R.cache#?mmpAffineExceptionalIdeal then
        return R.cache#mmpAffineExceptionalIdeal;
    answer := null;
    R0 := affineBaseRingInternal R;
    if R0 =!= null and dim R - dim R0 == 1 then (
        S := ambient R;
        svars := flatten entries vars S;
        fibreIndices := select(#svars, j -> not all(degree svars#j, c -> c == 0));
        if #fibreIndices > 0 then (
            B := ideal apply(fibreIndices, j -> sub(svars#j,R));
            relativeJacobian := sub(submatrix(jacobian ideal R,fibreIndices,),R);
            -- No prune and no module rank here: over an affine base there is no
            -- heft vector -- a degree-zero variable cannot be given positive
            -- weight -- so prune, rank and hilbertFunction all fail on such a
            -- module (section 10 of the relative-setting audit).  The rank is
            -- dim R - dim R_0 by the paragraph above and needs neither.
            answer = saturate(
                ann exteriorPower(2,coker relativeJacobian),B);
            );
        );
    R.cache#mmpAffineExceptionalIdeal = answer;
    answer
    )

-- Complete curves in the fibres of X = Proj R -> Spec R_0.
--
-- Over an affine base every curve of X that is proper over k lies in a fibre of
-- the structure morphism (section 9(1) of the relative-setting audit), and when
-- that morphism is birational the positive-dimensional fibres are exactly its
-- exceptional locus.  So the search range for a negative curve is the
-- exceptional locus and nothing else -- strictly narrower than in the absolute
-- setting, where it is the whole of X.
--
-- Components of dimension greater than one are cut by deterministic coordinate
-- hyperplanes until curves remain, the same way negativeBaseLocusCurveData
-- narrows a base locus, and a cut that collapses the piece to the unit ideal is
-- skipped rather than committed to.
affineFibreCurvesInternal = R -> (
    if R.cache#?mmpAffineFibreCurves then return R.cache#mmpAffineFibreCurves;
    curves := {};
    E := affineExceptionalIdealInternal R;
    if E =!= null and E != ideal 1_R then (
        S := ambient R;
        svars := flatten entries vars S;
        fibreIndices := select(#svars, j -> not all(degree svars#j, c -> c == 0));
        B := ideal apply(fibreIndices, j -> sub(svars#j,R));
        coordinates := flatten entries vars R;
        pieces := minimalPrimes E;
        depth := 0;
        while #pieces > 0 and depth <= numgens R do (
            curves = join(curves,select(pieces,Q -> dim(R/Q) == 2));
            nextPieces := {};
            scan(select(pieces,Q -> dim(R/Q) > 2),Q -> (
                candidates := select(coordinates,x -> x % Q != 0);
                cutIdeal := null;
                scan(candidates,x -> if cutIdeal === null then (
                    candidate := trim saturate(Q+ideal x,B);
                    if candidate != ideal 1_R then cutIdeal = candidate;
                    ));
                if cutIdeal =!= null then
                    nextPieces = join(nextPieces,minimalPrimes cutIdeal);
                ));
            pieces = unique nextPieces;
            depth = depth+1;
            );
        );
    curves = unique curves;
    R.cache#mmpAffineFibreCurves = curves;
    curves
    )

-- The degree of a Cartier divisor on one such curve, or null if it cannot be
-- read off.
--
-- The curve C is proper over k, so its own homogeneous coordinate ring R/Q has
-- a finite-dimensional degree-zero part and a heft vector, even though R does
-- not: contracted by a birational structure morphism means C maps to a point of
-- Spec R_0, so R_0 meets Q in a maximal ideal.  Computing on R/Q rather than on
-- R is what restores the Hilbert functions that section 10 of the audit
-- observes are unavailable over an affine base.
--
-- For a Cartier divisor the difference of Hilbert polynomials
-- HP(O(D)|_C) - HP(O_C) is the constant deg(D|_C), by Riemann-Roch on C; the
-- loop twists by O(n*h) until that difference stabilizes, exactly as
-- negativeBaseLocusCurveData does in the absolute setting.  h is the Cartier
-- degree of the presentation, so O(h) is invertible.
relativeCurveDegreeInternal = (D,Q,h,limit) -> (
    R := ring D;
    RC := R/Q;
    DModule := null;
    if (try (DModule = weilDivisorToModule D; true) else false) =!= true then
        return null;
    restriction := DModule ** RC;
    -- hilbertFunction is not available here, and not for the reason section 10
    -- of the audit gives about R: Macaulay2's R/Q keeps every variable of R,
    -- degree-zero ones included, so R/Q has no heft vector either even when the
    -- curve makes those variables zero.  Counting the degree-n strand with
    -- basis avoids heft entirely, and on the curve it returns what is wanted: a
    -- curve contracted to a point of Spec R_0 has R_0 mapping onto the residue
    -- field there, so the degree-zero subring of R/Q is that field and basis
    -- returns an honest basis over it rather than a generating set over R_0.
    -- A field extension would scale both counts by its degree and so cannot
    -- change the sign, which is all this certificate reads.
    answer := null;
    try (
        n := 1;
        current := numColumns basis({n*h},restriction)
            - numColumns basis({n*h},RC^1);
        stabilized := false;
        while not stabilized and n < limit do (
            previous := current;
            n = n+1;
            current = numColumns basis({n*h},restriction)
                - numColumns basis({n*h},RC^1);
            if current == previous then stabilized = true;
            );
        if stabilized then answer = current;
        ) else answer = null;
    answer
    )

-- Degrees of a*K and of H on every fibre curve, computed once per (R,a,H).
--
-- This is what makes the threshold search affordable over an affine base.  A
-- candidate t = p/q is tested on the divisor L = q*a*K + a*p*H, whose
-- coefficients grow with q, and the base-point-free test's cost is dominated by
-- constructing O(L); measured on the toric flip's source, that is half a second
-- at q = 2 and more than fifteen minutes at q = 8.  But
--
--     L.C = q*(a*K).C + a*p*(H.C)
--
-- is linear in (p,q), so the two degrees below are all that is ever needed, and
-- every candidate is then decided by one multiplication.  A negative value is
-- an unconditional non-nef certificate; a nonnegative one says nothing and the
-- effective base-point-free test must still run.
affineCurveDegreeDataInternal = (R,K,H,a) -> (
    key := (a,H);
    cache := if R.cache#?mmpAffineCurveDegrees then R.cache#mmpAffineCurveDegrees
        else (R.cache#mmpAffineCurveDegrees = new MutableHashTable);
    if cache#?key then return cache#key;
    answer := {};
    curves := affineFibreCurvesInternal R;
    if #curves > 0 then (
        weights := apply(flatten entries vars ambient R,q -> (degree q)#0);
        positiveWeights := select(weights,c -> c > 0);
        h := 1;
        scan(positiveWeights,c -> h = lcm(h,c));
        limit := 24;
        answer = select(apply(curves,Q -> (
            kDegree := relativeCurveDegreeInternal(a*K,Q,h,limit);
            hDegree := relativeCurveDegreeInternal(H,Q,h,limit);
            if kDegree === null or hDegree === null then null
            else new HashTable from {
                "curveIdeal" => Q,
                "canonicalDegree" => kDegree,
                "ampleDegree" => hDegree}
            )),entry -> entry =!= null);
        );
    cache#key = answer;
    answer
    )

-- A fibre curve on which q*a*K + a*p*H has negative degree, or null.
affineNegativeCurveShortcutInternal = (R,K,H,a,p,q) -> (
    if affineBaseIrrelevantIdealInternal R === null then return null;
    data := affineCurveDegreeDataInternal(R,K,H,a);
    witness := null;
    scan(data,entry -> if witness === null then (
        value := q*(entry#"canonicalDegree") + a*p*(entry#"ampleDegree");
        if value < 0 then witness = new HashTable from {
            "curveIdeal" => entry#"curveIdeal",
            "intersection" => value,
            "canonicalDegree" => entry#"canonicalDegree",
            "ampleDegree" => entry#"ampleDegree",
            "certificate" => "negative degree on a complete curve in a fibre "
                | "of X -> Spec R_0"};
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
    -- Over an affine base, try the complete curves in the fibres first.  Their
    -- intersection numbers with a*K and with H are computed once per ring and
    -- combine linearly, so this decides a candidate t in arithmetic where the
    -- base-point-free test below would have to construct O(m*L) with
    -- coefficients proportional to q.  It is a one-sided certificate: a
    -- negative value proves non-nefness outright, and anything else falls
    -- through to exactly the search that was here before.  Returns null at once
    -- on any presentation with R_0 = k, which is every classical caller.
    affineCurveWitness := affineNegativeCurveShortcutInternal(R,K,H,a,p,q);
    if affineCurveWitness =!= null then
        return new HashTable from {
            "nef" => false,
            "t" => t,
            "dimension" => d,
            "indexMultiple" => a,
            "N" => N,
            "multiplier" => null,
            "guaranteedMultiplier" => guaranteedMultiplier,
            "multipliersTested" => {},
            "certificateType" => "negative curve intersection",
            "negativeCurveWitness" => affineCurveWitness,
            "cartierDivisor" => L,
            "testDivisor" => null,
            "basePointFree" => false
            };
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
    IrrelevantIdeal => null, VariableBlocks => null,
    DivisorClassDegrees => null})
canonicalScaledNefData (Ring,ZZ,QQ) := o -> (R,a,t) -> (
    if a <= 0 then
        error "canonicalScaledNefData: the index multiple must be positive";
    K := mmpCanonicalDivisorInternal R;
    if not mmpIsCartierInternal(a*K) then
        error "canonicalScaledNefData: a*K_X is not Cartier";
    H := (weightedAmpleDivisorData R)#"divisor";
    classDegrees := normalizeDivisorClassDegrees(
        R,o.DivisorClassDegrees,"canonicalScaledNefData");
    canonicalScaledNefDataInternal(R,K,H,a,t,null,classDegrees)
    )
canonicalScaledNefData (Ring,ZZ,ZZ) := o -> (R,a,t) ->
    canonicalScaledNefData(R,a,t/1,
        IrrelevantIdeal=>o.IrrelevantIdeal,
        VariableBlocks=>o.VariableBlocks,
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
    K := mmpCanonicalDivisorInternal R;
    B := (irrelevantIdealDataInternal(
        "canonicalScaledNefData",R,o.VariableBlocks,o.IrrelevantIdeal))#"irrelevantIdeal";
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalScaledNefData: a*K_X is not Cartier";
    classDegrees := normalizeDivisorClassDegrees(
        R,o.DivisorClassDegrees,"canonicalScaledNefData");
    canonicalScaledNefDataInternal(R,K,H,a,t,B,classDegrees)
    )
canonicalScaledNefData (Ring,ZZ,ZZ,BasicDivisor) := o -> (R,a,t,H) ->
    canonicalScaledNefData(R,a,t/1,H,
        IrrelevantIdeal=>o.IrrelevantIdeal,
        VariableBlocks=>o.VariableBlocks,
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
    ThresholdSearchLimit => null, IrrelevantIdeal => null,
    VariableBlocks => null})
canonicalNefThresholdData (Ring,ZZ) := o -> (R,a) -> (
    if a <= 0 then
        error "canonicalNefThresholdData: the index multiple must be positive";
    limit := o.ThresholdSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalNefThresholdData: ThresholdSearchLimit must be null or positive";
    K := mmpCanonicalDivisorInternal R;
    if not mmpIsCartierInternal(a*K) then
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
    K := mmpCanonicalDivisorInternal R;
    idealData := irrelevantIdealDataInternal(
        "canonicalNefThresholdData",R,o.VariableBlocks,o.IrrelevantIdeal);
    B := idealData#"irrelevantIdeal";
    d := idealData#"geometricDimension";
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalNefThresholdData: a*K_X is not Cartier";
    result := canonicalNefThresholdDataCore(R,a,K,H,d,limit,B);
    extraKeys := irrelevantIdealResultKeysInternal idealData;
    new HashTable from join(pairs result,join({
        "ampleData" => new HashTable from {"ring" => R,"divisor" => H}},
        extraKeys))
    )

canonicalNefThreshold = method(Options => options canonicalNefThresholdData)
canonicalNefThreshold (Ring,ZZ) := o -> (R,a) -> (
    -- These two wrappers cover the paper's algorithm as stated, which is for a
    -- monograded variety: Section 3 opens with "Let X = Proj R be a normal
    -- monograded variety", and a bigraded input reaches it through Section
    -- 2.3's w-diagonal, a monograded ring.  The multigraded entry points in
    -- this package are an extension of that, added because the w-diagonal
    -- blows the presentation up in practice, and they live on the data-
    -- returning methods only.  So the two options belong to those and not
    -- here.  They arrive declared regardless, since the option list is
    -- inherited with "options canonicalNefThresholdData", and were previously
    -- dropped in silence -- which sent a multigraded ring into the monograded
    -- dimension test and produced "expected a projective threefold" about a
    -- ring that is a threefold.  Refuse them instead and name where to go.
    if o.IrrelevantIdeal =!= null or o.VariableBlocks =!= null then
        error("canonicalNefThreshold: IrrelevantIdeal and VariableBlocks do not "
            | "apply here.  This wrapper is the paper's monograded algorithm, "
            | "where one variable block leaves the irrelevant ideal with no "
            | "choice to make.  For a multigraded presentation use "
            | "canonicalNefThresholdData(R,a,H), which takes both.");
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
completeLinearSystemGraphData BasicDivisor := D0 -> (
    -- The sections this builds the morphism from are the degree-zero part of
    -- O(D), so the divisor has to be the one on X: a component supported
    -- inside V(B) would change that section space.  Inert unless the
    -- presentation has an affine base whose irrelevant ideal has height one.
    D := dropIrrelevantComponentsInternal(
        D0,affineBaseIrrelevantIdealInternal ring D0);
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
completeLinearSystemGraphDataMultigraded = method(Options => {
    IrrelevantIdeal => null, VariableBlocks => null})
completeLinearSystemGraphDataMultigraded (BasicDivisor,BasicDivisor) := o -> (D,w) -> (
    R := ring D;
    suppliedB := if o.VariableBlocks =!= null then (
        if o.IrrelevantIdeal =!= null then
            error("completeLinearSystemGraphDataMultigraded: supply "
                | "VariableBlocks or IrrelevantIdeal, not both -- the blocks "
                | "already determine the ideal");
        (multigradedBlockData(R,o.VariableBlocks))#"irrelevantIdeal"
        ) else normalizeIrrelevantIdealOption(
            "completeLinearSystemGraphDataMultigraded",R,o.IrrelevantIdeal);
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
    -- Over an affine base the target of the contraction is not what this
    -- construction computes.  Phi_{|MD|} is built as a morphism to P^{n-1}
    -- with n the number of degree-zero sections, and that is the *absolute*
    -- morphism: it forgets Spec R_0 entirely.  The relative contraction is
    -- the one over the base, a Proj over Spec R_0, which the graph-morphism
    -- representation here cannot express.
    --
    -- The single-section case is the exception, and it is exactly the case
    -- that used to be reported wrongly.  n = 1 classically means the only
    -- sections are the constants, so Phi maps to a point; over an affine base
    -- it means the sections are generated by one element over R_0, so the
    -- morphism is the structure morphism X -> Spec R_0.  The target is the
    -- base, of dimension dim R_0, not a point.  Measured on P^2 x A^1 at its
    -- threshold lambda = 3, where K + 3H is trivial: this returned
    -- targetDimension 0 and "trivial point target", conclusively, where the
    -- contraction is the projection to A^1 and the target has dimension 1.
    -- affineBaseDimensionInternal returns 0 when R_0 = k, so the classical
    -- reading is unchanged.
    baseDimension := affineBaseDimensionInternal R;
    -- More than one degree-zero generator over an affine base: the target is
    -- neither the base nor a point but an intermediate variety, Proj over
    -- Spec R_0 of the R_0-algebra the section representatives generate.  That
    -- is built here rather than left to the graph representation, which cannot
    -- express it.
    --
    -- Stein factorization is not run on it; it is certified unnecessary in the
    -- one case that is accepted.  When the image has the same dimension as X
    -- the morphism is birational, and if the image is normal then Zariski's
    -- main theorem makes Phi_* O_X = O of the image, so the fibres are already
    -- connected and Phi is its own Stein factorization.  A fibre-type image, or
    -- an image that is not normal, needs the A-module version of the section
    -- ring lemma and is refused instead of guessed at.
    if linearSystemGraph#"targetVariableCount" != 1 and baseDimension > 0 then (
        sections := linearSystemGraph#"sectionImages";
        relativeTarget := affineRelativeTargetRingInternal(R,sections);
        refuse := reason -> new HashTable from {
            "conclusive" => false,
            "threshold" => lambda,
            "N" => N,
            "cartierThresholdDivisor" => cartierThresholdDivisor,
            "guaranteedMultiplier" => guaranteedMultiplier,
            "multiplier" => multiplier,
            "morphismDivisor" => morphismDivisor,
            "linearSystemGraph" => linearSystemGraph,
            "canonicalDivisor" => K,
            "affineBaseDimension" => baseDimension,
            "relativeTargetRing" => relativeTarget,
            "phase" => "contraction target over an affine base",
            "warning" => reason};
        if relativeTarget === null then
            return refuse("R_0 is not a field and the linear system has more "
                | "than one degree-zero generator, so the contraction's target "
                | "is an intermediate variety over Spec R_0; its coordinate "
                | "algebra could not be built from the section "
                | "representatives.");
        relativeTargetDimension := dim relativeTarget - 1;
        if relativeTargetDimension != d then
            return refuse("the contraction over the affine base is of fibre "
                | "type, its image having dimension "
                | toString relativeTargetDimension | " where the source has "
                | toString d | ".  Certifying that the fibres are connected "
                | "then needs the A-module version of the section ring lemma "
                | "(section 6 of the relative-setting audit), which is not "
                | "implemented, so the Stein factorization is refused rather "
                | "than assumed trivial.");
        if not affineTargetBirationalInternal(R,sections) then
            return refuse("the contraction over the affine base is generically "
                | "finite onto its image, but this could not be certified "
                | "birational.  Without that certificate the image need not be "
                | "the contraction -- the morphism could be generically finite "
                | "of higher degree -- and skipping the Stein factorization "
                | "would be a guess.  The A-module version of the section ring "
                | "lemma (section 6 of the relative-setting audit) is what "
                | "would settle the general case.");
        if not isNormal relativeTarget then
            return refuse("the contraction over the affine base is birational "
                | "onto its image but that image is not normal, so Zariski's "
                | "main theorem does not certify that the fibres are connected "
                | "and the Stein factorization cannot be skipped; the target "
                | "would be the normalization of the image.");
        return new HashTable from join({
            "conclusive" => true,
            "threshold" => lambda,
            "N" => N,
            "cartierThresholdDivisor" => cartierThresholdDivisor,
            "multiplier" => multiplier,
            "guaranteedMultiplier" => guaranteedMultiplier,
            "morphismDivisor" => morphismDivisor,
            "linearSystemGraph" => linearSystemGraph,
            "canonicalDivisor" => K,
            "affineBaseDimension" => baseDimension,
            "sourceRing" => R,
            "relativeTargetRing" => relativeTarget,
            "relativeTargetSections" => sections,
            "steinFactorizationType" => "trivial: birational onto a normal "
                | "image over the affine base",
            "steinAlgebraData" => new HashTable from {
                "ring" => relativeTarget,
                "baseIsProjective" => true,
                "certificate" => "Proj over Spec R_0 of the R_0-algebra "
                    | "generated by the sections; birational onto it by an "
                    | "explicit ratio of sections for each coordinate, and "
                    | "normal, so Zariski's main theorem makes Phi its own "
                    | "Stein factorization"}
            },pairs contractionTypeData(d,relativeTargetDimension));
        );
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
            "steinFactorizationType" => if baseDimension == 0
                then "trivial point target"
                else "structure morphism to the affine base",
            "affineBaseDimension" => baseDimension,
            "contractionGraph" => linearSystemGraph#"graph",
            "canonicalDivisor" => K
            },
            -- Over an affine base the morphism this branch has identified is
            -- X -> Spec R_0, and the pieces downstream of a contraction need
            -- that target as a ring: the relative canonical model is computed
            -- from it (with an affine base, so Proj_{Spec R_0} rather than the
            -- projective Proj_X of Algorithm 4's usual reading), and the
            -- smallness test needs the source, since the graph recorded above
            -- is the absolute morphism to P^0 and contracts everything.  These
            -- keys are absent when R_0 = k, where the branch means what it
            -- always meant, a trivial point target.
            if baseDimension == 0 then {} else {
                "contractionIsStructureMorphism" => true,
                "sourceRing" => R,
                "affineBaseRing" => affineBaseRingInternal R,
                "steinAlgebraData" => new HashTable from {
                    "ring" => affineBaseRingInternal R,
                    "baseIsProjective" => false,
                    "certificate" => "the degree-zero subring R_0, reached as "
                        | "the target of the structure morphism"}
                },
            pairs contractionTypeData(d,baseDimension));
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
    Options => {ContractionMultipleLimit => null, IrrelevantIdeal => null,
        VariableBlocks => null})
canonicalContractionAtThresholdData (Ring,ZZ,QQ) := o -> (R,a,lambda) -> (
    if a <= 0 then
        error "canonicalContractionAtThresholdData: the index multiple must be positive";
    if lambda <= 0 then
        error "canonicalContractionAtThresholdData: the threshold must be positive";
    limit := o.ContractionMultipleLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalContractionAtThresholdData: ContractionMultipleLimit must be null or positive";
    K := mmpCanonicalDivisorInternal R;
    if not mmpIsCartierInternal(a*K) then
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
    K := mmpCanonicalDivisorInternal R;
    idealData := irrelevantIdealDataInternal(
        "canonicalContractionAtThresholdData",R,o.VariableBlocks,
        o.IrrelevantIdeal);
    B := idealData#"irrelevantIdeal";
    d := idealData#"geometricDimension";
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalContractionAtThresholdData: a*K_X is not Cartier";
    result := canonicalContractionAtThresholdDataCore(R,a,lambda,K,H,d,limit,
        morphismDivisor -> completeLinearSystemGraphDataMultigraded(
            morphismDivisor,H,IrrelevantIdeal=>B),B);
    extraKeys := irrelevantIdealResultKeysInternal idealData;
    new HashTable from join(pairs result,join({
        "ampleData" => new HashTable from {"ring" => R,"divisor" => H}},
        extraKeys))
    )
canonicalContractionAtThresholdData (Ring,ZZ,ZZ,BasicDivisor) := o -> (R,a,lambda,H) ->
    canonicalContractionAtThresholdData(R,a,lambda/1,H,
        ContractionMultipleLimit=>o.ContractionMultipleLimit,
        IrrelevantIdeal=>o.IrrelevantIdeal,
        VariableBlocks=>o.VariableBlocks)

canonicalContractionData = method(Options => {
    ThresholdSearchLimit => null,
    ContractionMultipleLimit => null,
    IrrelevantIdeal => null,
    VariableBlocks => null})
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
    -- Normalized once here rather than left to the two calls below, so that a
    -- B2MProjection or GraphMorphism passed as IrrelevantIdeal is resolved to
    -- an ideal of R a single time instead of once per callee.
    -- Resolved once here rather than left to the two calls below, so that
    -- VariableBlocks or a provenance object is turned into an ideal of R a
    -- single time instead of once per callee.
    B := (irrelevantIdealDataInternal(
        "canonicalContractionData",R,o.VariableBlocks,
        o.IrrelevantIdeal))#"irrelevantIdeal";
    thresholdData := canonicalNefThresholdData(
        R,a,H,ThresholdSearchLimit=>o.ThresholdSearchLimit,
        IrrelevantIdeal=>B);
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
        IrrelevantIdeal=>B);
    new HashTable from join(pairs result,{"thresholdData" => thresholdData})
    )

-- The relative canonical model over an affine base, as a monograded ring the
-- driver can carry to the next step.
--
-- FlipComputation's bigradedReesProjection builds the Rees algebra over an
-- affine base as k[u_1..u_r, x_1..x_n]/I_Z and, in its own words, "leaves the
-- grading by the u-degree implicit and computes with the standard grading" --
-- every variable of degree one.  That presentation is not the one this package
-- reads: here Z is Proj of a ring whose degree-zero part is the base, so the u
-- variables carry degree one and the x variables degree zero.  Re-grade rather
-- than rebuild: I_Z is already homogeneous for the u-degree, being a Rees
-- ideal, and the check below is what makes that a verified fact and not an
-- assumption.
--
-- This is exactly the shape of presentation the driver started from, so a flip
-- computed over an affine base can be fed straight back into the nefness test
-- for the next step.
-- The target of a contraction over an affine base whose image is not the base.
--
-- Phi_{|MD|} is built by the linear system as a morphism to P^{n-1}, and over
-- an affine base that is the *absolute* morphism: it forgets Spec R_0.  The
-- relative morphism is the one to P^{n-1} x Spec R_0, and its image is Proj of
-- the R_0-subalgebra of R generated by the section representatives.  That
-- subalgebra is again a graded ring whose degree-zero part is R_0, so the
-- target comes out in the same shape the driver reads and the next step can
-- start from it.
--
-- The section representatives share a degree e, so the kernel of
-- R_0[Y] --> R, Y_i |--> s_i is homogeneous when Y_i is given degree e; every
-- monomial of a relation then has the same Y-degree, so the same generators are
-- homogeneous for degree one as well, and it is that grading the result
-- carries.  Multiplying every representative by a common factor does not change
-- the kernel (R is a domain), so the artificial common factor a rational
-- trivialization can introduce is harmless here.
affineRelativeTargetRingInternal = (R,sections) -> (
    if #sections == 0 then return null;
    degrees0 := unique apply(sections, f -> (degree f)#0);
    if #degrees0 != 1 then return null;
    e := first degrees0;
    if e <= 0 then return null;
    S := ambient R;
    svars := flatten entries vars S;
    baseIndices := select(#svars, j -> all(degree svars#j, c -> c == 0));
    if #baseIndices == 0 then return null;
    baseNames := apply(baseIndices, j -> svars#j);
    kk := coefficientRing S;
    fibre := getSymbol "mmpRelativeTargetVariable";
    -- The base coordinates go first, ahead of the section variables.  Nothing
    -- downstream reads a variable by position -- the fibre and base blocks are
    -- always selected by degree -- but the order is the tie-break of the
    -- monomial order, and over an affine base that tie-break decides
    -- everything: the degree-zero variables make whole strata of monomials
    -- equal in degree, so the graded reverse lexicographic order falls through
    -- to position on all of them.
    --
    -- Measured on the second model of tests/three-step-relative-mmp.m2, the
    -- same ring presented both ways: canonicalNefThreshold takes 0.68 seconds
    -- with the base coordinates first and 203.5 seconds with the section
    -- variables first, a factor of three hundred on one identical question.
    -- The three-step program as a whole goes from about 230 seconds to about
    -- eight.  The presentation the driver hands to its own next iteration was
    -- the slow one, while every presentation written by hand in this
    -- repository's tests and examples is the fast one, which is why the cost
    -- only showed up once a step had to start from a ring an earlier step had
    -- built.
    coarse := kk(monoid [baseNames, fibre_1 .. fibre_(#sections),
        Degrees => join(toList(#baseIndices : {0}),toList(#sections : {e}))]);
    phi := map(R,coarse,
        join(apply(baseIndices, j -> sub(svars#j,R)),sections));
    relations := ker phi;
    fine := kk(monoid [baseNames, fibre_1 .. fibre_(#sections),
        Degrees => join(toList(#baseIndices : {0}),toList(#sections : {1}))]);
    J := sub(relations,fine);
    if not isHomogeneous J then return null;
    fine/J
    )

-- Is Phi birational onto its image?  A definite true is a certificate; false
-- means only that this test did not find one.
--
-- The test needs R generated in degree one over R_0, which it checks.  Then
-- K(X) = Frac(R)_0 is generated over Frac(R_0) by the ratios u/u_1 of the
-- degree-one variables, and Frac(R_0) is inside Frac(T)_0 because R_0 = T_0.
-- So Phi is birational onto its image exactly when every such ratio lies in
-- Frac(T)_0, and one witness for that is a pair A, B in T_1 with B nonzero and
-- u_1 A = u B, which gives u/u_1 = A/B.  T_1 is the R_0-span of the section
-- representatives, so the pairs are the coefficients of a syzygy of one row
-- vector, in the single degree where those coefficients have degree zero.
--
-- Birationality is what lets the Stein factorization be skipped: with it, and
-- the image normal, Zariski's main theorem gives Phi_* O_X = O of the image.
-- Without it the morphism could be generically finite of higher degree onto a
-- perfectly normal image, and then the image is not the contraction.
-- A ratio may need A and B of degree higher than one -- the strand T_1 is only
-- the R_0-span of the representatives themselves -- so the search climbs
-- through the products of m of them until it succeeds or runs out of tries.
affineTargetBirationalInternal = method(Options => {NefSearchLimit => 3})
affineTargetBirationalInternal (Ring,List) := o -> (R,sections) -> (
    if #sections == 0 then return false;
    fibreVars := select(flatten entries vars R, q -> (degree q)#0 > 0);
    if #fibreVars == 0 then return false;
    if any(fibreVars, q -> (degree q)#0 != 1) then return false;
    if any(flatten entries vars R, q -> (degree q)#0 < 0) then return false;
    u1 := first fibreVars;
    e := (degree first sections)#0;
    strand := m -> (
        current := {1_R};
        scan(m, i -> current = unique flatten apply(current,
            f -> apply(sections, g -> f*g)));
        select(current, f -> f != 0));
    ratioFound := u -> (
        answer := false;
        scan(1..o.NefSearchLimit, m -> if not answer then (
            products := strand m;
            k := #products;
            if k > 0 then (
                row := matrix{join(apply(products, f -> u1*f),
                    apply(products, f -> -u*f))};
                syzygies := ker row;
                -- basis of a submodule returns coordinates in that module's own
                -- generators, so super is needed to read the actual vectors of
                -- coefficients in the ambient free module.
                witnesses := super basis({m*e+1},syzygies);
                if any(numColumns witnesses, c ->
                    any(k, i -> witnesses_(k+i,c) != 0)) then answer = true;
                );
            ));
        answer);
    all(fibreVars, u -> u == u1 or ratioFound u)
    )

-- Spec W, presented the way this package reads a variety: as Proj of a graded
-- ring whose degree-zero part is W.  W[t] with deg t = 1 is that ring, and its
-- Proj is Spec W.
--
-- This is what a divisorial step over an affine base has to hand back.  Its
-- target is the affine base itself, and the driver's next iteration asks for
-- the nefness of the canonical divisor of a Proj, so an affine ring is not
-- something it can continue from -- dim W - 1 is 2, not 3, and the threefold
-- gate rejects it.  Every generator of W is given degree zero, so W's ideal is
-- homogeneous for the new grading whatever it was for the old one.
affineTargetPresentationInternal = W -> (
    A := ambient W;
    kk := coefficientRing A;
    fibre := getSymbol "mmpAffineFibreVariable";
    graded := kk(monoid [gens A, fibre,
        Degrees => join(toList(numgens A : {0}),{{1}})]);
    J := sub(ideal W,graded);
    graded/J
    )

affineRelativeModelRingInternal = P -> (
    A := P#ambientRing;
    us := P#fiberVariables;
    xs := P#baseVariables;
    kk := coefficientRing A;
    degreeList := join(toList(#us : {1}),toList(#xs : {0}));
    graded := kk(monoid [gens A, Degrees => degreeList]);
    J := sub(P#definingIdeal,graded);
    if not isHomogeneous J then
        error("relativeCanonicalModelFromBaseData: the Rees ideal of the "
            | "relative canonical model is not homogeneous for the fibre "
            | "degree, so the model has no presentation over the affine base");
    graded/J
    )

-- Algorithm 4, applied to the base W of a birational contraction.  If the
-- canonical module already embeds as the unit ideal, its relative canonical
-- Proj is W itself; otherwise FlipComputation constructs the model as a graph.
--
-- BaseIsProjective=>false is the relative setting: W is then the affine base
-- Spec R_0 of a contraction X -> Spec R_0, so W itself is the threefold rather
-- than a cone over one, the model is Proj over Spec W instead of over Proj W,
-- and there is no irrelevant ideal to saturate against when asking whether the
-- canonical blow-up ideal is already invertible.  Default true, which is every
-- existing caller, and on that path not one line below changes.
relativeCanonicalModelFromBaseData = method(Options => {
    RelativeCanonicalMultipliers => null,
    RelativeCanonicalMaxMultiplier => 24,
    RelativeCanonicalVerbose => false,
    BaseIsProjective => true})
relativeCanonicalModelFromBaseData Ring := o -> W -> (
    projectiveBase := o.BaseIsProjective;
    coneCorrection := if projectiveBase then 1 else 0;
    if dim W-coneCorrection != 3 then
        error(if projectiveBase
            then "relativeCanonicalModelFromBaseData: expected a projective threefold"
            else "relativeCanonicalModelFromBaseData: expected an affine threefold");
    -- The relative model of an affine base is Spec W, and the driver's next
    -- iteration reads a Proj, so hand it W[t] rather than W.  On a projective
    -- base W already is the presentation, and this is the identical object it
    -- always was.
    identityRing := if projectiveBase then W else affineTargetPresentationInternal W;
    -- A Q-Gorenstein base is its own relative canonical model, which is what
    -- the identity branch means.  If K_W is Q-Cartier of index r then
    -- omega^{[r]} is invertible, so the r-th Veronese of the canonical algebra
    -- is the Rees algebra of a line bundle and its Proj is W; Proj is
    -- insensitive to passing to a Veronese, so the model is W.
    --
    -- Only a positive is taken: a search that runs out of multiples says
    -- nothing.  The check is made only when the presentation has an affine
    -- base, so no classical caller pays for it or changes route -- and there
    -- it is not an optimization but the only way through, since a target that
    -- is Proj over Spec R_0 has variables of bidegree zero in FlipComputation's
    -- Rees construction and no heft vector exists for that ring.
    if affineBaseIrrelevantIdealInternal W =!= null then (
        indexData := canonicalIndexData(W,CanonicalIndexSearchLimit=>12);
        if indexData#"conclusive" then
            return new HashTable from {
                "conclusive" => true,
                "baseRing" => W,
                "relativeModelRing" => identityRing,
                "relativeModelGraph" => null,
                "relativeModelProjection" => null,
                "relativeModelType" => "identity",
                "isIdentity" => true,
                "baseIsProjective" => projectiveBase,
                "canonicalIndex" => indexData#"index",
                "identityCertificate" => "K_W is Q-Cartier of index "
                    | toString(indexData#"index")
                    | ", so W is its own relative canonical model",
                "sourceDimension" => dim W-coneCorrection,
                "targetDimension" => dim W-coneCorrection
                };
        );
    if canonicalIdeal W == ideal 1_W then
        return new HashTable from {
            "conclusive" => true,
            "baseRing" => W,
            "relativeModelRing" => identityRing,
            "relativeModelGraph" => null,
            "relativeModelProjection" => null,
            "relativeModelType" => "identity",
            "isIdentity" => true,
            "baseIsProjective" => projectiveBase,
            "identityCertificate" => "canonical module embeds as the unit ideal",
            "sourceDimension" => dim W-coneCorrection,
            "targetDimension" => dim W-coneCorrection
            };
    -- computeRelativeCanonicalModel raises an error when no multiplier it
    -- tried produced a small projection with an S_2 source.  Exhausting the
    -- schedule means "not settled at these multipliers", not "no relative
    -- canonical model exists", so report it the structured way the threshold
    -- and canonical-index searches above use instead of letting a raw error
    -- escape through threefoldMMPData.
    --
    -- Accepting only the identity or a small projection is not a restriction
    -- to work around: it is what the paper proves.  Proposition 6.8's
    -- termination argument shows that for a sufficiently divisible m the
    -- candidate IS Proj of the relative canonical algebra, so "such an m
    -- passes both tests", and Corollary 6.10's proof then uses "the morphism
    -- g is small" as an established fact, not a hypothesis to be checked.
    -- The identity is the Q-Gorenstein case, where the target is its own
    -- relative canonical model.  There is no third, divisorial case to
    -- implement -- the paper has no such notion.  Hitting this branch
    -- therefore means the bound was too low for the m that works, and raising
    -- RelativeCanonicalMaxMultiplier is the right response.
    modelProjection := try computeRelativeCanonicalModel(W,
        Multipliers=>o.RelativeCanonicalMultipliers,
        MaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
        ReturnGraph=>false,
        BaseIsProjective=>projectiveBase,
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
            "warning" => "no multiplier tried gave a small projection with "
                | "an S_2 source; raise RelativeCanonicalMaxMultiplier.  "
                | "Proposition 6.8 of the paper proves that a sufficiently "
                | "divisible multiplier passes both tests, so this is a bound "
                | "being too low and not a model that cannot be reached"
            };
    baseCanonicalIdeal := restrictToBase(
        modelProjection,modelProjection#blownUpIdeal);
    nonFreeLocus := fittingIdeal(1,module baseCanonicalIdeal);
    -- On a projective base the vertex of the cone is not a point of W, so the
    -- non-free locus is saturated against the irrelevant ideal first.  On an
    -- affine base W is Spec of this ring and every point of it counts, so
    -- there is nothing to saturate away.
    modelIsIdentity := if projectiveBase then (
        irrelevant := ideal flatten entries vars W;
        saturate(nonFreeLocus,irrelevant) == ideal 1_W
        ) else nonFreeLocus == ideal 1_W;
    if modelIsIdentity then
        return new HashTable from {
            "conclusive" => true,
            "baseRing" => W,
            "relativeModelRing" => identityRing,
            "relativeModelGraph" => null,
            "relativeModelProjection" => modelProjection,
            "canonicalBlowupIdeal" => baseCanonicalIdeal,
            "nonInvertibleLocus" => nonFreeLocus,
            "relativeModelType" => "identity",
            "isIdentity" => true,
            "baseIsProjective" => projectiveBase,
            "identityCertificate" => if projectiveBase
                then "the canonical blow-up ideal is locally free of rank one on Proj"
                else "the canonical blow-up ideal is locally free of rank one on Spec",
            "sourceDimension" => dim W-coneCorrection,
            "targetDimension" => dim W-coneCorrection
            };
    -- b2mToGraphMorphism refuses an affine base outright, and rightly: its
    -- output is a graph of monograded varieties inside W x X, and over an
    -- affine base there is no second cone direction to build one from.  What
    -- the driver needs there is not a graph but the model's own presentation,
    -- which the Rees projection already is once it is graded by the fibre
    -- degree.
    modelGraph := if projectiveBase then b2mToGraphMorphism(
        modelProjection,Verbose=>o.RelativeCanonicalVerbose) else null;
    modelRing := if projectiveBase then modelGraph#sourceRing
        else affineRelativeModelRingInternal modelProjection;
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
        "baseIsProjective" => projectiveBase,
        "identityCertificate" => if projectiveBase
            then "the canonical blow-up ideal is not locally free on Proj"
            else "the canonical blow-up ideal is not locally free on Spec",
        "sourceDimension" => dim(modelRing)-1,
        "targetDimension" => dim(W)-coneCorrection
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
    steinData := contraction#"steinAlgebraData";
    -- A contraction that is the structure morphism to an affine base records
    -- its target as Spec of that ring, not Proj of it; everything downstream
    -- has to be told which, since it changes both the dimension bookkeeping and
    -- the Rees construction.  Absent key means projective, as it was.
    projectiveBase := if steinData#?"baseIsProjective"
        then steinData#"baseIsProjective" else o.BaseIsProjective;
    result := relativeCanonicalModelFromBaseData(
        steinData#"ring",
        RelativeCanonicalMultipliers=>o.RelativeCanonicalMultipliers,
        RelativeCanonicalMaxMultiplier=>o.RelativeCanonicalMaxMultiplier,
        RelativeCanonicalVerbose=>o.RelativeCanonicalVerbose,
        BaseIsProjective=>projectiveBase);
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
        error("relativeModelInverseRationalMapData: expected a bi-to-mono "
            | "projection and graph data");
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

-- Smallness of the structure morphism f : X = Proj R -> Spec R_0.
--
-- Over an affine base the contraction at the threshold is often f itself (the
-- one-generator case of canonicalContractionAtThresholdDataCore), and then
-- there is no graph to feed the test above: the graph the linear system builds
-- is the absolute morphism to P^0, which contracts everything and says nothing
-- about f.  The criterion is the same one, applied to Spec R over Spec R_0
-- instead of to a bigraded graph over its target.
--
--   Omega_{Spec R / R_0} = coker of the Jacobian of I taken with respect to the
--   positively graded variables only -- the degree-zero variables are exactly
--   the coordinates of R_0 and are the ones held fixed.
--
-- Its generic rank is the relative dimension dim R - dim R_0, which is 1 for a
-- birational f: the single cone direction, the same "generic relative cone
-- dimension one" the graph version asserts.  Where the rank jumps, f is not
-- etale, and for a birational morphism of normal varieties in characteristic
-- zero that locus, once the removed V(B) is saturated away, is the exceptional
-- locus.  Its codimension in X decides smallness.
--
-- The rank is not computed from the module.  Over an affine base no heft vector
-- exists -- a degree-zero variable cannot be given positive weight -- so
-- Macaulay2's rank, prune and hilbertFunction all fail on such a module (see
-- section 10 of references/AlgoMMP/RELATIVE-SETTING-AUDIT.md).  dim R - dim R_0
-- is the same number and needs neither.
affineContractionSmallnessInternal = R -> (
    R0 := affineBaseRingInternal R;
    if R0 === null then
        error("affineContractionSmallnessData: expected a presentation with an "
            | "affine base, i.e. with a variable of degree zero");
    S := ambient R;
    svars := flatten entries vars S;
    fibreIndices := select(#svars, j -> not all(degree svars#j, c -> c == 0));
    if #fibreIndices == 0 then
        error "affineContractionSmallnessData: no variable of positive degree";
    sourceDimension := dim R - 1;
    if dim R - dim R0 != 1 then
        error("affineContractionSmallnessData: expected generic relative cone "
            | "dimension one, i.e. a generically finite structure morphism; "
            | "this presentation has relative dimension "
            | toString(dim R - dim R0 - 1));
    exceptionalIdeal := affineExceptionalIdealInternal R;
    if exceptionalIdeal === null then
        error("affineContractionSmallnessData: could not build the relative "
            | "differentials of Spec R over Spec R_0");
    empty := exceptionalIdeal == ideal 1_R;
    exceptionalDimension := if empty then -1 else dim(R/exceptionalIdeal)-1;
    exceptionalCodimension := if empty then sourceDimension+1
        else sourceDimension-exceptionalDimension;
    new HashTable from {
        "isSmall" => exceptionalCodimension >= 2,
        "sourceDimension" => sourceDimension,
        "targetDimension" => dim R0,
        "exceptionalDimension" => exceptionalDimension,
        "exceptionalCodimension" => exceptionalCodimension,
        "exceptionalLocusEmpty" => empty,
        "exceptionalIdeal" => exceptionalIdeal,
        "fibreCurves" => affineFibreCurvesInternal R,
        "criterion" => "codimension of support of exterior^2 of the relative "
            | "differentials of Spec R over Spec R_0",
        "assumptions" => "integral separable birational structure morphism "
            | "X = Proj R -> Spec R_0 with X normal"
        }
    )

-- Smallness of a birational morphism to an intermediate target over an affine
-- base, given by the section representatives that define it.
--
-- Omega_{X/T} is the cokernel of f^*Omega_{T/R_0} --> Omega_{X/R_0}, and for a
-- birational morphism of normal varieties in characteristic zero its support is
-- the exceptional locus: f is an isomorphism away from Exc, where Omega
-- vanishes, and is not one on Exc, where it does not.  On the cone this is the
-- cokernel of the Jacobian of I taken with respect to the positively graded
-- variables, extended by the columns of partial derivatives of the section
-- representatives, since those generate T over R_0.
--
-- The cone map Spec R --> Spec T' is not itself birational.  T' contains the
-- representatives, of degree e, so Frac(R) is degree e over Frac(T') and the
-- map is a mu_e quotient in the cone direction.  That costs nothing: the fixed
-- locus of mu_e is the zero section V(R_+), which lies inside V(B) and is
-- saturated away below, so what is left is the exceptional locus of f and
-- nothing else.  It is also why no exterior power appears here where the
-- graph version needs one: the extension is algebraic, so Omega_{R/T'} is
-- generically zero and its annihilator already cuts out the support.
affineTargetSmallnessInternal = (R,sections,sourceDimension) -> (
    S := ambient R;
    svars := flatten entries vars S;
    fibreIndices := select(#svars, j -> not all(degree svars#j, c -> c == 0));
    if #fibreIndices == 0 then
        error "affineTargetSmallnessData: no variable of positive degree";
    B := ideal apply(fibreIndices, j -> sub(svars#j,R));
    lifted := apply(sections, f -> lift(f,S));
    relativeJacobian := sub(submatrix(
        jacobian ideal R | jacobian matrix{lifted},fibreIndices,),R);
    exceptionalIdeal := saturate(ann coker relativeJacobian,B);
    empty := exceptionalIdeal == ideal 1_R;
    exceptionalDimension := if empty then -1 else dim(R/exceptionalIdeal)-1;
    exceptionalCodimension := if empty then sourceDimension+1
        else sourceDimension-exceptionalDimension;
    new HashTable from {
        "isSmall" => exceptionalCodimension >= 2,
        "sourceDimension" => sourceDimension,
        "exceptionalDimension" => exceptionalDimension,
        "exceptionalCodimension" => exceptionalCodimension,
        "exceptionalLocusEmpty" => empty,
        "exceptionalIdeal" => exceptionalIdeal,
        "criterion" => "codimension of the support of the relative "
            | "differentials of X over the image of the linear system",
        "assumptions" => "integral separable birational morphism of normal "
            | "varieties over Spec R_0"
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
    -- Over an affine base the contraction can be the structure morphism, which
    -- has no graph of its own; the source ring is then what the test needs.
    if contraction#?"contractionIsStructureMorphism"
        and contraction#"contractionIsStructureMorphism" then (
            if not contraction#?"sourceRing" then
                error "contractionSmallnessData: missing source ring";
            return affineContractionSmallnessInternal contraction#"sourceRing";
            );
    -- And it can be a morphism to an intermediate target over that base, which
    -- has no graph either: what determines it is the section representatives.
    if contraction#?"relativeTargetSections" then (
        if not contraction#?"sourceRing" then
            error "contractionSmallnessData: missing source ring";
        return affineTargetSmallnessInternal(
            contraction#"sourceRing",contraction#"relativeTargetSections",
            contraction#"sourceDimension");
        );
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
    -- Over an affine base the contraction is the structure morphism
    -- X -> Spec R_0, which is not a graph morphism of monograded varieties and
    -- is not recorded as one; the ring pair that determines it is already in
    -- the contraction.  Every other contraction still has to carry its graph.
    structureMorphism := contraction#?"contractionIsStructureMorphism"
        and contraction#"contractionIsStructureMorphism";
    -- A contraction to an intermediate target over an affine base has no graph
    -- either: what determines it is the section representatives, and the target
    -- ring is on the contraction.
    relativeTarget := contraction#?"relativeTargetSections";
    if not structureMorphism and not relativeTarget
        and (not contraction#?"contractionGraph"
        or not instance(contraction#"contractionGraph",GraphMorphism)) then
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
    -- relativeModelInverseRationalMapData builds the inverse map out of the
    -- Segre coordinates of b2mDiagonalData, which exist only over a projective
    -- base.  Over an affine base the model has no such graph -- the projection
    -- itself is the model's presentation -- so the certificate is not available
    -- and is recorded as absent rather than faked.
    affineModel := model#?"baseIsProjective" and not model#"baseIsProjective";
    inverseData := if identity or affineModel then null
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
        "contractionGraph" => if structureMorphism or relativeTarget then null
            else contraction#"contractionGraph",
        "contractionIsStructureMorphism" => structureMorphism,
        "contractionToRelativeTarget" => relativeTarget,
        "relativeModelData" => model,
        "relativeModelGraph" => model#"relativeModelGraph",
        "inverseRelativeModelData" => inverseData,
        "inverseRelativeModelRequired" => not identity and not affineModel,
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
    CanonicalIndexSearchLimit => null, IrrelevantIdeal => null,
    VariableBlocks => null})
canonicalIndexData Ring := o -> R -> (
    limit := o.CanonicalIndexSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalIndexData: CanonicalIndexSearchLimit must be null or positive";
    B := if o.VariableBlocks =!= null then (
        if o.IrrelevantIdeal =!= null then
            error("canonicalIndexData: supply VariableBlocks or "
                | "IrrelevantIdeal, not both -- the blocks already determine "
                | "the ideal");
        (multigradedBlockData(R,o.VariableBlocks))#"irrelevantIdeal"
        ) else normalizeIrrelevantIdealOption(
            "canonicalIndexData",R,o.IrrelevantIdeal);
    K := mmpCanonicalDivisorInternal R;
    -- Try the two cheap sufficient conditions for Cartier-ness first (no
    -- Hom/Ext call), and fall back to the general test otherwise.  Only a
    -- "yes" may be taken from either: neither is a necessary condition, so a
    -- negative from one carries no information and must not become the
    -- verdict.
    --
    -- That is not hypothetical.  canonicalIdealSeedInvertibleInternal tests
    -- whether the reflexive power of the canonical ideal is a *principal*
    -- ideal, which certifies Cartier-ness but is strictly stronger than it:
    -- principal means globally generated by one element, Cartier only means
    -- locally so, and the two part company as soon as Pic(X) is bigger than
    -- Z*H.  This code previously wrote "if seedCert =!= null then seedCert",
    -- taking its false as a verdict, and the comment here claimed both
    -- certificates could only answer true or null.  Both were wrong.  On the
    -- Segre threefold P1xP2 -- smooth, so every divisor is Cartier and the
    -- canonical index is 1 -- K = O(-2,-3) is not a multiple of H = O(1,1),
    -- the seed test answers false at m = 1, and canonicalIndexData returned
    -- "inconclusive" on a smooth threefold.  On the cyclic cover's flip target
    -- it reported no index up to 12 where the index is 2.
    isCartierAtIndex := m -> (
        candidate := m*K;
        if principalShiftCartierCertificateInternal candidate then true
        else (
            seedCert := canonicalIdealSeedInvertibleInternal(R,K,m);
            if seedCert === true then true
            else if B =!= null then isCartierSaturatedInternal(candidate,B)
            -- mmpIsCartierInternal is the same isCartier call for every
            -- classical ring and the saturated test against the presentation's
            -- own irrelevant ideal over an affine base, where the maximal ideal
            -- isCartier uses contains the base coordinates and is wrong.
            else mmpIsCartierInternal candidate
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
    IrrelevantIdeal => null,
    VariableBlocks => null})
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
    B := (irrelevantIdealDataInternal(
        "threefoldMMPData",initialRing,o.VariableBlocks,
        o.IrrelevantIdeal))#"irrelevantIdeal";
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
    VariableBlocks => null,
    DivisorClassDegrees => null})
canonicalNefData (Ring,ZZ) := o -> (R,a) -> (
    if dim R - 1 != 3 then
        error "canonicalNefData: expected a projective threefold";
    if a <= 0 then
        error "canonicalNefData: the index multiple must be positive";
    limit := o.NefSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalNefData: NefSearchLimit must be null or positive";
    K := mmpCanonicalDivisorInternal R;
    if not mmpIsCartierInternal(a*K) then
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
    idealData := irrelevantIdealDataInternal(
        "canonicalNefData",R,o.VariableBlocks,o.IrrelevantIdeal);
    geometricDimension := idealData#"geometricDimension";
    if geometricDimension != 3 then
        error "canonicalNefData: expected a projective threefold";
    K := mmpCanonicalDivisorInternal R;
    B := idealData#"irrelevantIdeal";
    if not isCartierSaturatedInternal(a*K,B) then
        error "canonicalNefData: a*K_X is not Cartier";
    classDegrees := normalizeDivisorClassDegrees(
        R,o.DivisorClassDegrees,"canonicalNefData");
    result := canonicalNefDataCore(R,a,K,H,limit,B,classDegrees);
    extraKeys := irrelevantIdealResultKeysInternal idealData;
    new HashTable from join(pairs result,join({
        "ampleData" => new HashTable from {"ring" => R,"divisor" => H}},
        extraKeys))
    )

isCanonicalNef = method(Options => options canonicalNefData)
isCanonicalNef (Ring,ZZ) := o -> (R,a) -> (
    -- These two wrappers cover the paper's algorithm as stated, which is for a
    -- monograded variety: Section 3 opens with "Let X = Proj R be a normal
    -- monograded variety", and a bigraded input reaches it through Section
    -- 2.3's w-diagonal, a monograded ring.  The multigraded entry points in
    -- this package are an extension of that, added because the w-diagonal
    -- blows the presentation up in practice, and they live on the data-
    -- returning methods only.  So the two options belong to those and not
    -- here.  They arrive declared regardless, since the option list is
    -- inherited with "options canonicalNefData", and were previously
    -- dropped in silence -- which sent a multigraded ring into the monograded
    -- dimension test and produced "expected a projective threefold" about a
    -- ring that is a threefold.  Refuse them instead and name where to go.
    if o.IrrelevantIdeal =!= null or o.VariableBlocks =!= null then
        error("isCanonicalNef: IrrelevantIdeal and VariableBlocks do not "
            | "apply here.  This wrapper is the paper's monograded algorithm, "
            | "where one variable block leaves the irrelevant ideal with no "
            | "choice to make.  For a multigraded presentation use "
            | "canonicalNefData(R,a,H), which takes both.");
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
      Takehiko Yasuda, {\em An algorithm for the minimal model program in
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
    :X over an affine base
    "the relative setting over an affine base"
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
    Example
      needsPackage("FlipComputation",
          FileName => "third_party/flip-computation/FlipComputation.m2");
      R = QQ[x0,x1,x2,x3,x4]/ideal(x0*x1-x2*x3);
      G = b2mToGraphMorphism bigradedReesProjection ideal(x0,x2);
      class G
      mmpGraphMorphism G === G
    Text
      A @TO GraphMorphism@ is already in the common representation, so it comes
      back as the same object; a legacy hash table is adapted into one.
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
      constructed as a relative $\mathcal{P}roj$ of a Rees algebra,
      substitute the Rees-ideal generators for the
      fibre variables in the Segre coordinates.  The result records homogeneous
      coordinates for $W \dashrightarrow Z$, verifies the model and graph
      equations, and certifies that their base locus is the Rees centre after
      saturation.  Skew weighted fibre coordinates use the positive diagonal
      selected internally by {\tt b2mDiagonalData}.
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
      multigraded presentations into {\tt SteinFactorization}'s
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
      flattened ring, since {\tt SteinFactorization} requires a block-diagonal
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
    (canonicalContractionAtThresholdData,Ring,ZZ,QQ,BasicDivisor)
    (canonicalContractionAtThresholdData,Ring,ZZ,ZZ,BasicDivisor)
  Headline
    construct the contraction at a known canonical nef threshold
  Usage
    result = canonicalContractionAtThresholdData(R,a,lambda)
    result = canonicalContractionAtThresholdData(R,a,lambda,H)
  Description
    Text
      Find a base-point-free multiple of $K_X+\lambda H$, construct its
      complete-linear-system graph, and compute its Stein factorization.  The
      function tests small multiples first and is guaranteed to stop at the
      effective multiplier from the scaled nefness theorem.

      A multigraded ring is handled by the overload that takes the ample
      Cartier class $H$ as an argument: deriving $H$ automatically is not
      attempted there, since @TO weightedAmpleDivisorData@ reads a single set
      of weights.  On such a ring supply the irrelevant ideal as well, with
      @TO IrrelevantIdeal@ -- either as an ideal of $R$ or as the
      {\tt B2MProjection} or {\tt GraphMorphism} that built $R$, which carries
      it.  Without it the call stops rather than guess, whenever the degree
      matrix is not verifiably block diagonal.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      contraction = canonicalContractionAtThresholdData(X,1,3);
      {contraction#"sourceDimension",contraction#"targetDimension"}

Node
  Key
    canonicalContractionData
    (canonicalContractionData,Ring,ZZ)
    (canonicalContractionData,Ring,ZZ,BasicDivisor)
  Headline
    compute the canonical nef threshold and its extremal-face contraction
  Usage
    result = canonicalContractionData(R,a)
    result = canonicalContractionData(R,a,H)
  Inputs
    R:Ring
      the homogeneous coordinate ring of a normal log terminal threefold
    a:ZZ
      a positive integer such that $aK_X$ is Cartier
    H:BasicDivisor
      an ample Cartier divisor, required only in the multigraded form
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

      A multigraded ring is handled by the overload that takes the ample
      Cartier class $H$ as an argument: deriving $H$ automatically is not
      attempted there, since @TO weightedAmpleDivisorData@ reads a single set
      of weights.  On such a ring supply the irrelevant ideal as well, with
      @TO IrrelevantIdeal@ -- either as an ideal of $R$ or as the
      {\tt B2MProjection} or {\tt GraphMorphism} that built $R$, which carries
      it.  Without it the call stops rather than guess, whenever the degree
      matrix is not verifiably block diagonal.
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
    (canonicalNefThresholdData,Ring,ZZ,BasicDivisor)
  Headline
    compute the canonical nef threshold and its search data
  Usage
    result = canonicalNefThresholdData(R,a)
    result = canonicalNefThresholdData(R,a,H)
  Inputs
    R:Ring
      the homogeneous coordinate ring of a normal log terminal threefold
    a:ZZ
      a positive integer such that $aK_X$ is Cartier
    H:BasicDivisor
      an ample Cartier divisor, required only in the multigraded form
  Outputs
    :HashTable
      the rational threshold in @TT "threshold"@ and its search certificates
  Description
    Text
      Assuming that $K_X$ is not nef, compute the first positive rational
      $t$ for which $K_X+tH$ is nef.  The function implements Algorithm 1:
      dyadic searches bracket the threshold and the rationality theorem gives
      a finite candidate list.  The ample Cartier divisor $H$ is the one
      returned by {\tt weightedAmpleDivisorData}.  Call this only after
      @TO canonicalNefData@ has shown that $K_X$ is not nef.  If a search
      bound is reached, @TT "threshold"@ is null and @TT "phase"@
      identifies the unfinished part of the search.

      A multigraded ring is handled by the overload that takes the ample
      Cartier class $H$ as an argument: deriving $H$ automatically is not
      attempted there, since @TO weightedAmpleDivisorData@ reads a single set
      of weights.  On such a ring supply the irrelevant ideal as well, with
      @TO IrrelevantIdeal@ -- either as an ideal of $R$ or as the
      {\tt B2MProjection} or {\tt GraphMorphism} that built $R$, which carries
      it.  Without it the call stops rather than guess, whenever the degree
      matrix is not verifiably block diagonal.
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
    (canonicalNefData,Ring,ZZ,BasicDivisor)
  Headline
    decide whether the canonical divisor of a threefold is nef
  Usage
    result = canonicalNefData(R,a)
    result = canonicalNefData(R,a,H)
  Inputs
    R:Ring
      the homogeneous coordinate ring of a normal log terminal threefold
    a:ZZ
      a positive integer such that $aK_X$ is Cartier
    H:BasicDivisor
      an ample Cartier divisor, required only in the multigraded form
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

      A multigraded ring is handled by the overload that takes the ample
      Cartier class $H$ as an argument: deriving $H$ automatically is not
      attempted there, since @TO weightedAmpleDivisorData@ reads a single set
      of weights.  On such a ring supply the irrelevant ideal as well, with
      @TO IrrelevantIdeal@ -- either as an ideal of $R$ or as the
      {\tt B2MProjection} or {\tt GraphMorphism} that built $R$, which carries
      it.  Without it the call stops rather than guess, whenever the degree
      matrix is not verifiably block diagonal.
    Example
      S = QQ[z00,z01,z02,z10,z11,z12];
      X = S/minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
      nefData = canonicalNefData(X,1);
      {nefData#"nef",nefData#"witnessType"}
  Caveat
    With no search limit the algorithm terminates under the stated threefold
    hypotheses by abundance.  Passing {\tt NefSearchLimit} makes the computation
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
    (canonicalScaledNefData,Ring,ZZ,QQ,BasicDivisor)
    (canonicalScaledNefData,Ring,ZZ,ZZ,BasicDivisor)
  Headline
    decide whether K_X+tH is nef for positive rational t
  Usage
    result = canonicalScaledNefData(R,a,t)
    result = canonicalScaledNefData(R,a,t,H)
  Description
    Text
      Test small positive multiples first.  A base-point-free multiple proves
      nefness; a negative intersection with a curve obtained from its base
      locus proves non-nefness.  If neither short certificate is found, use the
      effective base-point-free multiplier from Proposition 3.1.

      A multigraded ring is handled by the overload that takes the ample
      Cartier class $H$ as an argument: deriving $H$ automatically is not
      attempted there, since @TO weightedAmpleDivisorData@ reads a single set
      of weights.  On such a ring supply the irrelevant ideal as well, with
      @TO IrrelevantIdeal@ -- either as an ideal of $R$ or as the
      {\tt B2MProjection} or {\tt GraphMorphism} that built $R$, which carries
      it.  Without it the call stops rather than guess, whenever the degree
      matrix is not verifiably block diagonal.
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
    Text
      On the bigraded $\mathbb{P}^1\times\mathbb{P}^2$, where
      $K=\mathcal{O}(-2,-3)$ and $H=\mathcal{O}(1,1)$, the divisor $K+2H$ is
      $\mathcal{O}(0,-1)$: it has no sections at all, so its base locus is
      everything and the zero ideal contains it.  The witness found is a
      $\{\mathrm{pt}\}\times\{\mathrm{line}\}$ curve, on which
      $\mathcal{O}(0,-1)$ restricts to $\mathcal{O}_{\mathbb{P}^1}(-1)$.
    Example
      needsPackage "WeilDivisors";
      S = QQ[s,t,u,v,w, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
      H = divisor(s) + divisor(u);
      K = canonicalDivisor(S,IsGraded=>true);
      B = ideal(s,t) * ideal(u,v,w);
      witness = negativeCurveWitnessData(K + 2*H, ideal 0_S, B, {1,1});
      witness#"intersection"
    Text
      A base-point-free divisor gives @TO null@ rather than a spurious
      witness.
    Example
      negativeCurveWitnessData(H, ideal 0_S, B, {1,1})

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
    VariableBlocks
  Headline
    name the variable blocks of a multigraded presentation
  Description
    Text
      A list of lists of variables, one block per degree component, together
      partitioning the variables of the ring exactly.  Their order does not
      matter.
    Text
      This is the datum a multigraded presentation carries in the paper:
      Definition 2.5 writes the ambient ring as $k[\boldsymbol{y},\boldsymbol{x}]$, so
      which variables are $y$'s and which are $x$'s is part of the
      presentation, and the irrelevant ideal
      $S_\dagger=\langle y_jx_i\rangle S$ follows from it.  An irrelevant
      ideal is the product of the ideals of the blocks and nothing else, so
      naming the blocks decides it.
    Text
      Naming them is necessary because the degrees no longer determine them.
      Section 2.2 sets $\deg(y_j)=(d_j,0)$ but $\deg(x_i)=(a_i,c_i)$, with
      $\mathbf{a}$ a further datum, so a second-block variable may be nonzero
      in the first component and the internal classification of
      a variable by the last nonzero entry of its degree cannot tell it from a
      first-block one.  On such a ring that heuristic can return an ideal with
      the wrong radical, and every entry point refuses to use it -- see
      tests/multigraded-skew-cartier.m2, where one variable of degree $(1,1)$
      is the whole discrepancy.
    Text
      Prefer this to @TO IrrelevantIdeal@.  Blocks are a property of the
      variables and so carry from one presentation to another, whereas an
      ideal belongs to the single ring it lives in.  Supplying both is an
      error, since the blocks already determine the ideal.

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
      {\tt IrrelevantIdeal=>B} to canonicalScaledNefData,
      canonicalNefThresholdData, canonicalNefData,
      canonicalContractionAtThresholdData, or canonicalContractionData uses
      B verbatim for that entry point's own Cartier gate instead of
      re-deriving one, when a caller already holds a known-correct ideal.
      Default null preserves the previous re-derivation exactly.
    Text
      The value may also be the {\tt B2MProjection} or {\tt GraphMorphism} that built the
      ring, in place of an ideal: its own irrelevantIdeal field is read and
      moved into the ring for you, so a caller no longer writes
      $\mathtt{sub(P\#irrelevantIdeal,R)}$ by hand.  What makes that sound is
      that an irrelevant ideal is the product of the ideals of the variable
      blocks and nothing more, so the datum deciding it is the partition of
      the variables into blocks -- which is precisely what these objects
      already carry, in their fibreVariables and baseVariables, and precisely
      what the skew grading defeats multigradedBlockData's heuristic at.  A
      provenance object whose ambient variables do not match the ring's is
      rejected rather than substituted by position.

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
Node
  Key
    [canonicalScaledNefData, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the scaled-nefness test
  Usage
    canonicalScaledNefData(R,a,t,H,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.

Node
  Key
    [canonicalNefThresholdData, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the threshold search
  Usage
    canonicalNefThresholdData(R,a,H,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.

Node
  Key
    [canonicalNefData, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the nefness test
  Usage
    canonicalNefData(R,a,H,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.

Node
  Key
    [canonicalContractionAtThresholdData, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the contraction at a threshold
  Usage
    canonicalContractionAtThresholdData(R,a,lambda,H,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.

Node
  Key
    [canonicalContractionData, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the threshold and contraction
  Usage
    canonicalContractionData(R,a,H,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.

Node
  Key
    [threefoldMMPData, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the MMP driver's first step
  Usage
    threefoldMMPData(R,a,H,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.
    Text
      It applies to the multigraded first step only.  Once a birational step is
      recorded the driver's own next ring is singly graded, so the remaining
      iterations need no irrelevant ideal of their own.

Node
  Key
    [canonicalIndexData, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the canonical-index search
  Usage
    canonicalIndexData(R,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.
    Text
      When supplied, the fallback test uses the saturated Cartier predicate
      instead of the generic {\tt isCartier}, which also avoids
      {\tt WeilDivisors}' own irrelevant ideal being wrong on a mixed-sign
      multigraded ring.

Node
  Key
    [completeLinearSystemGraphDataMultigraded, IrrelevantIdeal]
  Headline
    supply the irrelevant ideal to the multigraded linear-system graph
  Usage
    completeLinearSystemGraphDataMultigraded(D,w,IrrelevantIdeal=>B)
  Description
    Text
      On a multigraded ring whose degree matrix is not verifiably block
      diagonal this is required: without it the call stops rather than guess
      an irrelevant ideal.  The value is an ideal of the ring, or the
      {\tt B2MProjection} or {\tt GraphMorphism} that built it, which carries
      the variable-block partition the ideal is the product of.

Node
  Key
    [isCanonicalNef, IrrelevantIdeal]
  Headline
    not applicable; use canonicalNefData
  Usage
    isCanonicalNef(R,a,IrrelevantIdeal=>B)
  Description
    Text
      Refused.  This method is the paper's algorithm as stated, for a
      monograded variety -- Section 3 opens with "Let $X=\operatorname{Proj}R$
      be a normal monograded variety", and a bigraded input reaches it through
      Section 2.3's $\mathbf{w}$-diagonal, which is again monograded.  With one
      variable block the irrelevant ideal is the ideal of all the variables and
      there is nothing to supply.
    Text
      The multigraded entry points are this package's extension of the paper,
      added because the $\mathbf{w}$-diagonal blows the presentation up in
      practice, and they are the data-returning methods.  Use
      @TO canonicalNefData@ on a multigraded presentation.  The option is
      declared here only because the option list is inherited with
      {\tt options canonicalNefData}.

Node
  Key
    [canonicalNefThreshold, IrrelevantIdeal]
  Headline
    not applicable; use canonicalNefThresholdData
  Usage
    canonicalNefThreshold(R,a,IrrelevantIdeal=>B)
  Description
    Text
      Refused.  This method is the paper's algorithm as stated, for a
      monograded variety -- Section 3 opens with "Let $X=\operatorname{Proj}R$
      be a normal monograded variety", and a bigraded input reaches it through
      Section 2.3's $\mathbf{w}$-diagonal, which is again monograded.  With one
      variable block the irrelevant ideal is the ideal of all the variables and
      there is nothing to supply.
    Text
      The multigraded entry points are this package's extension of the paper,
      added because the $\mathbf{w}$-diagonal blows the presentation up in
      practice, and they are the data-returning methods.  Use
      @TO canonicalNefThresholdData@ on a multigraded presentation.  The option is
      declared here only because the option list is inherited with
      {\tt options canonicalNefThresholdData}.

Node
  Key
    [canonicalNefData, DivisorClassDegrees]
  Headline
    supply the canonical and ample class degrees
  Usage
    canonicalNefData(R,a,H,DivisorClassDegrees=>{dK,dH})
  Description
    Text
      Pass @TT "{degree(K),degree(H)}"@ when they are already known, to skip
      re-deriving them; the value is forwarded to the nested
      @TO canonicalScaledNefData@ tests.

Node
  Key
    [canonicalScaledNefData, DivisorClassDegrees]
  Headline
    supply the canonical and ample class degrees
  Usage
    canonicalScaledNefData(R,a,t,H,DivisorClassDegrees=>{dK,dH})
  Description
    Text
      Pass @TT "{degree(K),degree(H)}"@ when they are already known, to skip
      re-deriving them.  Default null recomputes both.

Node
  Key
    [isCanonicalNef, DivisorClassDegrees]
  Headline
    supply the canonical and ample class degrees
  Usage
    isCanonicalNef(R,a,DivisorClassDegrees=>{dK,dH})
  Description
    Text
      Forwarded verbatim to @TO canonicalNefData@.

Node
  Key
    [canonicalContractionData, ThresholdSearchLimit]
  Headline
    bound the threshold search inside the contraction
  Usage
    canonicalContractionData(R,a,ThresholdSearchLimit=>n)
  Description
    Text
      Forwarded to @TO canonicalNefThresholdData@.  If the bound is reached the
      result is inconclusive with @TT "phase"@ set to the threshold search.

Node
  Key
    [threefoldMMPData, ThresholdSearchLimit]
  Headline
    bound each step's threshold search
  Usage
    threefoldMMPData(R,a,ThresholdSearchLimit=>n)
  Description
    Text
      Forwarded to every step's @TO canonicalContractionData@ call.

Node
  Key
    [canonicalContractionAtThresholdData, ContractionMultipleLimit]
  Headline
    bound the multiples tested at the threshold
  Usage
    canonicalContractionAtThresholdData(R,a,lambda,ContractionMultipleLimit=>n)
  Description
    Text
      Test at most n multiples of $K_X+\lambda H$ before giving up.  The number
      actually tested is reported in @TT "multipliersTested"@.

Node
  Key
    [canonicalContractionData, ContractionMultipleLimit]
  Headline
    bound the multiples tested when contracting
  Usage
    canonicalContractionData(R,a,ContractionMultipleLimit=>n)
  Description
    Text
      Forwarded to @TO canonicalContractionAtThresholdData@.

Node
  Key
    [threefoldMMPData, ContractionMultipleLimit]
  Headline
    bound each step's contraction multiples
  Usage
    threefoldMMPData(R,a,ContractionMultipleLimit=>n)
  Description
    Text
      Forwarded to every step's @TO canonicalContractionData@ call.

Node
  Key
    [threefoldMMPData, NefSearchLimit]
  Headline
    bound each step's nefness search
  Usage
    threefoldMMPData(R,a,NefSearchLimit=>n)
  Description
    Text
      Forwarded to every step's @TO canonicalNefData@ call.  Reaching it stops
      the driver with @TT "phase"@ set to nefness.

Node
  Key
    [canonicalIndexData, CanonicalIndexSearchLimit]
  Headline
    bound the canonical-index search
  Usage
    canonicalIndexData(R,CanonicalIndexSearchLimit=>n)
  Description
    Text
      Try the multiples $i = 1,\dots,n$ and report an inconclusive result if
      none of them makes $iK_X$ Cartier.  Default null searches unbounded.

Node
  Key
    [threefoldMMPData, CanonicalIndexSearchLimit]
  Headline
    bound each step's canonical-index search
  Usage
    threefoldMMPData(R,a,CanonicalIndexSearchLimit=>n)
  Description
    Text
      Forwarded to the @TO canonicalIndexData@ call that computes the index of
      each new ring the driver reaches.

Node
  Key
    [threefoldMMPData, MMPMaxSteps]
  Headline
    bound the number of MMP steps
  Usage
    threefoldMMPData(R,a,MMPMaxSteps=>n)
  Description
    Text
      Stop after n birational steps and report @TT "phase"@ as the step limit.
      Default null iterates until a minimal model or a K-negative fibration is
      reached.

Node
  Key
    [relativeCanonicalModelFromBaseData, RelativeCanonicalMultipliers]
  Headline
    give the multiplier list explicitly
  Usage
    relativeCanonicalModelFromBaseData(W,RelativeCanonicalMultipliers=>L)
  Description
    Text
      Try exactly the multipliers in L, in order, instead of the consecutive
      search $m = 1, 2, 3, \dots$ of Algorithm 4.

Node
  Key
    [relativeCanonicalModelFromBaseData, RelativeCanonicalMaxMultiplier]
  Headline
    cap the multiplier search
  Usage
    relativeCanonicalModelFromBaseData(W,RelativeCanonicalMaxMultiplier=>m)
  Description
    Text
      Stop after multiplier m.  Exhausting the search is reported as an
      inconclusive result, not raised as an error.

Node
  Key
    [relativeCanonicalModelFromBaseData, RelativeCanonicalVerbose]
  Headline
    show the model computation's progress
  Usage
    relativeCanonicalModelFromBaseData(W,RelativeCanonicalVerbose=>true)

Node
  Key
    [relativeCanonicalModelData, RelativeCanonicalMultipliers]
  Headline
    give the multiplier list explicitly
  Usage
    relativeCanonicalModelData(contraction,RelativeCanonicalMultipliers=>L)
  Description
    Text
      Forwarded to @TO relativeCanonicalModelFromBaseData@.

Node
  Key
    [relativeCanonicalModelData, RelativeCanonicalMaxMultiplier]
  Headline
    cap the multiplier search
  Usage
    relativeCanonicalModelData(contraction,RelativeCanonicalMaxMultiplier=>m)
  Description
    Text
      Forwarded to @TO relativeCanonicalModelFromBaseData@.

Node
  Key
    [relativeCanonicalModelData, RelativeCanonicalVerbose]
  Headline
    show the model computation's progress
  Usage
    relativeCanonicalModelData(contraction,RelativeCanonicalVerbose=>true)

Node
  Key
    [threefoldMMPData, RelativeCanonicalMultipliers]
  Headline
    give each step's multiplier list explicitly
  Usage
    threefoldMMPData(R,a,RelativeCanonicalMultipliers=>L)
  Description
    Text
      Forwarded to every step's @TO relativeCanonicalModelData@ call.

Node
  Key
    [threefoldMMPData, RelativeCanonicalMaxMultiplier]
  Headline
    cap each step's multiplier search
  Usage
    threefoldMMPData(R,a,RelativeCanonicalMaxMultiplier=>m)
  Description
    Text
      Forwarded to every step's @TO relativeCanonicalModelData@ call.  A step
      that exhausts it stops the driver with @TT "phase"@ set to the relative
      canonical model.

Node
  Key
    [threefoldMMPData, RelativeCanonicalVerbose]
  Headline
    show each step's model computation
  Usage
    threefoldMMPData(R,a,RelativeCanonicalVerbose=>true)

Node
  Key
    [mmpStepRecordData, ContractionIsSmall]
  Headline
    assert the contraction's smallness instead of computing it
  Usage
    mmpStepRecordData(contraction,model,ContractionIsSmall=>true)
  Description
    Text
      Skip @TO contractionSmallnessData@ and take the given Boolean as the
      answer, which is what distinguishes a flipping step from a mixed one.
      The certificate is the caller's responsibility; default null computes it.

Node
  Key
    [negativeCurveWitnessData, NegativeCurveSearchLimit]
  Headline
    bound the dimension-reducing cuts
  Usage
    negativeCurveWitnessData(D,candidateBaseLocus,B,h,NegativeCurveSearchLimit=>n)
  Description
    Text
      Make at most n coordinate cuts while reducing a base-locus component to a
      curve, then give up and return @TO null@.  The default is 8.

Node
  Key
    [canonicalScaledNefData, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    canonicalScaledNefData(R,a,t,H,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [canonicalNefThresholdData, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    canonicalNefThresholdData(R,a,H,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [canonicalNefData, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    canonicalNefData(R,a,H,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [canonicalContractionAtThresholdData, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    canonicalContractionAtThresholdData(R,a,lambda,H,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [canonicalContractionData, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    canonicalContractionData(R,a,H,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [threefoldMMPData, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    threefoldMMPData(R,a,H,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [canonicalIndexData, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    canonicalIndexData(R,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [completeLinearSystemGraphDataMultigraded, VariableBlocks]
  Headline
    name the variable blocks instead of the irrelevant ideal
  Usage
    completeLinearSystemGraphDataMultigraded(D,w,VariableBlocks=>blks)
  Description
    Text
      See @TO VariableBlocks@.  The blocks determine the irrelevant ideal, so
      passing @TO IrrelevantIdeal@ as well is an error.

Node
  Key
    [isCanonicalNef, VariableBlocks]
  Headline
    not applicable; use canonicalNefData
  Usage
    isCanonicalNef(R,a,VariableBlocks=>blks)
  Description
    Text
      Refused.  This method is the paper's algorithm as stated, for a
      monograded variety -- Section 3 opens with "Let $X=\operatorname{Proj}R$
      be a normal monograded variety", and a bigraded input reaches it through
      Section 2.3's $\mathbf{w}$-diagonal, which is again monograded.  With one
      variable block the irrelevant ideal is the ideal of all the variables and
      there is nothing to supply.
    Text
      The multigraded entry points are this package's extension of the paper,
      added because the $\mathbf{w}$-diagonal blows the presentation up in
      practice, and they are the data-returning methods.  Use
      @TO canonicalNefData@ on a multigraded presentation.  The option is
      declared here only because the option list is inherited with
      {\tt options canonicalNefData}.

Node
  Key
    [canonicalNefThreshold, VariableBlocks]
  Headline
    not applicable; use canonicalNefThresholdData
  Usage
    canonicalNefThreshold(R,a,VariableBlocks=>blks)
  Description
    Text
      Refused.  This method is the paper's algorithm as stated, for a
      monograded variety -- Section 3 opens with "Let $X=\operatorname{Proj}R$
      be a normal monograded variety", and a bigraded input reaches it through
      Section 2.3's $\mathbf{w}$-diagonal, which is again monograded.  With one
      variable block the irrelevant ideal is the ideal of all the variables and
      there is nothing to supply.
    Text
      The multigraded entry points are this package's extension of the paper,
      added because the $\mathbf{w}$-diagonal blows the presentation up in
      practice, and they are the data-returning methods.  Use
      @TO canonicalNefThresholdData@ on a multigraded presentation.  The option is
      declared here only because the option list is inherited with
      {\tt options canonicalNefThresholdData}.

Node
  Key
    "the relative setting over an affine base"
  Headline
    X = Proj R projective over the affine Spec R_0, where R_0 need not be a field
  Description
    Text
      Section 3 of the paper takes $X = \operatorname{Proj} R$ with $R_0 = k$,
      so that $X$ is projective over a point.  Giving an ambient variable
      degree zero puts its coordinate into $R_0$ instead, and
      $X = \operatorname{Proj} R$ becomes projective over the affine
      $\operatorname{Spec} R_0$.  There is no option to set: every entry point
      reads the case off the presentation, by looking for an ambient variable
      all of whose degrees are zero, and every part of the relative reading is
      inert when $R_0 = k$.  So a presentation with degree-zero variables is
      the whole interface.

      This is where the standard three-fold flips are.  A flipping contraction
      contracts a curve to a point of an affine variety, so it is not a
      morphism of projective varieties and does not appear in the absolute
      setting unless it is compactified first.

      How long a relative program can be turns on which target the contraction
      at the threshold has.  If it is $\operatorname{Spec} R_0$ itself then
      Algorithm 4 returns the whole relative canonical model at once and the
      program is over; contracting to an intermediate variety over
      $\operatorname{Spec} R_0$ instead is what lets one step hand a ring on to
      the next, and that is what makes a relative program more than one
      birational step long.

      The smallest input is the blow-up of the origin in $\mathbb{A}^3$, as
      $\operatorname{Proj}$ of the Rees algebra of $(a,b,c)$.  There
      $K = 2E$ and $\mathcal{O}_X(1) = -E$, so $K + tH = (2-t)E$ is nef exactly
      for $t \geq 2$.  The contraction at the threshold is the structure
      morphism $X \to \operatorname{Spec} R_0$, its exceptional locus is a
      surface in a threefold, so the step is divisorial and the program stops
      at $\mathbb{A}^3$.  Load the package as in @TO MMPComputation@ first; the
      examples below carry on from one another.
    Example
      reesRing = QQ[a,b,c,x,y,z, Degrees => {0,0,0,1,1,1}];
      blowup = reesRing/minors(2,matrix{{a,b,c},{x,y,z}});
      canonicalNefThreshold(blowup,1)
      blowupProgram = threefoldMMPData(blowup,1);
      blowupProgram#"terminationType"
      apply(blowupProgram#"steps", record -> record#"stepType")
      flatten degrees blowupProgram#"finalRing"
    Text
      The final ring has three variables of degree zero and one of degree one.
      A contraction to the affine base has $\operatorname{Spec} R_0$ for its
      target, which is not a $\operatorname{Proj}$ and so not something the next
      iteration could read; it is handed back as $\operatorname{Proj}$ of
      $R_0[t]$, whose $\operatorname{Proj}$ is $\operatorname{Spec} R_0$ again.

      A contraction result says which kind of target it found.  The structure
      morphism to the base records @TT "contractionIsStructureMorphism"@,
      @TT "affineBaseDimension"@, and a @TT "steinFactorizationType"@ of
      {\tt "structure morphism to the affine base"}.  A target that is neither
      the base nor a point records @TT "relativeTargetRing"@ -- again a graded
      ring whose degree-zero part is $R_0$, so the next step starts from it
      directly -- and a @TT "steinFactorizationType"@ of
      {\tt "trivial: birational onto a normal image over the affine base"}.
      That second one is a certificate rather than a computation: the morphism
      is certified birational onto its image by an explicit ratio of sections
      for each coordinate, the image is checked normal, and Zariski's main
      theorem then gives $\Phi_* \mathcal{O}_X = \mathcal{O}$ of the image, so
      the Stein factorization is trivial and is skipped rather than assumed.

      Here is a flip, found from the ring alone.  Take the toric circuit
      $v_1 + v_2 = 2v_3 + v_4$ in $N = \mathbb{Z}^3$ with $v_1 = (1,0,0)$,
      $v_2 = (0,1,0)$, $v_3 = (0,0,1)$ and $v_4 = (1,1,-2)$, and let
      $\operatorname{Spec} R_0 = \operatorname{Spec} k[\sigma^\vee \cap M]$ for
      $\sigma = \operatorname{cone}(v_1,v_2,v_3,v_4)$, an affine threefold that
      is not $\mathbb{Q}$-Gorenstein.  The two triangulations of the circuit
      are its two small modifications; on the one below, $Y$, the wall curve has
      $K \cdot C = -1$, so $Y \to \operatorname{Spec} R_0$ is a flipping
      contraction.  $Y$ has one $\tfrac12(1,1,1)$ point, so its canonical index
      is 2, and the program finds the threshold, checks that the contraction is
      small -- exceptional locus of dimension one in a threefold -- and then
      flips.
    Example
      monomialRing = QQ[ea,eb,ec,et];
      circuitBase = {eb, eb^2*ec, ea, ea*eb*ec, ea^2*ec};
      flippingSide = QQ[p_1 .. p_5, q_1, q_2, Degrees => {0,0,0,0,0,1,1}];
      Y = flippingSide/ker map(monomialRing, flippingSide,
          circuitBase | {ea^2*eb^2*ec^2*et, ea^2*eb^2*ec^3*et});
      (canonicalIndexData Y)#"index"
      canonicalNefThreshold(Y,2)
      flipProgram = threefoldMMPData(Y,2);
      flipProgram#"terminationType"
      apply(flipProgram#"steps", record -> record#"stepType")
      apply(flipProgram#"steps", record -> record#"contractionIsSmall")
    Text
      A flipping step is the one place where Algorithm 4 constructs rather than
      recognizes: read @TT "isIdentity"@ off the step's
      @TT "relativeModelData"@, which is false here and true for a divisorial
      step onto a $\mathbb{Q}$-Gorenstein target.

      Programs over an affine base can be longer.  Take the toric surface
      $S_3$ obtained from $\mathbb{A}^2$ by blowing up the origin and then a
      torus-fixed point of each successive exceptional curve, and let
      $X = S_3 \times \mathbb{A}^1$ over $\mathbb{A}^3$.  Its three exceptional
      curves have $K \cdot E = 0, 0, -1$, and the same holds again after each
      contraction, so the program is forced to contract them one at a time and
      takes three divisorial steps to reach $\mathbb{A}^3$.
    Example
      threeStepAmbient = QQ[a3,b3,c3,w_0,w_1,w_2,w_3,
          Degrees => {0,0,0,1,1,1,1}];
      threeStep = threeStepAmbient/ker map(monomialRing, threeStepAmbient,
          {ea,eb,ec, ea^3*et, ea^2*eb*et, ea*eb^3*et, eb^6*et});
      threeStepProgram = threefoldMMPData(threeStep,1);
      threeStepProgram#"numberOfSteps"
      apply(threeStepProgram#"steps", record -> record#"stepType")
      apply(threeStepProgram#"steps", record -> flatten degrees record#"nextRing")
    Text
      A program can also be three steps long and end in a flip; that one is
      {\tt examples/09-three-step-flip.m2} in the repository, and it takes a
      couple of minutes rather than seconds.  The flip has to be its last step,
      and that is a property of the setting rather than of the input.  The
      flipping contraction this package can carry out is the structure
      morphism, which is the contraction at the threshold only when the
      relative Picard rank is one; a flip onto an intermediate target would ask
      @TO relativeCanonicalModelFromBaseData@ for the relative canonical model
      of a base that is itself a $\operatorname{Proj}$ over
      $\operatorname{Spec} R_0$, whose Rees construction has degree-zero fibre
      variables and no heft vector.  So the relative Picard rank has to be
      spent on divisorial steps first.

      Four things are worth knowing before presenting an input this way.

      {\em Give every positive-degree generator degree one.}  On a weighted
      presentation $\operatorname{Spec} R \setminus V(B)$ is not a torsor over
      $X$, so a divisor can be locally free on the punctured cone without being
      invertible on $X$ -- the same thing that happens to $\mathcal{O}(1)$ on
      $\mathbb{P}(1,1,2)$ -- and the Cartier test over-reports: on a
      presentation of the $Y$ above that needs a degree-two generator, the
      canonical index comes back as 1 where it is 2.  A Veronese presentation
      avoids it, and is what the example above uses.

      {\em Fibre-type contractions onto an intermediate target are refused.}
      Certifying that their fibres are connected needs the $A$-module version
      of the section-ring lemma, which is not implemented; the refusal names it
      rather than assuming the Stein factorization is trivial.

      {\em Section counts have to be taken with the basis command.}  A
      degree-zero variable cannot be given a positive weight, so $R$ has no
      heft vector, and @TO rank@, @TO prune@ and @TO hilbertFunction@ all fail
      on modules over it where @TO basis@ still works.  This matters if you
      compute alongside the package rather than only through it.

      {\em A Weil divisor of $\operatorname{Spec} R$ can have components that
      are not on $X$.}  Over an affine base the irrelevant ideal $B$ has height
      one exactly when $X \to \operatorname{Spec} R_0$ is birational, and then a
      divisor can have prime components inside $V(B)$, which
      $\operatorname{Proj}$ removes.  They change every section count taken from
      the graded module, and the package drops them from the canonical divisor
      at the source.

      What the implementation needed, item by item, is in
      {\tt docs/IMPLEMENTATION-STATUS.md} under "The relative setting"; what
      the paper's statements need is audited in
      {\tt references/AlgoMMP/RELATIVE-SETTING-AUDIT.md}.  The worked examples
      are {\tt examples/07-affine-base-flip.m2},
      {\tt examples/08-three-step-program.m2} and
      {\tt examples/09-three-step-flip.m2}, and the regressions are
      {\tt tests/relative-affine-flip-mmp.m2},
      {\tt tests/three-step-relative-mmp.m2} and
      {\tt tests/three-step-flip-mmp.m2}.
  SeeAlso
    threefoldMMPData
    canonicalContractionData
    relativeCanonicalModelData
    contractionSmallnessData

///

endPackage "MMPComputation"
