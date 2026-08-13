-- -*- coding: utf-8 -*-
needsPackage("SteinFactorization",
    FileName=>"third_party/SteinFactorizationM2/SteinFactorization.m2");
needsPackage("FlipComputation",
    FileName=>"third_party/flip-computation/FlipComputation.m2");
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

export {
    "weightedAmpleDivisorData",
    "effectiveNefMultiplier",
    "isBasePointFreeDivisor",
    "canonicalScaledNefData",
    "canonicalNefThresholdData",
    "canonicalNefThreshold",
    "completeLinearSystemGraphData",
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
    "RelativeCanonicalMaxSteps",
    "RelativeCanonicalVerbose",
    "ContractionIsSmall",
    "CanonicalIndexSearchLimit",
    "MMPMaxSteps"
    }

weilDivisorsPackage := needsPackage "WeilDivisors";
weilDivisorToModule := value(
    weilDivisorsPackage#"private dictionary"#"divisorToModule");

-- Stage 1 (T1) of docs/STAGE1-MEASUREMENT-PLAN.md: block structure and the
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
    new HashTable from {
        "ring" => R,
        "rank" => r,
        "permutation" => usedPermutation,
        "blockAssignment" => assignment,
        "blockVariableIndices" => blockIndices,
        "blockVariables" => blockVariables,
        "blockIdeals" => blockIdeals,
        "irrelevantIdeal" => B,
        "geometricDimension" => dim R - r
        }
    )

-- Lemma 3.5 of the paper: if X is presented in a weighted projective space
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

isBasePointFreeDivisor = method()
isBasePointFreeDivisor BasicDivisor := D -> (
    R := ring D;
    trim baseLocus D == ideal 1_R
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

canonicalScaledNefDataInternal = (R,K,H,a,t) -> (
    if t <= 0 then
        error "canonicalScaledNefData: t must be a positive rational number";
    p := if instance(t,ZZ) then t else numerator t;
    q := if instance(t,ZZ) then 1 else denominator t;
    d := dim R - 1;
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
        if useNegativeCurveShortcut then (
            candidateBaseLocus = trim baseLocus candidateDivisor;
            candidateBPF = candidateBaseLocus == ideal 1_R;
            )
        else candidateBPF = isBasePointFreeDivisor candidateDivisor;
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
canonicalScaledNefData = method()
canonicalScaledNefData (Ring,ZZ,QQ) := (R,a,t) -> (
    if a <= 0 then
        error "canonicalScaledNefData: the index multiple must be positive";
    K := canonicalDivisor(R,IsGraded=>true);
    if not isCartier(a*K,IsGraded=>true) then
        error "canonicalScaledNefData: a*K_X is not Cartier";
    H := (weightedAmpleDivisorData R)#"divisor";
    canonicalScaledNefDataInternal(R,K,H,a,t)
    )
canonicalScaledNefData (Ring,ZZ,ZZ) := (R,a,t) ->
    canonicalScaledNefData(R,a,t/1)

-- Algorithm 1 of the paper.  First bracket the positive threshold by dyadic
-- rationals, then enumerate the finite set supplied by the rationality
-- theorem.  The threshold v/u in lowest terms has 1 <= v <= a(d+1).
canonicalNefThresholdData = method(Options => {ThresholdSearchLimit => null})
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
    tests := {};
    testsRun := 0;
    testCache := new MutableHashTable;
    testAt := t -> (
        if testCache#?t then return testCache#t;
        if limit =!= null and testsRun >= limit then return null;
        result := canonicalScaledNefDataInternal(R,K,H,a,t);
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
            "ampleData" => ampleData,
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
            "ampleData" => ampleData,
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
    threshold := null;
    thresholdTest := null;
    scan(candidates,t -> if threshold === null then (
        candidateTest := testAt(t);
        if candidateTest =!= null and candidateTest#"nef" then (
            threshold = t;
            thresholdTest = candidateTest;
            );
        ));
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
            "canonicalDivisor" => K,
            "ampleData" => ampleData,
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
        "canonicalDivisor" => K,
        "ampleData" => ampleData
        }
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
-- Cartier divisor.  mapToProjectiveSpace represents its sections in a common
-- rational trivialization; their polynomial representatives can therefore
-- have an artificial common zero divisor.  The kernel into R[t] is the Rees
-- graph closure and is insensitive to that choice of trivialization.
completeLinearSystemGraphData = method()
completeLinearSystemGraphData BasicDivisor := D -> (
    if not isBasePointFreeDivisor D then
        error "completeLinearSystemGraphData: the divisor is not base-point-free";
    R := ring D;
    S := ambient R;
    if degreeLength S != 1 then
        error "completeLinearSystemGraphData: expected a singly graded ring";
    sourceIdeal := ideal R;
    sectionMap := mapToProjectiveSpace(D,Variable=>"mmpLinearSystemTarget");
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

canonicalContractionAtThresholdData = method(
    Options => {ContractionMultipleLimit => null})
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
    p := numerator lambda;
    q := denominator lambda;
    N := a*q;
    cartierThresholdDivisor := q*a*K+a*p*H;
    guaranteedMultiplier := effectiveNefMultiplier(dim R-1,N);
    maximum := if limit === null then guaranteedMultiplier
        else min(limit,guaranteedMultiplier);
    multiplier := 1;
    morphismDivisor := cartierThresholdDivisor;
    while multiplier <= maximum
        and not isBasePointFreeDivisor morphismDivisor do (
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
            "ampleData" => ampleData,
            "warning" => "the optional contraction multiple limit was reached"
            };
    linearSystemGraph := completeLinearSystemGraphData morphismDivisor;
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
            "canonicalDivisor" => K,
            "ampleData" => ampleData
            },pairs contractionTypeData(dim R-1,0));
    homData := steinHomData(
        linearSystemGraph#"productRing",linearSystemGraph#"graphIdeal");
    algebraData := steinCoordinateAlgebra homData;
    rawContractionGraph := directSteinGraph(homData,algebraData);
    contractionGraphData := new HashTable from join(pairs rawContractionGraph,{
        "sourceRing" => R,
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
        "canonicalDivisor" => K,
        "ampleData" => ampleData
        },pairs contractionTypeData(dim R-1,targetDimension))
    )
canonicalContractionAtThresholdData (Ring,ZZ,ZZ) := o -> (R,a,lambda) ->
    canonicalContractionAtThresholdData(R,a,lambda/1,
        ContractionMultipleLimit=>o.ContractionMultipleLimit)

canonicalContractionData = method(Options => {
    ThresholdSearchLimit => null,
    ContractionMultipleLimit => null})
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

-- Algorithm 3, applied to the base W of a birational contraction.  If the
-- canonical module already embeds as the unit ideal, its relative canonical
-- Proj is W itself; otherwise FlipComputation constructs the model as a graph.
relativeCanonicalModelFromBaseData = method(Options => {
    RelativeCanonicalMultipliers => null,
    RelativeCanonicalMaxSteps => 4,
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
    modelProjection := computeFlip(W,
        Multipliers=>o.RelativeCanonicalMultipliers,
        MaxSteps=>o.RelativeCanonicalMaxSteps,
        ReturnGraph=>false,
        BaseIsProjective=>true,
        Verbose=>o.RelativeCanonicalVerbose);
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
        RelativeCanonicalMaxSteps=>o.RelativeCanonicalMaxSteps,
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

canonicalIndexData = method(Options => {CanonicalIndexSearchLimit => null})
canonicalIndexData Ring := o -> R -> (
    limit := o.CanonicalIndexSearchLimit;
    if limit =!= null and (not instance(limit,ZZ) or limit <= 0) then
        error "canonicalIndexData: CanonicalIndexSearchLimit must be null or positive";
    K := canonicalDivisor(R,IsGraded=>true);
    i := 1;
    while (limit === null or i <= limit)
        and not isCartier(i*K,IsGraded=>true) do i = i+1;
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
    RelativeCanonicalMaxSteps => 4,
    RelativeCanonicalVerbose => false})
threefoldMMPData (Ring,ZZ) := o -> (initialRing,initialIndex) ->
    threefoldMMPData(initialRing,initialIndex,{},
        MMPMaxSteps=>o.MMPMaxSteps,
        CanonicalIndexSearchLimit=>o.CanonicalIndexSearchLimit,
        NefSearchLimit=>o.NefSearchLimit,
        ThresholdSearchLimit=>o.ThresholdSearchLimit,
        ContractionMultipleLimit=>o.ContractionMultipleLimit,
        RelativeCanonicalMultipliers=>o.RelativeCanonicalMultipliers,
        RelativeCanonicalMaxSteps=>o.RelativeCanonicalMaxSteps,
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
                "terminationType" => "Mori fibre space",
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
            RelativeCanonicalMaxSteps=>o.RelativeCanonicalMaxSteps,
            RelativeCanonicalVerbose=>o.RelativeCanonicalVerbose);
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

-- Proposition 3.8 for threefolds.  Run the two terminating searches in
-- parallel: global generation of a reflexive pluricanonical sheaf proves nef,
-- while failure of nefness for K_X+2^{-j}H proves non-nef.  NefSearchLimit is
-- an optional practical bound; null means the mathematical unbounded search.
canonicalNefData = method(Options => {NefSearchLimit => null})
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
    i := 1;
    while limit === null or i <= limit do (
        pluricanonical := i*a*K;
        if isBasePointFreeDivisor pluricanonical then
            return new HashTable from {
                "nef" => true,
                "conclusive" => true,
                "witnessType" => "base-point-free pluricanonical divisor",
                "iteration" => i,
                "witnessDivisor" => pluricanonical,
                "canonicalDivisor" => K,
                "ampleData" => ampleData
                };
        scaledData := canonicalScaledNefDataInternal(R,K,H,a,1/(2^i));
        if not scaledData#"nef" then
            return new HashTable from {
                "nef" => false,
                "conclusive" => true,
                "witnessType" => "non-nef positive perturbation",
                "iteration" => i,
                "witnessT" => 1/(2^i),
                "scaledTest" => scaledData,
                "canonicalDivisor" => K,
                "ampleData" => ampleData
                };
        i = i+1;
        );
    new HashTable from {
        "nef" => null,
        "conclusive" => false,
        "iterationsRun" => limit,
        "canonicalDivisor" => K,
        "ampleData" => ampleData,
        "warning" => "the optional search limit was reached"
        }
    )

isCanonicalNef = method(Options => options canonicalNefData)
isCanonicalNef (Ring,ZZ) := o -> (R,a) -> (
    result := canonicalNefData(R,a,NefSearchLimit=>o.NefSearchLimit);
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
      dimension three}.  The first implemented stage is the canonical-divisor
      nefness test of Proposition 3.8.

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

Node
  Key
    threefoldMMPData
    (threefoldMMPData,Ring,ZZ)
    (threefoldMMPData,Ring,ZZ,List)
  Headline
    run the three-dimensional minimal model program
  Usage
    result = threefoldMMPData(R,a)
    result = threefoldMMPData(R,a,steps)
  Description
    Text
      Starting with a positive Cartier index multiple for $K_X$, iterate the
      nefness, threshold, contraction, relative-model, smallness, and index
      computations.  Return the graph-preserving step sequence and stop at a
      minimal model or a Mori fibre space.  The three-argument form continues
      from a current model while retaining certified preceding nonterminal
      step records; the last record must lead to the supplied current ring.

Node
  Key
    canonicalIndexData
    (canonicalIndexData,Ring)
  Headline
    find the Cartier index of the canonical divisor
  Usage
    result = canonicalIndexData R

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
      constructed as a Rees Proj, substitute the Rees-ideal generators for the
      fibre variables in the Segre coordinates.  The result records homogeneous
      coordinates for $W \dashrightarrow Z$, verifies the model and graph
      equations, and certifies that their base locus is the Rees centre after
      saturation.  Skew weighted fibre coordinates use the positive diagonal
      selected by @TO b2mDiagonalData@.
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

Node
  Key
    contractionSmallnessData
    (contractionSmallnessData,HashTable)
  Headline
    test smallness of a computed birational contraction
  Usage
    result = contractionSmallnessData contraction
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
      canonical algebra computation and return its graph morphism.

Node
  Key
    relativeCanonicalModelData
    (relativeCanonicalModelData,HashTable)
  Headline
    compute the next model from a birational contraction result
  Usage
    result = relativeCanonicalModelData contraction
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

Node
  Key
    completeLinearSystemGraphData
    (completeLinearSystemGraphData,BasicDivisor)
  Headline
    construct the graph of a complete base-point-free linear system
  Usage
    graphData = completeLinearSystemGraphData D

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
      Find a base-point-free multiple of $K_X+lambda H$, construct its
      complete-linear-system graph, and compute its Stein factorization.  The
      function tests small multiples first and is guaranteed to stop at the
      effective multiplier from the scaled nefness theorem.

Node
  Key
    canonicalContractionData
    (canonicalContractionData,Ring,ZZ)
  Headline
    compute the canonical nef threshold and its extremal-face contraction
  Usage
    result = canonicalContractionData(R,a)
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
  Description
    Text
      Assuming that $K_X$ is not nef, compute the first positive rational
      $t$ for which $K_X+tH$ is nef.  The function implements Algorithm 1:
      dyadic searches bracket the threshold and the rationality theorem gives
      a finite candidate list.  The ample Cartier divisor $H$ is the one
      returned by {tt weightedAmpleDivisorData}.
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
      the Boolean answer and the base-point-free or non-nef witness
  Description
    Text
      The function alternates the two searches in Proposition 3.8.  It tests
      reflexive pluricanonical divisors for base-point-freeness and tests the
      positive perturbations $K_X+2^{-j}H$ by the effective multiplier of
      Proposition 3.1.  The hypotheses that $X$ is normal and log terminal are
      mathematical input requirements and are not certified by this function.
    Example
      R = QQ[x_0..x_3];
      canonicalNefData(R,1)
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
  SeeAlso
    effectiveNefMultiplier
    weightedAmpleDivisorData

Node
  Key
    weightedAmpleDivisorData
    (weightedAmpleDivisorData,Ring)
  Headline
    construct the ample Cartier divisor from the coordinate weights
  Usage
    data = weightedAmpleDivisorData R

Node
  Key
    effectiveNefMultiplier
    (effectiveNefMultiplier,ZZ,ZZ)
  Headline
    compute the effective base-point-free multiplier
  Usage
    m = effectiveNefMultiplier(d,N)

Node
  Key
    isBasePointFreeDivisor
    (isBasePointFreeDivisor,BasicDivisor)
  Headline
    test whether a complete divisor linear system is base-point-free
  Usage
    answer = isBasePointFreeDivisor D

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
    RelativeCanonicalMaxSteps
  Headline
    maximum factorial schedule depth for relative canonical models

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
