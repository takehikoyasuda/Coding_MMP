-- Measured (2026-08-15): traces negativeCurveWitnessData's internals for
-- L=4K+2H on the cyclic-cover natural presentation.  Only one curve is found
-- in the base locus, Q=ideal(y_5,y_4,y_2,y_1,u_1); the Hilbert-function
-- difference is -1, 29, 13, 13, 13, ... for n=1..8, stabilizing at +13 (not
-- a negative witness).  Companion to -negcurve-probe.m2.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
branch = sum apply(coverVars,q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));

Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase);
antiProjection = bigradedReesProjection antiIdeal;
Xnatural = antiProjection#totalRing;
Bnatural = sub(antiProjection#irrelevantIdeal,Xnatural);
usNatural = apply(antiProjection#fiberVariables, u -> sub(u,Xnatural));
xsNatural = apply(antiProjection#baseVariables, x -> sub(x,Xnatural));
Hnatural = divisor(usNatural#0) + divisor(xsNatural#0);
Knat = canonicalDivisor(Xnatural,IsGraded=>true);
r = degreeLength Xnatural;
hVec = (degree usNatural#0) + (degree xsNatural#0);
stamp("setup complete");

weilDivisorsPkg = needsPackage "WeilDivisors";
weilDivisorToModule = value(
    weilDivisorsPkg#"private dictionary"#"divisorToModule");
zeroDegree = toList(r : 0);

Lnat = 4*Knat + 2*Hnatural;
candidateBaseLocus = trim ann coker basis(zeroDegree,weilDivisorToModule Lnat);
stamp("candidateBaseLocus computed");
print("candidateBaseLocus=" | toString candidateBaseLocus);

projectiveBaseLocus = trim saturate(candidateBaseLocus,Bnatural);
stamp("projectiveBaseLocus computed");
print("projectiveBaseLocus=" | toString projectiveBaseLocus);

comps = minimalPrimes projectiveBaseLocus;
stamp("minimalPrimes computed");
print("#comps=" | toString(#comps));
scan(comps, P -> print("dim(R/P)-r=" | toString(dim(Xnatural/P)-r)));

coordinates = flatten entries vars Xnatural;
pieces = comps;
iterCount = 0;
while any(pieces, Q -> dim(Xnatural/Q)-r > 1) and iterCount < 6 do (
    iterCount = iterCount+1;
    nextPieces = {};
    scan(pieces, Q -> (
        cd := dim(Xnatural/Q)-r;
        if cd <= 1 then nextPieces = append(nextPieces,Q)
        else (
            candidates := select(coordinates, x -> x % Q != 0);
            cutIdeal = null;
            scan(candidates, x -> if cutIdeal === null then (
                cand := trim saturate(Q+ideal x,Bnatural);
                if cand != ideal 1_Xnatural then cutIdeal = cand;
                ));
            if cutIdeal =!= null then
                nextPieces = join(nextPieces, minimalPrimes cutIdeal);
            );
        ));
    pieces = unique nextPieces;
    stamp("cutting iteration " | toString iterCount | " done, #pieces=" | toString(#pieces));
    );
print("final #pieces=" | toString(#pieces));
scan(pieces, Q -> print("dim(R/Q)-r=" | toString(dim(Xnatural/Q)-r)));

curves = select(pieces, Q -> dim(Xnatural/Q)-r == 1);
print("#curves=" | toString(#curves));
stamp("curves identified");

DModule = weilDivisorToModule Lnat;
scan(curves, Q -> (
    curveModule := coker gens Q;
    restriction := DModule ** curveModule;
    scan(1..8, n -> (
        d0 := hilbertFunction(n*hVec,curveModule);
        d1 := hilbertFunction(n*hVec,restriction);
        print("Q=" | toString Q | " n=" | toString n | " diff=" | toString(d1-d0));
        ));
    stamp("curve Hilbert-function scan done");
    ));
