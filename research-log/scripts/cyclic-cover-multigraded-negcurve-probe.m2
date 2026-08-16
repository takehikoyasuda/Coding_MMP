-- Measured (2026-08-15): the new negativeCurveWitnessData (Phase 4 idea A,
-- docs/ITERATED-MULTIGRADING-MMP-PLAN.md) applied to the m=1 candidate
-- divisor L=4K+2H completes in ~95 cpu seconds total (candidateBaseLocus's
-- weilDivisorToModule construction dominates at ~90s, the curve search and
-- Hilbert-function scan itself is fast).  The one curve found gives
-- intersection +13 (not negative), so witness=null: correctly inconclusive
-- for this m, not a bug -- see -negcurve-diag.m2 for the full trace.
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
stamp("setup complete");

weilDivisorsPkg = needsPackage "WeilDivisors";
weilDivisorToModule = value(
    weilDivisorsPkg#"private dictionary"#"divisorToModule");
zeroDegree = toList(degreeLength Xnatural : 0);
hVec = (degree usNatural#0) + (degree xsNatural#0);
print("hVec=" | toString hVec);

-- Mirrors canonicalScaledNefDataInternal's own first candidate: a=2, i=1,
-- t=1/2 (p=1,q=2) gives L = q*a*K + a*p*H = 4K + 2H.
Lnat = 4*Knat + 2*Hnatural;
stamp("Lnat formed");

candidateBaseLocus = trim ann coker basis(zeroDegree,weilDivisorToModule Lnat);
stamp("candidateBaseLocus computed");
print("numgens candidateBaseLocus=" | toString numgens candidateBaseLocus);

witness = negativeCurveWitnessData(Lnat,candidateBaseLocus,Bnatural,hVec);
stamp("negativeCurveWitnessData computed");
print("witness=" | toString witness);
