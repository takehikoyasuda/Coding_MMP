-- Test the (now least-degree-embedding-fixed) canonical-ideal-seed machinery
-- directly on Xnatural (the natural 9-variable bigraded presentation, codim
-- 4 -- NOT the 35-variable monograded flattening Xminus, codim 31, where the
-- same idea was already shown not to help).  Two cheap, isolated checks
-- before attempting the full threshold search again:
--   1. canonicalIdealSeedDataInternal(Xnatural,Knat) -- the Ext/Hom seed
--      construction itself, now with least-degree embedding selection.
--   2. cartierClassDegreeInternal(Hnatural) -- falls back to ONE
--      weilDivisorToModule(H) call (not per-multiplier) if H is not visibly
--      principal, which it is not here.
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
stamp("Wcover constructed");

Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase);
antiProjection = bigradedReesProjection antiIdeal;
Xnatural = antiProjection#totalRing;
Bnatural = sub(antiProjection#irrelevantIdeal,Xnatural);
usNatural = apply(antiProjection#fiberVariables, u -> sub(u,Xnatural));
xsNatural = apply(antiProjection#baseVariables, x -> sub(x,Xnatural));
Hnatural = divisor(usNatural#0) + divisor(xsNatural#0);
Knat = canonicalDivisor(Xnatural,IsGraded=>true);
stamp("Xnatural/Bnatural/Hnatural/Knat assembled");
print("dim Xnatural=" | toString dim Xnatural | " dim ambient=" | toString dim ambient Xnatural
    | " codim=" | toString (dim ambient Xnatural - dim Xnatural));

canonicalIdealSeedDataInternalFn = value(
    MMPComputation#"private dictionary"#"canonicalIdealSeedDataInternal");
cartierClassDegreeInternalFn = value(
    MMPComputation#"private dictionary"#"cartierClassDegreeInternal");

t0 = cpuTime();
seed = canonicalIdealSeedDataInternalFn(Xnatural,Knat);
t1 = cpuTime();
print("seed === null: " | toString (seed === null));
if seed =!= null then (
    print("seed#ideal numgens (untrimmed input) = " | toString numgens seed#"ideal");
    print("seed#embeddingDegree = " | toString seed#"embeddingDegree");
    );
print("canonicalIdealSeedDataInternal(Xnatural,Knat) elapsed=" | toString (t1-t0));
stamp("seed computed");

t2 = cpuTime();
hDeg = cartierClassDegreeInternalFn Hnatural;
t3 = cpuTime();
print("cartierClassDegreeInternal(Hnatural) = " | toString hDeg
    | " elapsed=" | toString (t3-t2));
stamp("H class degree computed");
flush stdio;
