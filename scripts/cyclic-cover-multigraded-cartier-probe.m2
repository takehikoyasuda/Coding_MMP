-- Measured (2026-08-15): isCartierSaturatedInternal(2*Knat,Bnatural) alone
-- completes in ~0.2 cpu seconds (2*Knat is Cartier=true), ruling out the
-- Cartier gate as the cost driver in canonicalNefData's slow behaviour on
-- this ring; see cyclic-cover-multigraded-driver-probe.m2 for context.
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
stamp("setup complete");

Knat = canonicalDivisor(Xnatural,IsGraded=>true);
stamp("canonicalDivisor(Xnatural) computed");

twoK = 2*Knat;
stamp("2*Knat formed");

mmpPkg = needsPackage "MMPComputation";
isCartierSaturatedInternal = value(
    mmpPkg#"private dictionary"#"isCartierSaturatedInternal");
stamp("isCartierSaturatedInternal fetched");

cartierResult = isCartierSaturatedInternal(twoK,Bnatural);
stamp("isCartierSaturatedInternal(2*Knat,Bnatural) computed");
print("2*Knat Cartier (saturated w.r.t. Bnatural)=" | toString cartierResult);
