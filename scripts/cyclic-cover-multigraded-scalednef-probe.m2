-- Measured (2026-08-15): this single call (a=2, i=1, t=1/2, mirroring
-- canonicalScaledNefDataInternal's own first invocation inside
-- canonicalNefDataCore) did not return within 15 cpu minutes, confirming this
-- is where canonicalNefData's cost on the natural bigraded presentation
-- actually concentrates (contrast with -cartier-probe.m2 and -bpf-probe.m2,
-- both of which complete in under a second on the same ring).
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

mmpPkg = needsPackage "MMPComputation";
canonicalScaledNefDataInternal = value(
    mmpPkg#"private dictionary"#"canonicalScaledNefDataInternal");
stamp("canonicalScaledNefDataInternal fetched");

-- Mirrors canonicalNefDataCore's own first call: a=2, i=1, t=1/2.
scaled = canonicalScaledNefDataInternal(Xnatural,Knat,Hnatural,2,1/2,Bnatural);
stamp("canonicalScaledNefDataInternal(Xnatural,Knat,Hnatural,2,1/2,Bnatural) computed");
print("scaled nef=" | toString scaled#"nef");
