-- Measured (2026-08-15): isBasePointFreeDivisor(2K,Bnatural) alone completes
-- in ~0.3 cpu seconds (2K is not base-point-free, as expected).  Rules out a
-- single BPF check as the cost driver; the actual bottleneck is the sweep of
-- up to 6 such checks inside canonicalScaledNefDataInternal -- see
-- -scalednef-probe.m2 and cyclic-cover-multigraded-driver-probe.m2.
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
Knat = canonicalDivisor(Xnatural,IsGraded=>true);
stamp("setup complete, Knat computed");

twoK = 2*Knat;
bpf2K = isBasePointFreeDivisor(twoK,Bnatural);
stamp("isBasePointFreeDivisor(2K,Bnatural) computed");
print("2K is base-point-free (w.r.t. Bnatural)=" | toString bpf2K);
