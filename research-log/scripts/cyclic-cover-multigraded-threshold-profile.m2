-- Diagnostic: canonicalNefThresholdData(Xnatural,2,Hnatural,IrrelevantIdeal=>
-- Bnatural) ran past 75 minutes cpu / 5.1GB before being killed, even though
-- the single canonicalNefData call on the same data completed in ~3.3s.
-- canonicalNefThresholdDataCore's beta-doubling search calls
-- canonicalScaledNefDataInternal(R,K,H,a,t,B,null) for t=1,2,4,8,... until it
-- finds a nef witness.  This script replicates that sequence one t at a time,
-- with its own stamps, to find exactly which t is expensive.
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
stamp("cyclic-cover base");

Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase);
antiProjection = bigradedReesProjection antiIdeal;
Xnatural = antiProjection#totalRing;
Bnatural = sub(antiProjection#irrelevantIdeal,Xnatural);
usNatural = apply(antiProjection#fiberVariables, u -> sub(u,Xnatural));
xsNatural = apply(antiProjection#baseVariables, x -> sub(x,Xnatural));
Hnatural = divisor(usNatural#0) + divisor(xsNatural#0);
stamp("Xnatural/Bnatural/Hnatural assembled");

Knat = canonicalDivisor(Xnatural,IsGraded=>true);
print("Knat=" | toString Knat);
print("Hnatural=" | toString Hnatural);

-- Sanity: which fastpath hypotheses does each of Knat/Hnatural satisfy?
principalShiftCartierCertificateInternalFn = value(
    MMPComputation#"private dictionary"#"principalShiftCartierCertificateInternal");
print("principal-shift(Knat)=" | toString principalShiftCartierCertificateInternalFn Knat);
print("principal-shift(Hnatural)=" | toString principalShiftCartierCertificateInternalFn Hnatural);
stamp("fastpath hypothesis check");

scan({1,2,4,8,16}, t -> (
    t0 := cpuTime();
    result := canonicalScaledNefData(Xnatural,2,t,Hnatural,IrrelevantIdeal=>Bnatural);
    elapsed := cpuTime() - t0;
    print("t=" | toString t | " nef=" | toString result#"nef"
        | " multipliersTested=" | toString result#"multipliersTested"
        | " elapsed=" | toString elapsed);
    stamp("t=" | toString t | " done");
    ));
flush stdio;
