-- Regression for the canonicalIndexData Cartier fastpath (memory
-- hom-fastpath-scope-excludes-iscartier): canonicalIdealSeedInvertibleInternal
-- and principalShiftCartierCertificateInternal should let canonicalIndexData
-- certify the known index without ever calling the expensive generic
-- isCartier/Hom(dualModule,R^1) path.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- Same rank-2 toric hypersurface as tests/canonical-seed-bpf-fastpath.m2 and
-- docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md; K_X=(-1,0) is already Cartier
-- there (index 1).
A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2-y1^2+2*y0*y1-y2^2+y1*y2;
Fcubic = y0^3+2*y0^2*y1-y1^2*y2+y2^3-y0*y1*y2;
Fquartic = y0^4-y1^4+2*y0^2*y1^2+y1^3*y2-y2^4+y0*y1*y2^2;
F = x^2*Fquad+x*(u0+2*u1)*Fcubic+(u0^2+u0*u1+2*u1^2)*Fquartic;
R = A/F;
K = canonicalDivisor(R,IsGraded=>true);

principalShiftCartierCertificateInternalFn = value(
    MMPComputation#"private dictionary"#"principalShiftCartierCertificateInternal");
canonicalIdealSeedInvertibleInternalFn = value(
    MMPComputation#"private dictionary"#"canonicalIdealSeedInvertibleInternal");

-- On this particular ring K itself already happens to be visibly a sum of
-- homogeneous principal primes, so the cheapest certificate (path 1) already
-- fires; this is not the ring that motivated the seed-based certificate
-- (path 2) -- that was found on the Xminus ring in
-- scripts/cyclic-cover-raw-driver-probe.m2, whose 35-variable presentation
-- makes an isolated, minimal regression example impractical here. Both
-- certificates are exercised directly, independent of ordering:
assert(principalShiftCartierCertificateInternalFn K);
assert(canonicalIdealSeedInvertibleInternalFn(R,K,1) === true);

t0 = cpuTime();
indexData = canonicalIndexData R;
elapsed = cpuTime() - t0;
assert(indexData#"conclusive");
assert(indexData#"index" == 1);
print("canonicalIndexData(R) cpu=" | toString elapsed);
-- Generous bound: the old, unfixable-for-this-ring generic isCartier path
-- previously took well over a minute on structurally similar rings (see
-- hom-fastpath-scope-excludes-iscartier); the fastpath finishes in a couple
-- of seconds. 15s leaves comfortable headroom without asserting on it too
-- tightly.
assert(elapsed < 15);

-- IrrelevantIdeal option: purely additive, must not change the answer.
blockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
B = (blockDataFn R)#"irrelevantIdeal";
indexDataB = canonicalIndexData(R,IrrelevantIdeal=>B);
assert(indexDataB#"conclusive");
assert(indexDataB#"index" == 1);

print "OK canonicalIndexData Cartier fastpath: index certified without the generic isCartier/Hom double dual.";
