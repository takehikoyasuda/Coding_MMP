-- Phase E follow-up (docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md section 10.3):
-- negativeCurveWitnessData(K,...) directly on the bare canonical divisor was
-- cheap (~1.1 cpu s) but uninformative -- K = -divisor(u0) has trivially
-- structured sections (a single height-one prime), so its candidateBaseLocus
-- came back with codim 0 and the witness search short-circuited to null
-- (inconclusive, not "nef") before ever searching a curve.
--
-- canonicalNefDataCore's real first non-trivial test (i=1) is
-- canonicalScaledNefDataInternal(R,K,H,1,1/2,B), whose L = 2*a*K + a*1*H =
-- 2K+H combines TWO distinct prime divisors ((u0) with coefficient -1, (x)
-- with coefficient +1) -- structurally like the cyclic-cover example's L
-- values, not like bare K.  Because geometricDimension=3 here,
-- canonicalScaledNefDataInternal's negative-curve shortcut is dead code
-- (trialBound==guaranteedMultiplier always for d=3, confirmed by reading
-- MMPComputation.m2 lines 600-612), so it always calls the expensive
-- isBasePointFreeDivisor(m*L,B) for m=1,2,... up to guaranteedMultiplier --
-- never the cheaper negativeCurveWitnessData path.  This script reproduces
-- that exact sweep with per-m timing stamps, to see which m (if any)
-- actually completes before the cost blows up, mirroring
-- cyclic-cover-multigraded-bpf-probe.m2 / -scalednef-probe.m2.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2 - y1^2 + 2*y0*y1 - y2^2 + y1*y2;
Fcubic = y0^3 + 2*y0^2*y1 - y1^2*y2 + y2^3 - y0*y1*y2;
Fquartic = y0^4 - y1^4 + 2*y0^2*y1^2 + y1^3*y2 - y2^4 + y0*y1*y2^2;
F = (x^2*Fquad + x*(u0+2*u1)*Fcubic + (u0^2+u0*u1+2*u1^2)*Fquartic);
R = A/F;
stamp("R constructed");

multigradedBlockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
blockData = multigradedBlockDataFn R;
B = blockData#"irrelevantIdeal";
d = blockData#"geometricDimension";
print("d=" | toString d);
stamp("B computed");

K = canonicalDivisor(R,IsGraded=>true);
H = divisor(u0) + divisor(x);
stamp("K, H constructed");

-- i=1 pluricanonical check first (a=1, so pluricanonical = K itself).
bpfK = isBasePointFreeDivisor(K,B);
print("isBasePointFreeDivisor(K,B)=" | toString bpfK);
stamp("isBasePointFreeDivisor(K,B) done");

-- canonicalScaledNefDataInternal(R,K,H,a=1,t=1/2,B): p=1,q=2,
-- L = q*a*K + a*p*H = 2K+H.
L = 2*K + H;
print("L=2K+H degree computed");
stamp("L constructed");

N = 1*2;  -- a*q
guaranteedMultiplier = effectiveNefMultiplier(d,N);
print("guaranteedMultiplier=" | toString guaranteedMultiplier);
stamp("guaranteedMultiplier computed");

m = 1;
found = false;
while m <= guaranteedMultiplier and not found do (
    print("testing m=" | toString m | " ...");
    flush stdio;
    candidateDivisor := m*L;
    bpfM := isBasePointFreeDivisor(candidateDivisor,B);
    stamp("m=" | toString m | " isBasePointFreeDivisor done, result=" | toString bpfM);
    if bpfM then found = true;
    m = m+1;
    );
print("sweep finished, found=" | toString found);
