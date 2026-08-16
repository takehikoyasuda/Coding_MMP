-- Experimental probe: compare WeilDivisors' double-dual construction
-- with the direct divisorial-ideal Hom(I_{D+}, I_{D-}) construction.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2 - y1^2 + 2*y0*y1 - y2^2 + y1*y2;
Fcubic = y0^3 + 2*y0^2*y1 - y1^2*y2 + y2^3 - y0*y1*y2;
Fquartic = y0^4 - y1^4 + 2*y0^2*y1^2 + y1^3*y2 - y2^4 + y0*y1*y2^2;
F = (x^2*Fquad + x*(u0+2*u1)*Fcubic + (u0^2+u0*u1+2*u1^2)*Fquartic);
R = A/F;
multigradedBlockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
B = (multigradedBlockDataFn R)#"irrelevantIdeal";
K = canonicalDivisor(R,IsGraded=>true);
H = divisor(u0) + divisor(x);
D = 2*(2*K + H);
stamp("D constructed");

-- In this toric Cox presentation D has class (-2,2), so the invertible
-- sheaf is represented by the free shifted module R^{{2,-2}}.  This is the
-- candidate that avoids every Hom/dual operation; it is only valid when the
-- divisor class/trivialization has been certified.
shifted = R^{{2,-2}};
zeroDegree = toList(degreeLength R : 0);
shiftedBasis = basis(zeroDegree,shifted);
shiftedBase = trim saturate(ann coker shiftedBasis,B);
print("shifted degree=" | toString degrees shifted);
print("shifted BPF=" | toString(shiftedBase == ideal(1_R)));
stamp("shifted BPF assessed");

E = positivePart D;
Fneg = negativePart D;
E1 = apply(getPrimeCount(E), i -> idealPower((coefficients E)#i,(primes E)#i));
F1 = apply(getPrimeCount(Fneg), i -> idealPower((coefficients Fneg)#i,(primes Fneg)#i));
prodE = if #E1 != 0 then product E1 else ideal(sub(1,R));
prodF = if #F1 != 0 then product F1 else ideal(sub(1,R));
stamp("prodE,prodF constructed");

direct = Hom(prodE,prodF);
stamp("direct Hom(prodE,prodF) constructed");
zeroDegree = toList(degreeLength R : 0);
directBasis = basis(zeroDegree,direct);
directBase = trim saturate(ann coker directBasis,B);
print("direct degree=" | toString degrees direct);
print("direct BPF=" | toString(directBase == ideal(1_R)));
stamp("direct BPF assessed");

-- Keep the reference construction last: it is intentionally expensive.
referenceDual = (prodE*R^1) ** Hom(prodF*R^1,R^1);
stamp("reference intermediate dual constructed");
reference = Hom(referenceDual,R^1);
stamp("reference double dual constructed");
referenceBasis = basis(zeroDegree,reference);
referenceBase = trim saturate(ann coker referenceBasis,B);
print("reference degree=" | toString degrees reference);
print("reference BPF=" | toString(referenceBase == ideal(1_R)));
print("same base ideal=" | toString(directBase == referenceBase));
stamp("reference BPF assessed");
