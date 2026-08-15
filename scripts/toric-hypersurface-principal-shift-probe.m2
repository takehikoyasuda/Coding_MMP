-- Validate the no-Hom path for the toric hypersurface candidate.
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
L = 2*K + H;
print("K=" | toString K);
print("K primes=" | toString primes K);
print("K coefficients=" | toString coefficients K);
print("L=" | toString L);
print("L primes=" | toString primes L);
print("L coefficients=" | toString coefficients L);
Lpos = positivePart L;
Lneg = negativePart L;
LposIdeal = product apply(getPrimeCount(Lpos), i -> idealPower((coefficients Lpos)#i,(primes Lpos)#i));
LnegIdeal = product apply(getPrimeCount(Lneg), i -> idealPower((coefficients Lneg)#i,(primes Lneg)#i));
print("Lpos ideal=" | toString trim LposIdeal);
print("Lneg ideal=" | toString trim LnegIdeal);
zeroDegree = toList(degreeLength R : 0);

-- The support is {divisor(u0), divisor(x)} with coefficients {-1,1};
-- degree(L)=(-1,1), and OO(mL) is R^{m*degree(L)}.
deltaL = {-1,1};
scan(1..7,m -> (
    M = R^{m*deltaL};
    J = trim saturate(ann coker basis(zeroDegree,M),B);
    print("m="|toString m|" moduleDegrees="|toString degrees M|" BPF="|toString(J == ideal(1_R)));
    ));
stamp("all shifted BPF tests completed");
