-- Phase E follow-up (docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md section 10.5):
-- root-cause WHERE inside isBasePointFreeDivisorInternal/divisorToModule the
-- m=2 cost (~69s, vs m=1's ~0.09s) actually goes, by reimplementing both
-- functions' steps inline with a cpuTime() stamp between every step.
-- divisorToModule's own source (WeilDivisors.m2 lines 832-861) is:
--   E = positivePart D, F = negativePart D
--   E1 = idealPower per prime of E, F1 = idealPower per prime of F
--   prodE = product E1, prodF = product F1
--   dual = (prodE*R^1) ** Hom(prodF*R^1, R^1)
--   M = Hom(dual, R^1)                          <- final reflexive hull
-- isBasePointFreeDivisorInternal then does:
--   basis(zeroDegree, M) -> coker -> ann -> saturate(_, B)
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
stamp("B computed");

K = canonicalDivisor(R,IsGraded=>true);
H = divisor(u0) + divisor(x);
L = 2*K + H;
D = 2*L;  -- m=2, the candidate that took ~69s as a whole in the earlier sweep.
stamp("D=2L constructed");

-- positivePart, negativePart, idealPower, getPrimeCount, coefficients, primes
-- are all exported by WeilDivisors, so no private-dictionary access needed.
E = positivePart D;
Fneg = negativePart D;
stamp("positivePart/negativePart computed");

print("getPrimeCount E=" | toString getPrimeCount E);
print("getPrimeCount Fneg=" | toString getPrimeCount Fneg);
print("coefficients E=" | toString coefficients E);
print("coefficients Fneg=" | toString coefficients Fneg);
scan(getPrimeCount E, i -> print("prime E#"|toString i|" numgens="|toString numgens trim (primes E)#i|" codim="|toString codim (primes E)#i));
scan(getPrimeCount Fneg, i -> print("prime F#"|toString i|" numgens="|toString numgens trim (primes Fneg)#i|" codim="|toString codim (primes Fneg)#i));
stamp("prime structure of E,Fneg inspected");

E1 = apply(getPrimeCount E, i -> idealPower((coefficients E)#i,(primes E)#i));
F1 = apply(getPrimeCount Fneg, i -> idealPower((coefficients Fneg)#i,(primes Fneg)#i));
stamp("idealPower lists (E1,F1) computed");

prodE = if #E1 != 0 then product E1 else ideal(sub(1,R));
prodF = if #F1 != 0 then product F1 else ideal(sub(1,R));
print("numgens trim prodE=" | toString numgens trim prodE);
print("numgens trim prodF=" | toString numgens trim prodF);
stamp("prodE, prodF computed");

homF = Hom(prodF*R^1, R^1);
stamp("Hom(prodF*R^1,R^1) computed  <-- first Hom (inverse of negative part)");

dualModule = (prodE*R^1) ** homF;
stamp("tensor product (dualModule) computed");

M = Hom(dualModule, R^1);
stamp("Hom(dualModule,R^1) computed  <-- final reflexive hull (double dual)");

zeroDegree = toList(degreeLength R : 0);
basisM = basis(zeroDegree,M);
stamp("basis(zeroDegree,M) computed");

evalCoker = coker basisM;
stamp("coker computed");

annCoker = ann evalCoker;
stamp("ann computed");

satAnn = saturate(annCoker,B);
stamp("saturate computed");

print("BPF result=" | toString(trim satAnn == ideal 1_R));
