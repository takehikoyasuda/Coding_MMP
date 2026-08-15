-- Phase E follow-up (docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md section 10.5):
-- isolate whether the ~59.5s Hom(dualModule,R^1) cost measured on the rank-2
-- multigraded presentation (scripts/toric-hypersurface-divisortomodule-
-- profile.m2) comes from the multigrading itself (rank 2) or from the
-- "combine three distinct height-one primes" structure regardless of
-- grading rank.
--
-- Construction: literally the same hypersurface equation, coefficient for
-- coefficient, but with variables renamed (v0,v1,vx,w0,w1,w2) and given a
-- SINGLE (rank-1) grading via the positive linear functional (a,b) |-> a+2b
-- applied to the original rank-2 degrees ((1,0)->1, (0,1)->2, (-1,1)->1).
-- This functional is chosen to keep every variable's degree positive (a
-- prerequisite the original degree map (a,b)|->a+b would have violated: it
-- sends the y-variables' degree (-1,1) to 0).  F is homogeneous of degree
-- (-2,4) under the original grading, hence automatically homogeneous of
-- degree (-2)+2*4=6 under this functional, so no new primality/homogeneity
-- check is needed -- it is forced by construction.
--
-- If Hom(dualModule2,R2^1) is comparably slow (~60s), the multigraded rank
-- is not the driver; if it is much faster, multigrading itself carries a
-- large overhead in Macaulay2's Hom/Ext machinery for this kind of module.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

A2 = QQ[v0,v1,vx,w0,w1,w2, Degrees=>{1,1,2,1,1,1}];
Fquad2 = 3*w0^2 - w1^2 + 2*w0*w1 - w2^2 + w1*w2;
Fcubic2 = w0^3 + 2*w0^2*w1 - w1^2*w2 + w2^3 - w0*w1*w2;
Fquartic2 = w0^4 - w1^4 + 2*w0^2*w1^2 + w1^3*w2 - w2^4 + w0*w1*w2^2;
F2 = (vx^2*Fquad2 + vx*(v0+2*v1)*Fcubic2 + (v0^2+v0*v1+2*v1^2)*Fquartic2);
print("degree F2=" | toString degree F2);
R2 = A2/F2;
stamp("R2 constructed (monograded)");

B2 = ideal(v0,v1) * ideal(vx,w0,w1,w2);
stamp("B2 (monograded irrelevant ideal) constructed");

K2 = canonicalDivisor(R2,IsGraded=>true);
print("K2=" | toString K2);
H2 = divisor(v0) + divisor(vx);
-- Note: WeilDivisor has no degree method (confirmed while writing
-- negativeCurveWitnessData; see MMPComputation.m2's comment on that
-- function), so H2's multidegree is not printed here.
L2 = 2*K2 + H2;
D2 = 2*L2;
stamp("K2, H2, D2=2L2 constructed");

E = positivePart D2;
Fneg = negativePart D2;
print("getPrimeCount E=" | toString getPrimeCount E);
print("getPrimeCount Fneg=" | toString getPrimeCount Fneg);
print("coefficients E=" | toString coefficients E);
print("coefficients Fneg=" | toString coefficients Fneg);
scan(getPrimeCount E, i -> print("prime E#"|toString i|" numgens="|toString numgens trim (primes E)#i|" codim="|toString codim (primes E)#i));
scan(getPrimeCount Fneg, i -> print("prime F#"|toString i|" numgens="|toString numgens trim (primes Fneg)#i|" codim="|toString codim (primes Fneg)#i));
stamp("prime structure of E,Fneg inspected (should match the rank-2 case: 2+1 primes)");

E1 = apply(getPrimeCount E, i -> idealPower((coefficients E)#i,(primes E)#i));
F1 = apply(getPrimeCount Fneg, i -> idealPower((coefficients Fneg)#i,(primes Fneg)#i));
prodE = if #E1 != 0 then product E1 else ideal(sub(1,R2));
prodF = if #F1 != 0 then product F1 else ideal(sub(1,R2));
print("numgens trim prodE=" | toString numgens trim prodE);
print("numgens trim prodF=" | toString numgens trim prodF);
stamp("prodE, prodF computed");

homF = Hom(prodF*R2^1, R2^1);
stamp("Hom(prodF*R2^1,R2^1) computed");

dualModule = (prodE*R2^1) ** homF;
stamp("tensor product (dualModule) computed");

M = Hom(dualModule, R2^1);
stamp("Hom(dualModule,R2^1) computed  <-- the comparison point: ~59.5s in rank 2");

zeroDegree2 = 0;
basisM = basis(zeroDegree2,M);
stamp("basis(0,M) computed");

evalCoker = coker basisM;
annCoker = ann evalCoker;
stamp("ann computed");

satAnn = saturate(annCoker,B2);
stamp("saturate computed");

print("BPF result=" | toString(trim satAnn == ideal 1_R2));
