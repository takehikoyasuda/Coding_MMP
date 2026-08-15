-- End-to-end probe for the canonical-ideal/reflexive-power BPF path.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");
stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2-y1^2+2*y0*y1-y2^2+y1*y2;
Fcubic = y0^3+2*y0^2*y1-y1^2*y2+y2^3-y0*y1*y2;
Fquartic = y0^4-y1^4+2*y0^2*y1^2+y1^3*y2-y2^4+y0*y1*y2^2;
F = x^2*Fquad+x*(u0+2*u1)*Fcubic+(u0^2+u0*u1+2*u1^2)*Fquartic;
R = A/F;
blockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
B = (blockDataFn R)#"irrelevantIdeal";
K = canonicalDivisor(R,IsGraded=>true);
H = divisor(u0)+divisor(x);
private = MMPComputation#"private dictionary";
principalDegreeFn = value(private#"principalHomogeneousShiftDegreeInternal");
seedFn = value(private#"canonicalIdealSeedDataInternal");
print("H principal degree=" | toString principalDegreeFn H);
print("degrees OO(H)=" | toString degrees OO(H));
seed = seedFn(R,K);
print("seed available=" | toString(seed =!= null));
if seed =!= null then print("seed degree=" | toString seed#"embeddingDegree");
stamp("input constructed");

result = canonicalScaledNefData(R,1,1/2,H,IrrelevantIdeal=>B);
print("nef=" | toString result#"nef");
print("multipliers=" | toString result#"multipliersTested");
assert(result#"nef" == false);
assert(result#"multipliersTested" == {1,2,3,4,5,6});
fullResult = canonicalNefData(R,1,H,IrrelevantIdeal=>B);
print("full canonicalNefData nef=" | toString fullResult#"nef");
print("full canonicalNefData witness=" | toString fullResult#"witnessType");
assert(fullResult#"conclusive");
assert(fullResult#"nef" == false);
print("OK canonical ideal seed BPF path");
