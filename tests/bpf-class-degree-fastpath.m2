-- Regression for the certified divisor-class-degree BPF fast path.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2 - y1^2 + 2*y0*y1 - y2^2 + y1*y2;
Fcubic = y0^3 + 2*y0^2*y1 - y1^2*y2 + y2^3 - y0*y1*y2;
Fquartic = y0^4 - y1^4 + 2*y0^2*y1^2 + y1^3*y2 - y2^4 + y0*y1*y2^2;
F = (x^2*Fquad + x*(u0+2*u1)*Fcubic + (u0^2+u0*u1+2*u1^2)*Fquartic);
R = A/F;
blockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
B = (blockDataFn R)#"irrelevantIdeal";
H = divisor(u0) + divisor(x);

result = canonicalScaledNefData(R,1,1/2,H,
    IrrelevantIdeal=>B,
    DivisorClassDegrees=>{{-1,0},{1,1}});
assert(result#"nef" == false);
assert(result#"multipliersTested" == {1,2,3,4,5,6});
assert(result#"basePointFree" == false);
print("OK divisor-class-degree BPF fast path: scaled nef sweep completes without reflexive double dual");
