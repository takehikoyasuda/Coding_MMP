-- End-to-end probe for the certified divisor-class-degree fast path.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");
stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2 - y1^2 + 2*y0*y1 - y2^2 + y1*y2;
Fcubic = y0^3 + 2*y0^2*y1 - y1^2*y2 + y2^3 - y0*y1*y2;
Fquartic = y0^4 - y1^4 + 2*y0^2*y1^2 + y1^3*y2 - y2^4 + y0*y1*y2^2;
F = (x^2*Fquad + x*(u0+2*u1)*Fcubic + (u0^2+u0*u1+2*u1^2)*Fquartic);
R = A/F;
blockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
B = (blockDataFn R)#"irrelevantIdeal";
K = canonicalDivisor(R,IsGraded=>true);
H = divisor(u0) + divisor(x);
stamp("input constructed");

result = canonicalNefData(R,1,H,
    IrrelevantIdeal=>B,
    DivisorClassDegrees=>{{-1,0},{1,1}});
print("conclusive=" | toString result#"conclusive");
print("nef=" | toString result#"nef");
print("keys=" | toString keys result);
stamp("class-degree canonicalNefData completed");
