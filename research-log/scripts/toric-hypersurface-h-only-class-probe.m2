-- Measure the intermediate strategy: keep K general, but apply H as a
-- graded shift after constructing the K-part module.
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
divisorToModuleFn = value(WeilDivisors#"private dictionary"#"divisorToModule");
zeroDegree = toList(degreeLength R : 0);

scan(1..6,m -> (
    Kmodule = divisorToModuleFn(m*2*K);
    Hshift = R^{{m,m}}; -- O(mH), with deg(H)=(1,1)
    candidateModule = Kmodule ** Hshift;
    J = trim saturate(ann coker basis(zeroDegree,candidateModule),B);
    print("m="|toString m|" BPF="|toString(J == ideal(1_R)));
    ));
stamp("H-only class-degree sweep completed");
