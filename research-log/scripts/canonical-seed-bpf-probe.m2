needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

canonicalSeed = R -> (
    S := ambient R;
    degs := apply(flatten entries vars S,q -> degree q);
    print("ambient degree sum=" | toString sum degs);
    omega := (Ext^(dim S-dim R)(S^1/(ideal R),S^{-(sum degs)})) ** R;
    Hmod := Hom(omega,R^1);
    if numgens Hmod == 0 then return null;
    e := (degrees Hmod)#0;
    phi := homomorphism Hmod_0;
    I := trim ideal matrix phi;
    if I == ideal 0_R then return null;
    new HashTable from {"ideal"=>I,"embeddingDegree"=>e}
    );

basePointFreeAtDegree = (M,d,B) -> (
    R := ring M;
    ev := coker basis(d,M);
    trim saturate(ann ev,B) == ideal 1_R
    );

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2-y1^2+2*y0*y1-y2^2+y1*y2;
Fcubic = y0^3+2*y0^2*y1-y1^2*y2+y2^3-y0*y1*y2;
Fquartic = y0^4-y1^4+2*y0^2*y1^2+y1^3*y2-y2^4+y0*y1*y2^2;
F = x^2*Fquad+x*(u0+2*u1)*Fcubic+(u0^2+u0*u1+2*u1^2)*Fquartic;
R = A/F;
blockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
B = (blockDataFn R)#"irrelevantIdeal";
seed = canonicalSeed R;
print("seed ideal=" | toString seed#"ideal");
print("seed embedding degree=" | toString seed#"embeddingDegree");
scan(1..7,m -> (
    I = reflexivePower(2*m,seed#"ideal");
    M = (I*R^1) ** R^{2*m*(seed#"embeddingDegree") + m*{1,1}};
    bpf = basePointFreeAtDegree(M,toList(degreeLength R:0),B);
    print("m=" | toString m | " module degrees=" | toString degrees M | " BPF=" | toString bpf);
    ));
