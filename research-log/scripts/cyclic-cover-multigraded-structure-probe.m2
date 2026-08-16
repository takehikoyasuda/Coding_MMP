-- Measured (2026-08-15): cheap (~1.2 cpu seconds) structural characterization
-- of the natural bigraded Rees presentation of X- (before b2mToGraphMorphism's
-- flattening to 35 variables): 9 ambient variables (2 fiber, 7 base),
-- degreeLength 2.  Confirms construction itself is not the bottleneck; see
-- cyclic-cover-multigraded-driver-probe.m2 for where the cost actually is.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
print("#HB=" | toString(#HB));
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));

T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
branch = sum apply(coverVars,q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));
stamp("Wcover");
print("numgens ambient Wcover=" | toString numgens ambient Wcover);

Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase);
stamp("antiIdeal");
print("numgens antiIdeal (trimmed)=" | toString numgens trim antiIdeal);
print("degrees of trimmed antiIdeal gens=" | toString (flatten degrees trim antiIdeal));

antiProjection = bigradedReesProjection antiIdeal;
stamp("antiProjection");
print("#fiberVariables=" | toString(#(antiProjection#fiberVariables)));
print("#baseVariables=" | toString(#(antiProjection#baseVariables)));

Abig = antiProjection#ambientRing;
print("degrees of Abig gens=" | toString (degrees Abig));
IZ = antiProjection#definingIdeal;
stamp("definingIdeal accessed");
print("numgens IZ (ungenerated count, just listing)=" | toString numgens IZ);
stamp("numgens IZ printed");

Xnatural = antiProjection#totalRing;
stamp("Xnatural = totalRing");
print("numgens ambient Xnatural=" | toString numgens ambient Xnatural);
print("degrees ambient Xnatural=" | toString degrees ambient Xnatural);

irr = antiProjection#irrelevantIdeal;
stamp("irrelevantIdeal accessed");
print("numgens irrelevantIdeal (in Abig)=" | toString numgens irr);
print("degrees of irrelevantIdeal gens=" | toString flatten degrees irr);
