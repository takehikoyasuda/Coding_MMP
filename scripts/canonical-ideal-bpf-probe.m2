needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("FlipComputation",FileName=>"third_party/flip-computation/FlipComputation.m2");
needsPackage("WeilDivisors");

R = QQ[x0,x1,x2,x3];
K = canonicalDivisor(R,IsGraded=>true);
I = canonicalIdeal R;
print("P3 K=" | toString K);
print("canonicalIdeal=" | toString I);
print("degrees I=" | toString degrees I);
print("degrees R^{{4}}=" | toString degrees R^{{4}});
print("degrees R^{{-4}}=" | toString degrees R^{{-4}});
print("degrees OO(K)=" | toString degrees OO(K));
print("degrees K+4H=" | toString degrees OO(K+4*divisor(x0)));
print("bpf OO(K+4H)=" | toString isBasePointFreeDivisor(K+4*divisor(x0)));

Q = QQ[y0,y1,y2,y3,y4]/ideal(y0^5+y1^5+y2^5+y3^5+y4^5);
IQ = canonicalIdeal Q;
print("quintic canonicalIdeal=" | toString IQ);
print("quintic degrees I=" | toString degrees IQ);
print("quintic degrees OO(K)=" | toString degrees OO(canonicalDivisor(Q,IsGraded=>true)));
print("quintic bpf K=" | toString isBasePointFreeDivisor(canonicalDivisor(Q,IsGraded=>true)));

assert(isBasePointFreeDivisor(canonicalDivisor(Q,IsGraded=>true)));

-- Repeat the canonical-ideal construction on the non-Gorenstein cyclic cover.
rayList = {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB,h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
W = T/(sub(I0,T)+ideal(c^4-sum apply(coverVars,q -> q^4)));
IW = canonicalIdeal W;
print("cyclic cover canonicalIdeal=" | toString IW);
print("cyclic cover degrees I=" | toString degrees IW);
print("cyclic cover K=" | toString canonicalDivisor(W,IsGraded=>true));

S = ambient W;
dl = apply(flatten entries vars S,q -> degree q);
om = (Ext^(dim S-dim W)(S^1/(ideal W),S^{-sum dl})) ** W;
Hmod = Hom(om,W^1);
hhdeg = apply(numgens Hmod,i -> (degrees Hmod)#i);
print("H degrees=" | toString hhdeg);
hi = Hmod_(minPosition apply(hhdeg,d -> first d));
phi = homomorphism hi;
print("selected H element=" | toString hi);
print("source phi=" | toString source phi);
print("target phi=" | toString target phi);
print("phi matrix=" | toString matrix phi);
