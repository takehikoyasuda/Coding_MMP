-- First chartwise differential-form probe on the cyclic-cover example.
-- The affine cone has dimension 4 and codimension 3 in 7 variables.  We
-- inspect Jacobian minors on the smooth locus and compare their transition
-- ratios, which is the local input needed for a canonical-form atlas.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

rayList = {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB,
    h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
branch = sum apply(coverVars,q -> q^4);
W = T/(sub(I0,T)+ideal(c^4-branch));
I = ideal W;
ambientVars = flatten entries vars ambient W;
print("HB=" | toString HB);
print("I0=" | toString sub(I0,T));
print("W relations=" | toString I);
print("dim W=" | toString dim W);
stamp("cyclic cover constructed");

-- Use the first three independent relation rows from a minimal generating
-- set.  For each 3x3 Jacobian minor, the corresponding local top form is
-- (up to sign) the complementary 4-form divided by that minor.
G = gens I;
relCount = numgens I;
print("num relations=" | toString relCount);
J = jacobian G;
print("jacobian size=" | toString numRows J | "x" | toString numColumns J);
print("rank of jacobian over W=" | toString rank sub(J,W));
stamp("jacobian computed");

-- Find nonzero maximal minors and print their complementary coordinate sets.
minorSize = dim ambient W - dim W;
minorsJ = minors(minorSize,J);
print("nonzero Jacobian minors=" | toString numgens trim minorsJ);
minorsJW = sub(minorsJ,W);
print("Jacobian singular-locus ideal dimension=" | toString dim(W/minorsJW));
stamp("Jacobian minors inspected");

-- Make the atlas data explicit.  A chart is indexed by a choice of three
-- coordinate rows and three relation columns for which the determinant is
-- nonzero.  The complementary four coordinates give the numerator of the
-- local top form.
varIndices = toList(0..(#ambientVars-1));
relIndices = toList(0..(relCount-1));
chartCandidates = flatten for rr in subsets(varIndices,minorSize) list
    for cc in subsets(relIndices,minorSize) list (
        delta := det submatrix(J,rr,cc);
        {rr,cc,delta,toList(set varIndices - set rr)}
        );
chartData = select(chartCandidates, q -> q#2 != 0);
print("explicit chart records=" | toString(#chartData));
print("first chart record=" | toString(first chartData));
print("chart denominator degree=" | toString(degree((first chartData)#2)));
assert(ideal apply(chartData, q -> q#2) == minorsJ);
assert(all(chartData, q -> #(q#3) == dim W));
stamp("explicit chart records built");

K = canonicalDivisor(W,IsGraded=>true);
print("canonical K=" | toString K);
print("K coefficients=" | toString coefficients K);
print("K primes=" | toString primes K);
print("K is Cartier=" | toString isCartier(K,IsGraded=>true));
print("K class module degrees=" | toString degrees OO(K));
print("K Q-Cartier index bound 8=" | toString isQCartier(8,K,IsGraded=>true));
stamp("canonical divisor and module compared");

-- The local form associated to a nonzero maximal minor has the shape
-- complementary four-form / minor.  We record the available denominator
-- ideal and its homogeneous degrees as the first atlas certificate.
print("Jacobian denominator ideal degrees=" | toString degrees trim minorsJ);
print("Jacobian denominator ideal codim=" | toString codim trim minorsJ);

nonCartier = nonCartierLocus(K);
nonCartierW = sub(nonCartier,W);
singularW = sub(ideal singularLocus W,W);
print("nonCartier locus dimension=" | toString dim(W/nonCartierW));
print("singular locus dimension=" | toString dim(W/singularW));
print("nonCartier disappears on Jacobian charts=" | toString(
    trim radical saturate(nonCartierW,minorsJW) == ideal(1_W)));
print("same radical support=" | toString(
    trim radical nonCartierW == trim radical singularW));
stamp("non-Cartier locus compared with Jacobian singular locus");

assert(rank sub(J,W) == 3);
assert(dim(W/minorsJW) == 1);
assert(dim(W/nonCartierW) == 1);
assert(trim radical nonCartierW == trim radical singularW);
assert(trim radical saturate(nonCartierW,minorsJW) == ideal(1_W));
assert(isQCartier(8,K,IsGraded=>true) == 0);
print("OK chartwise canonical-form certificate: smooth charts cover codimension one and K's non-Cartier support is exactly the singular locus");
