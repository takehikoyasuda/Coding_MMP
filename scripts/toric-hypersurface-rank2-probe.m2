-- Phase E (docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md, section 4.1/7): validate
-- the rank-2 VGIT toric-ambient hypersurface candidate before spending time on
-- Stein/smallness/flip.  Cox variables u0,u1 (deg (1,0)), x (deg (0,1)),
-- y0,y1,y2 (deg (-1,1)); hypersurface of multidegree (-2,4); expected
-- irrelevantIdeal (u0,u1)*(x,y0,y1,y2); expected K_X=(-1,0); polarization
-- H=(1,1).
--
-- Section 4.3 lesson: an earlier probe broke the equation across lines
-- without wrapping it in parentheses, so only the first summand was actually
-- substituted and the ring was silently non-domain.  Every summand below is
-- therefore assembled on a single logical statement, with the full sum
-- wrapped in one set of parentheses, and isPrime/isNormal are checked before
-- any WeilDivisors call.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];

Fquad = 3*y0^2 - y1^2 + 2*y0*y1 - y2^2 + y1*y2;
Fcubic = y0^3 + 2*y0^2*y1 - y1^2*y2 + y2^3 - y0*y1*y2;
Fquartic = y0^4 - y1^4 + 2*y0^2*y1^2 + y1^3*y2 - y2^4 + y0*y1*y2^2;
F = (x^2*Fquad + x*(u0+2*u1)*Fcubic + (u0^2+u0*u1+2*u1^2)*Fquartic);
stamp("F constructed");
print("degree F=" | toString degree F);
if degree F != {-2,4} then error "F is not homogeneous of multidegree (-2,4)";

isPrimeF = isPrime ideal F;
print("isPrime ideal F=" | toString isPrimeF);
stamp("isPrime checked");
if not isPrimeF then error "F does not generate a prime ideal; pick different coefficients";

R = A/F;
print("numgens ambient R=" | toString numgens ambient R);
print("dim R=" | toString dim R);

isNormalR = isNormal R;
print("isNormal R=" | toString isNormalR);
stamp("isNormal checked");
if not isNormalR then error "R is not normal; pick different coefficients";

-- multigradedBlockData is unexported; read it via the private dictionary,
-- the same technique tests/multigraded-skew-cartier.m2 uses.
multigradedBlockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
isCartierSaturatedInternalFn = value(MMPComputation#"private dictionary"#"isCartierSaturatedInternal");

-- multigradedBlockData should auto-derive B=(u0,u1)*(x,y0,y1,y2) and
-- geometricDimension=3 without an explicit IrrelevantIdeal option.
blockData = multigradedBlockDataFn R;
print("blockData#geometricDimension=" | toString blockData#"geometricDimension");
print("blockData#blockVariables=" | toString blockData#"blockVariables");
B = blockData#"irrelevantIdeal";
print("B=" | toString B);
stamp("multigradedBlockData computed");

expectedB = ideal(u0,u1) * ideal(x,y0,y1,y2);
if B != sub(expectedB,R) then
    error "multigradedBlockData did not derive the expected irrelevant ideal";
if blockData#"geometricDimension" != 3 then
    error "geometricDimension is not 3";

K = canonicalDivisor(R,IsGraded=>true);
print("K=" | toString K);
stamp("K computed");

-- H = u0 + x has degree (1,0)+(0,1) = (1,1) as expected.
H = divisor(u0) + divisor(x);
stamp("H constructed");

aK = 1*K;
cartierK = isCartierSaturatedInternalFn(aK,B);
print("isCartier(K,B)=" | toString cartierK);
stamp("Cartier(K) checked");

cartierH = isCartierSaturatedInternalFn(H,B);
print("isCartier(H,B)=" | toString cartierH);
stamp("Cartier(H) checked");

-- Raw driver step: no known contraction target, no certified prefix, no
-- flipping curve supplied.  canonicalNefData(R,a,H,IrrelevantIdeal=>B) must
-- discover nef-ness itself; a=1 since K itself is already Cartier above.
nefData = canonicalNefData(R,1,H,IrrelevantIdeal=>B);
print("nefData#conclusive=" | toString nefData#"conclusive");
print("nefData#nef=" | toString nefData#"nef");
stamp("canonicalNefData(R,1,H,B) done");

