-- Regression for the Noether-normalization route to the canonical ideal.
--
-- omega_R = Hom_A(R, omega_A) for a Noether normalization A = k[theta] -> R,
-- with the A-basis taken as a lift of a k-basis of the Artinian reduction
-- R/(theta).  Used only past mmpNoetherCodimThreshold, where the Ext route's
-- resolution of R over its ambient is out of reach: on the cyclic cover's flip
-- target (29 variables, codim 25) that Ext exceeds 8GB, and Ext^16 on v_3(P^3)
-- below did not return in 887s, where this route takes about eight seconds.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

noetherFn = value(
    MMPComputation#"private dictionary"#"noetherCanonicalIdealSeedInternal");
seedFn = value(
    MMPComputation#"private dictionary"#"canonicalIdealSeedDataInternal");
threshold = value(
    MMPComputation#"private dictionary"#"mmpNoetherCodimThreshold");

kk = ZZ/32003;
SP = kk[x0,x1,x2,x3];

veroneseRing = m -> (
    mons := first entries basis(m,SP);
    T := kk[yy_1..yy_(#mons)];
    T/(ker map(SP,T,mons)));

-- Below the threshold nothing changes route, and the two agree anyway.
R2 = veroneseRing 2;
assert(dim ambient R2 - dim R2 == 6);
assert(6 < threshold);
extSeed = seedFn(R2,null);
assert(extSeed#"certificate" ==
    "canonical module Ext/Hom embedding and ideal reflexive powers");
noetherSeed = noetherFn R2;
assert(noetherSeed =!= null);
assert(noetherSeed#"embeddingDegree" == extSeed#"embeddingDegree");
assert(apply(toList(0..5), i -> hilbertFunction(i, module (noetherSeed#"ideal")))
    == apply(toList(0..5), i -> hilbertFunction(i, module (extSeed#"ideal"))));
print "OK Noether route agrees with the Ext route on the 2-uple Veronese of P3.";

-- Above it the seed switches route, and the answer is the one theory predicts:
-- omega = ⊕_d H^0(O(3d-4)), so with the embedding degree -1 the ideal's Hilbert
-- function is d |-> h^0(O(3(d+1)-4)) = binomial(3d+2,3).
R3 = veroneseRing 3;
assert(dim ambient R3 - dim R3 == 16);
assert(16 >= threshold);
seed3 = seedFn(R3,null);
assert(seed3#"certificate" ==
    "canonical module via Noether normalization, embedding solved over the base field");
assert(seed3#"embeddingDegree" == {-1});
expected = apply(toList(0..5), d -> if 3*d-1 < 0 then 0 else binomial(3*d+2,3));
assert(apply(toList(0..5), i -> hilbertFunction(i, module (seed3#"ideal")))
    == expected);
print "OK past the codimension threshold the seed uses Noether normalization and matches theory.";

-- The canonical divisor itself, not just the seed: canonicalDivisor is
-- WeilDivisors' own function and runs the same Ext, so without this every
-- caller would still stop there before the seed was ever asked for.
--
-- v_3(P^3) is P^3 re-embedded by O(3), so X is smooth and every divisor on it
-- is Cartier: the canonical index is 1.  It is worth being explicit that this
-- is not the same as the smallest m with m*K in Z*H, which is 3 here since
-- K_{P^3} = O(-4) is -4/3 times O(3).  Conflating the two is exactly the defect
-- fixed in tests/cartier-index-fastpath.m2: taking the seed certificate's
-- negative as a verdict computes the second quantity, not the index.
kdivFn = value(MMPComputation#"private dictionary"#"mmpCanonicalDivisorInternal");
seedKey = value(MMPComputation#"private dictionary"#"mmpCanonicalIdealSeedData");
K3 = kdivFn R3;
assert(K3#cache#?seedKey);
index3 = canonicalIndexData(R3,CanonicalIndexSearchLimit=>6);
assert(index3#"conclusive");
assert(index3#"index" == 1);
print "OK the canonical divisor comes out of the Noether route; v_3(P3) is smooth so its index is 1.";

-- The route declines what it cannot handle, so the caller always has a fallback.
assert(noetherFn (kk[u,v,t,Degrees=>{1,1,2}]) === null);
Abi = kk[a0,a1,b0,b1,Degrees=>{{1,0},{1,0},{0,1},{0,1}}];
assert(noetherFn Abi === null);
print "OK the Noether route returns null on weighted and multigraded rings.";
