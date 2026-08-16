needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- research-log/docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md section 6.3: WeilDivisors'
-- mapToProjectiveSpace defends against the D = 0 case by checking only the
-- first component of the embedding degree shift d1 returned by embedAsIdeal
-- ("if d1#0 == 0 then ..."). On a multigraded ring this misfires whenever
-- d1 is a nonzero vector whose first entry happens to be 0, multiplying
-- every returned section by the ring's first variable.
--
-- Segre P1xP2 (same presentation as tests/multigraded-nefness.m2) exhibits
-- this exactly: divisor(u) is base-point-free, principal, and embeds via
-- embedAsIdeal with shift d1 = degree(u) = {0,1} -- not the zero vector, so
-- no defense should fire, but the first-component check fires anyway.

S = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
D = divisor(u);
H = divisor(s) + divisor(u);

assert(isBasePointFreeDivisor D);

-- Confirm the exact bug this regression guards against, directly against
-- WeilDivisors' own (unpatched) mapToProjectiveSpace: it really does produce
-- section representatives with an artificial common factor of s on this
-- input, so this test is not vacuous.
buggyMap = mapToProjectiveSpace(D,Variable=>"mmpRegressionRawYY");
assert((first entries buggyMap.matrix) == {s*u,s*v,s*w1});

-- completeLinearSystemGraphDataMultigraded's "sectionImages" comes from
-- MMPComputation's own mapToProjectiveSpaceInternal, which checks every
-- component of d1. It must reproduce D's true sections u,v,w1 with no
-- artificial common factor.
g = completeLinearSystemGraphDataMultigraded(D,H);
assert((g#"sectionImages") == {u,v,w1});
assert((g#"liftedSectionImages") == {u,v,w1});

print "OK section representatives: divisor(u)'s embedding shift {0,1} on a bigraded ring no longer triggers WeilDivisors' D=0 defense.";

-- Sanity check that the genuine D = 0 defense still fires: the zero
-- divisor's sections must come out multiplied by a ring variable to stay
-- homogeneous, not the bare (inhomogeneous) constant 1.
trivialDivisor = divisor(s) - divisor(s);
assert(isBasePointFreeDivisor trivialDivisor);
zeroMap = completeLinearSystemGraphDataMultigraded(trivialDivisor,H);
assert((zeroMap#"sectionImages") == {s});

print "OK section representatives: the genuine D=0 defense is unaffected.";
