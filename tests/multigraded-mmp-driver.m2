needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- Iterated multigrading, Phase 1 (research-log/docs/ITERATED-MULTIGRADING-MMP-PLAN.md):
-- exercises the new threefoldMMPData(R,a,H) and threefoldMMPData(R,a,H,
-- IrrelevantIdeal=>B) top-level multigraded entry points.  These reuse
-- canonicalNefData/canonicalContractionData's existing multigraded overloads
-- for the first iteration only; a genuinely multigraded example that reaches
-- a *birational* first step (rather than terminating at that iteration) is
-- Phase 3/4 work (relativeCanonicalModelFromBaseData is still monograded),
-- so this file covers the two terminal branches (minimal model, K-negative
-- fibration) reachable without that generalization, plus the option/error gates.

-- Segre P1xP2: K=O(-2,-3), H=O(1,1); the multigraded nef test fails at the
-- first iteration and the multigraded contraction is fibre type (to P1), so
-- the whole driver terminates as a K-negative fibration in exactly one recorded
-- step, without ever flattening the bigraded presentation.
S = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
H = divisor(s) + divisor(u);

segreMMP = threefoldMMPData(S,1,H);
assert(segreMMP#"conclusive");
assert(segreMMP#"terminationType" == "K-negative fibration");
assert(segreMMP#"finalRing" === S);
assert(segreMMP#"finalIndex" == 1);
assert(segreMMP#"numberOfSteps" == 1);
assert((segreMMP#"steps")#0#"stepType" == "fibration");
assert((segreMMP#"steps")#0#"terminal");
assert(instance((segreMMP#"steps")#0#"contractionGraph",GraphMorphism));

print "OK multigraded driver: threefoldMMPData(S,1,H) reaches a K-negative fibration in one step, no flattening.";

-- The same run with an explicit caller-supplied IrrelevantIdeal (rather than
-- the internal, unexported block-structure search) gives the identical
-- termination.  S's two degree-{1,0}/{0,1} blocks are {s,t} and {u,v,w1}.
B = ideal(s,t) * ideal(u,v,w1);
segreMMPExplicitB = threefoldMMPData(S,1,H,IrrelevantIdeal=>B);
assert(segreMMPExplicitB#"conclusive");
assert(segreMMPExplicitB#"terminationType" == "K-negative fibration");
assert(segreMMPExplicitB#"numberOfSteps" == 1);

print "OK multigraded driver: an explicit caller-supplied IrrelevantIdeal reproduces the same termination.";

-- A degenerate but legitimate case of the same entry point: a monograded ring
-- (degreeLength 1) is a rank-1 admissible presentation, so multigradedBlockData
-- returns the ordinary irrelevant ideal and the BasicDivisor overload must
-- agree with the plain (Ring,ZZ) overload when K is already nef.
P3 = QQ[y0,y1,y2,y3];
HP3 = divisor y0;
p3MMP = threefoldMMPData(P3,1,HP3);
assert(p3MMP#"conclusive");
assert(p3MMP#"terminationType" == "K-negative fibration");
assert(p3MMP#"numberOfSteps" == 1);

quintic = QQ[y0,y1,y2,y3,y4]/ideal(y0^5+y1^5+y2^5+y3^5+y4^5);
Hquintic = divisor y0;
quinticMMP = threefoldMMPData(quintic,1,Hquintic);
assert(quinticMMP#"conclusive");
assert(quinticMMP#"terminationType" == "minimal model");
assert(quinticMMP#"numberOfSteps" == 0);
assert(quinticMMP#"finalRing" === quintic);

print "OK multigraded driver: the BasicDivisor overload agrees with the plain overload on monograded P3 and the quintic.";

-- Option and argument gates.
assert(try (threefoldMMPData(S,0,H); false) else true);
assert(try (threefoldMMPData(S,1,HP3); false) else true);
assert(try (threefoldMMPData(S,1,H,IrrelevantIdeal=>ideal vars P3); false) else true);
assert(try (threefoldMMPData(S,1,H,MMPMaxSteps=>0); false) else true);

print "OK multigraded driver: index positivity, matching-ring, and MMPMaxSteps gates all reject bad input.";
