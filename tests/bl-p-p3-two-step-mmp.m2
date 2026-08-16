-- SLOW TEST -- not part of `make test-core`.  Run manually with
--   M2 --no-readline --stop -q tests/bl-p-p3-two-step-mmp.m2
-- Wall time is dominated by mmpStepRecordData's contractionSmallnessData
-- call below, which took roughly 13-14 minutes of cpu time when this file
-- was written (2026-08-14, Macaulay2 1.26.06, Darwin arm64).  See
-- research-log/docs/STEIN-FACTORIZATION-COST-EXPERIMENT-REPORT.md's "Capstone" section
-- for the full cost breakdown and the reasoning behind every step below.
--
-- This is the first nontrivial (more than one step) smooth MMP example in
-- this project computed end to end from a genuinely bigraded input, with
-- no manually supplied graph anywhere in the chain -- unlike the existing
-- Bl_L(P3)/Bl_p(P3) birational-continuation regressions in
-- tests/contraction.m2, which both require the first contraction graph to
-- be built by hand because the natural monograded (Rees-Proj) presentation
-- of the blow-up stalls (research-log/docs/BOTTLENECKS-AND-MULTIGRADING.md).
--
-- Bl_p(P3) is presented in P3 x P2 as the incidence variety
--   {(x,u) : rank of matrix{{x1,x2,x3},{u0,u1,u2}} <= 1},
-- with x0 the coordinate not vanishing at the blown-up point p=[1:0:0:0].
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

S0 = QQ[x0,x1,x2,x3,u0,u1,u2,
    Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
R = S0/minors(2, matrix{{x1,x2,x3},{u0,u1,u2}});

-- The nef cone of Bl_p(P3) in the O(a,b) basis is the first quadrant,
-- bounded by O(1,0) (the blow-down E->point) and O(0,1) (the P^2-bundle
-- structure map).  Since K=-O(2,2) (Fano index 2), K+t*w is nef exactly
-- when t>=max(2/a,2/b) for w=O(a,b).  Tilting w away from (1,1) (which
-- hits both rays at once, at the numerically trivial K+2w=0, collapsing to
-- a degenerate point contraction) picks out the divisorial ray instead.
H = 2*divisor(x0) + divisor(u0);   -- w = O(2,1): threshold t*=max(2/2,2/1)=2
K = canonicalDivisor(R, IsGraded=>true);
L = K + 2*H;                        -- proportional to O(1,0), the blow-down ray

graphData = completeLinearSystemGraphDataMultigraded(L,H);
assert(graphData#"sourceVariableCount" == 19);
assert(graphData#"targetVariableCount" == 10);

-- steinHomData's own certified-bound resolution is infeasible here
-- (res(nn,LengthLimit=>28) in a 29-variable ring; unresolved after 30+
-- minutes -- see the cost-report's "Root cause" section).  The guessed
-- bound r=1 was proved -- not merely numerically matched -- to give the
-- true Stein factorization: g finite and g∘h=f hold automatically at any
-- bound (Lemma iota, AlgoMMP.tex:2197), and isNormal(cd#"ring")=true
-- (confirmed separately, ~294s, not re-run here) combined with f being
-- birational gives h_*O_Y=O_Z by Zariski's Main Theorem (Hartshorne
-- III.11.3-11.4).  See the cost report's theoretical-note sections for
-- the full argument.
hd = steinHomDataAtBound(graphData#"productRing",graphData#"graphIdeal",{1,0});
cd = steinCoordinateAlgebra(hd,0);
assert(dim(cd#"ring") == 4);

-- Build the actual contraction graph and record, mirroring
-- tests/contraction.m2's Bl_L(P3) birational-continuation pattern, but
-- with the first contraction computed here rather than supplied by hand.
rawGraph = directSteinGraph(hd,cd);
contractionGraph = mmpGraphMorphism new HashTable from join(pairs rawGraph,{
    "sourceRing" => graphData#"sourceRing",
    "targetRing" => cd#"ring"
    });

sourceDimension = 3;
targetDimension = dim(cd#"ring") - 1;
assert(targetDimension == 3);
typeData = contractionTypeData(sourceDimension,targetDimension);
assert(typeData#"isBirational");
assert(typeData#"contractionType" == "birational");

divisorialContraction = new HashTable from join({
    "conclusive" => true,
    "contractionGraph" => contractionGraph,
    "steinAlgebraData" => new HashTable from {"ring" => cd#"ring"}
    }, pairs typeData);

divisorialModel = relativeCanonicalModelData divisorialContraction;
assert(divisorialModel#"isIdentity");  -- P3's canonical algebra is already trivial

-- contractionSmallnessData (called inside mmpStepRecordData) is the
-- dominant cost of this whole file: it took roughly 13-14 minutes of cpu
-- time when this file was written, computing the exceptional locus'
-- codimension from the support of the second exterior power of relative
-- differentials.  Memory stayed flat throughout (no runaway growth), so
-- this is slow, not stuck -- unlike steinHomData's certified-bound path,
-- which never reaches this stage at all.
divisorialStep = mmpStepRecordData(divisorialContraction,divisorialModel);
assert(divisorialStep#"stepType" == "divisorial");
assert(not divisorialStep#"contractionIsSmall");  -- E is a genuine divisor, codimension 1

birationalMMP = threefoldMMPData(cd#"ring",1,{divisorialStep});
assert(birationalMMP#"conclusive");
assert(birationalMMP#"terminationType" == "K-negative fibration");
assert(birationalMMP#"numberOfSteps" == 2);
assert((birationalMMP#"steps")#0#"stepType" == "divisorial");
assert((birationalMMP#"steps")#1#"stepType" == "fibration");

print "OK Bl_p(P3) -> P3 -> point: two-step smooth MMP from a pure bigraded input, no manually supplied graph.";
