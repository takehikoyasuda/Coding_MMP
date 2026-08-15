needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md sections 5 and 7 (Phase C):
-- canonicalNefThresholdDataCore's candidate-search step now picks the
-- cheapest untested candidate (by denominator, then numerator) instead of
-- the sorted list's middle index, and records enough per-test diagnostic
-- data ("testLog") to refine the cost model later. This must still return
-- exactly the same threshold as before, on every existing example.

R = QQ[x0,x1,x2,x3];
p3 = canonicalNefThresholdData(R,1);
assert(p3#"conclusive");
assert(p3#"threshold" == 4);
assert(#(p3#"testLog") > 0);
scan(p3#"testLog", e -> (
    assert(e#"denominator" == denominator(e#"candidate"));
    assert(e#"actualCpuTime" >= 0);
    assert(member(e#"nefCertificate",
        {"base-point-free multiple","effective base-point-free theorem",
         "negative curve intersection"}));
    ));

print "OK cost-aware threshold search: testLog is well-formed and P3's threshold is unchanged.";

-- Bl_p(P3): candidates = {4/3, 3/2, 2}, so the candidate-search window has
-- more than one untested entry before the first test (unlike P3 and Segre
-- P1xP2, tested below, where it always has exactly one) -- the first
-- example in this project's test suite where the selection rule actually
-- has more than one candidate to choose between.
Sb = QQ[x0,x1,x2,x3,u0,u1,u2,
    Degrees => {{1,0},{1,0},{1,0},{1,0},{0,1},{0,1},{0,1}}];
Rb = Sb/minors(2, matrix{{x1,x2,x3},{u0,u1,u2}});
w = divisor(x0) + divisor(u0);
bd = canonicalNefThresholdData(Rb,1,w);
assert(bd#"conclusive");
assert(bd#"threshold" == 2);
assert(bd#"candidates" == {4/3,3/2,2});

-- candidates#2 = 2 is beta, already known nef from the bracket phase, so
-- the candidate-search window is indices 0,1 (values 4/3 and 3/2). Cost =
-- denominator*(numeratorBound+1)+numerator: 3*5+4=19 for 4/3 (denominator
-- 3), 2*5+3=13 for 3/2 (denominator 2). 3/2 is cheaper, so it must be
-- tested first, and its non-nef result immediately settles lo=hi=2 without
-- ever testing 4/3.
firstTest = (bd#"testLog")#0;
assert(firstTest#"candidate" == 3/2);
assert(firstTest#"denominator" == 2);
assert(firstTest#"estimatedCost" == 2*(bd#"numeratorBound"+1)+3);
assert(#(bd#"testLog") == 1);
assert(firstTest#"nefCertificate" == "effective base-point-free theorem");

print "OK cost-aware threshold search: Bl_p(P3) tries the denominator-2 candidate before the denominator-3 one.";

-- Segre P1xP2: candidates = {3,4}, the same "window of exactly one" shape
-- as P3 -- included so both of the plan's rank-2 measurement inputs
-- (docs/STAGE1-MEASUREMENT-PLAN.md section 5.1) are covered here, not just
-- the monograded case.
S = QQ[s,t,u,v,w1, Degrees => {{1,0},{1,0},{0,1},{0,1},{0,1}}];
H = divisor(s) + divisor(u);
sd = canonicalNefThresholdData(S,1,H);
assert(sd#"conclusive");
assert(sd#"threshold" == 3);
assert(#(sd#"testLog") == 1);
assert((sd#"testLog")#0#"candidate" == 3);

-- No candidate is tested twice within the candidate-search phase (testAt's
-- cache is shared with the bracket phase, but the candidate-search loop
-- itself only ever narrows lo/hi and never revisits an excluded index).
scan({p3,bd,sd}, td ->
    assert(#(unique apply(td#"testLog", e -> e#"candidate")) == #(td#"testLog")));

print "OK cost-aware threshold search: no candidate is tested twice.";
