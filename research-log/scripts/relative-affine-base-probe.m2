-- Probe: does the driver run on a projective scheme over an affine base?
--
-- The relative setting replaces X = Proj R with R_0 = k by X = Proj R -> Spec A
-- with R_0 = A, which is presented by giving the base variables degree zero.
-- See references/AlgoMMP/RELATIVE-SETTING-AUDIT.md for what the paper's
-- statements need in that setting; this script asks the separate, purely
-- computational question of how far the existing code gets as written.
--
-- Two inputs, chosen so the expected answers are known independently:
--   P^2 x A^1        K = O(-3), the complete curves are the lines in the
--                    fibres, so K.C = -3 < 0 and K is not f-nef.
--   S x A^1, S a quintic surface in P^3
--                    K_S = O(1) is ample, so K is f-nef.
-- Both have dim R - 1 = 3, so the "expected a projective threefold" gate,
-- which reads dim R - 1, is satisfied without any change.

needsPackage("MMPComputation", FileName => "MMPComputation.m2");
needsPackage("WeilDivisors");

stage = (label, f) -> (
    t := cpuTime();
    result := try f() else "FAILED";
    elapsed := cpuTime() - t;
    << "  " << label << ": ";
    if result === "FAILED" then << "FAILED" else << toString result;
    << "   [" << elapsed << "s]" << endl;
    result);

runCase = (name, R, a) -> (
    << endl << "=== " << name << " ===" << endl;
    << "  dim R = " << dim R << ", dim R - 1 = " << dim R - 1
       << ", degreeLength = " << degreeLength R << endl;
    << "  degrees = " << toString degrees R << endl;
    stage("basis({0},R^1)", () -> toString basis({0},R^1));
    K := stage("canonicalDivisor", () -> (
        D := canonicalDivisor(R, IsGraded => true);
        toString D));
    stage("canonicalIndexData", () -> (
        d := canonicalIndexData R;
        if d#?"index" then d#"index" else "no index key"));
    stage("canonicalNefData", () -> (
        d := canonicalNefData(R, a);
        if d#?"nef" then d#"nef" else "no nef key"));
    );

-- P^2 x A^1: expect nef = false
R1 = QQ[t,x,y,z, Degrees => {0,1,1,1}];
runCase("P^2 x A^1", R1, 1);

-- quintic surface x A^1: expect nef = true
S2 = QQ[t,x0,x1,x2,x3, Degrees => {0,1,1,1,1}];
R2 = S2/ideal(x0^5+x1^5+x2^5+x3^5);
runCase("quintic surface x A^1", R2, 1);

<< endl << "probe finished" << endl;
