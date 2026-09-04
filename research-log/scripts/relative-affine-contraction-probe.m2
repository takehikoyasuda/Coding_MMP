-- Probe: nef threshold and extremal contraction over an affine base.
--
-- Follows research-log/scripts/relative-affine-base-probe.m2, which got
-- canonicalNefData to a correct verdict on a projective scheme over Spec R_0.
-- This one carries the same two inputs further, into the threshold and the
-- contraction, and adds a genuine relative birational contraction.
--
--   P^2 x A^1        K = O(-3), H = O(1), so K + tH = O(t-3) is f-nef exactly
--                    for t >= 3.  Expect lambda = 3.  At lambda the divisor is
--                    trivial, so the contraction is the projection to the base
--                    A^1: a K-negative fibration in the relative sense.
--
--   Bl_0(A^3)        Proj of the Rees algebra of m = (a,b,c), presented by the
--                    2x2 minors with the base variables in degree zero.
--                    K = 2E, and O_X(1) = -E, so K + tH = (2-t)E and
--                    E.C = -1 on a line of E = P^2.  Expect lambda = 2 and a
--                    divisorial contraction back down to A^3 -- an honest MMP
--                    step over an affine base.

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

runCase = (name, R, a, expectedLambda) -> (
    << endl << "=== " << name << " ===" << endl;
    << "  dim R = " << dim R << ", dim R - 1 = " << dim R - 1 << endl;
    stage("canonicalNefData", () -> (canonicalNefData(R,a))#"nef");
    stage("canonicalNefThreshold  (expect " | toString expectedLambda | ")",
        () -> canonicalNefThreshold(R,a));
    stage("canonicalContractionData", () -> (
        d := canonicalContractionData(R,a);
        keysWanted := {"conclusive","contractionType","isBirational",
            "sourceDimension","targetDimension"};
        toString apply(select(keysWanted, k -> d#?k), k -> k => d#k)));
    );

R1 = QQ[t,x,y,z, Degrees => {0,1,1,1}];
runCase("P^2 x A^1", R1, 1, 3);

S2 = QQ[a,b,c,x,y,z, Degrees => {0,0,0,1,1,1}];
R2 = S2/minors(2, matrix{{a,b,c},{x,y,z}});
runCase("Bl_0(A^3)", R2, 1, 2);

<< endl << "probe finished" << endl;
