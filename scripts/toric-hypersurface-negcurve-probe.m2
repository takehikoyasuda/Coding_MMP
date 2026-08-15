-- Phase E follow-up (docs/TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md section 10.3):
-- canonicalNefData(R,1,H,IrrelevantIdeal=>B) did not finish after 27+ minutes
-- and 5+GB of memory (killed).  Try negativeCurveWitnessData directly on K
-- itself instead -- a single weilDivisorToModule construction (for K, whose
-- ideal is just u0) plus a Hilbert-function sweep, rather than
-- canonicalScaledNefDataInternal's internal loop over several perturbed
-- multiples of H.  This is not a shortcut that assumes the answer: it is a
-- genuinely cheaper *sufficient* certificate for non-nefness (a single
-- witness curve with K.C<0); failure to find one proves nothing and must not
-- be read as "nef".
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

stamp = label -> (print(label | " cpu=" | toString cpuTime()); flush stdio);

A = QQ[u0,u1,x,y0,y1,y2, Degrees=>{{1,0},{1,0},{0,1},{-1,1},{-1,1},{-1,1}}];
Fquad = 3*y0^2 - y1^2 + 2*y0*y1 - y2^2 + y1*y2;
Fcubic = y0^3 + 2*y0^2*y1 - y1^2*y2 + y2^3 - y0*y1*y2;
Fquartic = y0^4 - y1^4 + 2*y0^2*y1^2 + y1^3*y2 - y2^4 + y0*y1*y2^2;
F = (x^2*Fquad + x*(u0+2*u1)*Fcubic + (u0^2+u0*u1+2*u1^2)*Fquartic);
R = A/F;
stamp("R constructed");

multigradedBlockDataFn = value(MMPComputation#"private dictionary"#"multigradedBlockData");
blockData = multigradedBlockDataFn R;
B = blockData#"irrelevantIdeal";
stamp("B computed");

K = canonicalDivisor(R,IsGraded=>true);
H = divisor(u0) + divisor(x);
h = {1,1};
stamp("K, H constructed");

weilDivisorsPkg = needsPackage "WeilDivisors";
weilDivisorToModule = value(weilDivisorsPkg#"private dictionary"#"divisorToModule");
zeroDegree = toList(degreeLength R : 0);
candidateBaseLocus = D -> trim ann coker basis(zeroDegree,weilDivisorToModule D);

print("computing candidateBaseLocus K ...");
flush stdio;
cbl = candidateBaseLocus K;
stamp("candidateBaseLocus K computed");
print("codim cbl=" | toString codim cbl);

print("computing negativeCurveWitnessData K ...");
flush stdio;
witnessK = negativeCurveWitnessData(K,cbl,B,h);
stamp("negativeCurveWitnessData K done");
print("witnessK=" | toString witnessK);
if witnessK =!= null then (
    print("witnessK#intersection=" | toString witnessK#"intersection");
    print("witnessK#curveIdeal=" | toString witnessK#"curveIdeal");
    );
