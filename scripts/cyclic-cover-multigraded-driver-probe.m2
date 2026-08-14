-- Measured (2026-08-15, docs/ITERATED-MULTIGRADING-MMP-PLAN.md): ring
-- construction and the Cartier/BPF probes below complete in seconds, but the
-- canonicalNefData probe (which internally calls canonicalScaledNefDataInternal)
-- did not return within 15 minutes on the natural 9-variable bigraded
-- presentation.  See cyclic-cover-multigraded-cartier-probe.m2,
-- -bpf-probe.m2, and -scalednef-probe.m2 for the isolated timings that
-- pinpoint canonicalScaledNefDataInternal's internal BPF sweep as the cost.
needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("Polyhedra");
needsPackage("WeilDivisors");

stamp = label -> (
    print(label | " cpu=" | toString cpuTime());
    flush stdio;
    );

-- Same cyclic-cover base as scripts/cyclic-cover-one-flip-minimal.m2.
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB, h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));

T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
branch = sum apply(coverVars,q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));
stamp("cyclic-cover base");

Kbase = canonicalDivisor(Wcover,IsGraded=>true);
antiIdeal = ideal(2*Kbase);
antiProjection = bigradedReesProjection antiIdeal;
stamp("anti-canonical bigraded Rees projection");

-- The NATURAL bigraded presentation of X- (before b2mToGraphMorphism's
-- internal flattening to 35 variables): the total ring of the Rees
-- projection itself.
Xnatural = antiProjection#totalRing;
stamp("Xnatural = totalRing constructed");
print("naturalVariables=" | toString numgens ambient Xnatural);
print("naturalDegreeLength=" | toString degreeLength ambient Xnatural);
stamp("naturalVariables/naturalDegreeLength printed");
print("naturalDim=" | toString (dim Xnatural - 1));
stamp("naturalDim computed");
Bnatural = sub(antiProjection#irrelevantIdeal,Xnatural);
stamp("Bnatural substituted");
usNatural = apply(antiProjection#fiberVariables, u -> sub(u,Xnatural));
xsNatural = apply(antiProjection#baseVariables, x -> sub(x,Xnatural));
stamp("usNatural/xsNatural substituted");
Hnatural = divisor(usNatural#0) + divisor(xsNatural#0);
stamp("natural presentation assembled");

-- Phase 1 probe: how far does the caller-supplied-(H,B) entry point get on
-- this genuinely multigraded, non-flattened presentation, with no hand-built
-- contraction graph at all?
print "--- canonicalNefData probe ---";
nefResult = try canonicalNefData(Xnatural,2,Hnatural,
    IrrelevantIdeal=>Bnatural,NefSearchLimit=>6)
    else "ERRORED";
if instance(nefResult,String) then print("canonicalNefData: " | nefResult)
else (
    print("canonicalNefData: conclusive=" | toString nefResult#"conclusive"
        | " nef=" | toString nefResult#"nef");
    );
stamp("canonicalNefData probe");

print "--- canonicalNefThresholdData probe ---";
thresholdResult = try canonicalNefThresholdData(Xnatural,2,Hnatural,
    IrrelevantIdeal=>Bnatural,ThresholdSearchLimit=>6)
    else "ERRORED";
if instance(thresholdResult,String) then
    print("canonicalNefThresholdData: " | thresholdResult)
else print("canonicalNefThresholdData: conclusive="
    | toString thresholdResult#"conclusive");
stamp("canonicalNefThresholdData probe");

print "--- canonicalContractionData probe ---";
contractionResult = try canonicalContractionData(Xnatural,2,Hnatural,
    ThresholdSearchLimit=>6,IrrelevantIdeal=>Bnatural)
    else "ERRORED";
if instance(contractionResult,String) then
    print("canonicalContractionData: " | contractionResult)
else print("canonicalContractionData: conclusive="
    | toString contractionResult#"conclusive");
stamp("canonicalContractionData probe");

print "--- threefoldMMPData probe (the new top-level entry point) ---";
mmpResult = try threefoldMMPData(Xnatural,2,Hnatural,
    IrrelevantIdeal=>Bnatural,NefSearchLimit=>6,ThresholdSearchLimit=>6,
    MMPMaxSteps=>1)
    else "ERRORED";
if instance(mmpResult,String) then print("threefoldMMPData: " | mmpResult)
else print("threefoldMMPData: conclusive=" | toString mmpResult#"conclusive"
    | " phase=" | toString (if mmpResult#?"phase" then mmpResult#"phase" else null));
stamp("threefoldMMPData probe");
