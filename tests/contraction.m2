needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage("WeilDivisors");

-- The Segre threefold X=P^1 x P^2 in P^5 has
-- K_X=O(-2,-3), H=O(1,1), and threshold lambda=3.  Thus
-- K_X+3H=O(1,0), whose complete linear system is the projection to P^1.
S = QQ[z00,z01,z02,z10,z11,z12];
I = minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
X = S/I;
contraction = canonicalContractionAtThresholdData(X,1,3);

assert(contraction#"conclusive");
assert(contraction#"threshold" == 3);
assert(contraction#"multiplier" == 1);
assert(contraction#"guaranteedMultiplier" == 1920);
assert(contraction#"targetDimension" == 1);
assert(contraction#"sourceDimension" == 3);
assert(contraction#"dimensionDrop" == 2);
assert(contraction#"contractionType" == "fibration");
assert(contraction#"isFibreType");
assert(not contraction#"isBirational");
assert(contraction#"steinFactorizationType" == "computed");
assert(contraction#"steinHomData"#"certifiedBound");
assert(contraction#"linearSystemGraph"#"targetVariableCount" == 2);
assert(isPrime contraction#"linearSystemGraph"#"graphIdeal");
assert(instance(contraction#"linearSystemGraph"#"graph",GraphMorphism));
assert(instance(contraction#"contractionGraph",GraphMorphism));
assert(isPrime contraction#"contractionGraph"#definingIdeal);
assert(dim(contraction#"contractionGraph"#totalRing) == dim X+1);
assert(contraction#"contractionGraph"#sourceRing === X);
assert(contraction#"contractionGraph"#baseCoordinateRing
    === contraction#"steinAlgebraData"#"ring");

print "OK Segre P1xP2: K+3H=O(1,0) gives the connected-fibre contraction to P1.";
print "OK contraction graph: certified Stein bound, prime graph, expected dimension.";

-- The connected part of the standard blow-up example is Bl_L(P3) -> P3,
-- so source and Stein target both have projective dimension three.
B = QQ[b00,b01,b10,b11,b20,b21,b30,b31,t0,t1,t2,t3,
    Degrees=>{
        {1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},
        {0,1},{0,1},{0,1},{0,1}}];
P0 = QQ[x0,x1,x2,x3,u,v,sourceScale,targetScale];
P = P0/ideal(x0*v-x1*u);
parametrization = map(P,B,{
    x0*u*sourceScale,x0*v*sourceScale,
    x1*u*sourceScale,x1*v*sourceScale,
    x2*u*sourceScale,x2*v*sourceScale,
    x3*u*sourceScale,x3*v*sourceScale,
    x0^2*targetScale,x1^2*targetScale,
    x2^2*targetScale,x3^2*targetScale});
blowupHom = steinHomData(B,kernel parametrization);
blowupAlgebra = steinCoordinateAlgebra blowupHom;
blowupType = contractionTypeData(3,dim(blowupAlgebra#"ring")-1);
assert(blowupType#"contractionType" == "birational");
assert(blowupType#"isBirational");
assert(not blowupType#"isFibreType");
assert(blowupType#"dimensionDrop" == 0);

print "OK Bl_L(P3)->P3: equal dimensions classify the contraction as birational.";

-- Direct graph of Bl_L(P3)->P3 (without the auxiliary squaring map).  The
-- relative-differential rank-jump locus is the exceptional divisor.
BD = QQ[d00,d01,d10,d11,d20,d21,d30,d31,r0,r1,r2,r3,
    Degrees=>{
        {1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},{1,0},
        {0,1},{0,1},{0,1},{0,1}}];
DP0 = QQ[c0,c1,c2,c3,du,dv,dSourceScale,dTargetScale];
DP = DP0/ideal(c0*dv-c1*du);
directParametrization = map(DP,BD,{
    c0*du*dSourceScale,c0*dv*dSourceScale,
    c1*du*dSourceScale,c1*dv*dSourceScale,
    c2*du*dSourceScale,c2*dv*dSourceScale,
    c3*du*dSourceScale,c3*dv*dSourceScale,
    c0*dTargetScale,c1*dTargetScale,c2*dTargetScale,c3*dTargetScale});
directIdeal = kernel directParametrization;
directSourcePolynomialRing = QQ[s00,s01,s10,s11,s20,s21,s30,s31];
directTargetRing = QQ[q0,q1,q2,q3];
directSourceElimination = eliminate(directIdeal,drop(flatten entries vars BD,8));
directSourceMap = map(directSourcePolynomialRing,BD,
    flatten entries vars directSourcePolynomialRing
        | toList(4:0_directSourcePolynomialRing));
directSourceRing = directSourcePolynomialRing/directSourceMap directSourceElimination;
directGraphData = new HashTable from {
    "jointRing" => BD,
    "graphIdeal" => directIdeal,
    "sourceVariableCount" => 8,
    "sourceRing" => directSourceRing,
    "targetRing" => directTargetRing
    };
directGraph = mmpGraphMorphism directGraphData;
divisorialSmallness = contractionGraphSmallnessData directGraph;
assert(not divisorialSmallness#"isSmall");
assert(divisorialSmallness#"exceptionalDimension" == 2);
assert(divisorialSmallness#"exceptionalCodimension" == 1);

-- The standard small resolution of a projective ordinary double point has an
-- exceptional curve, hence codimension two in its threefold source.
ODP = QQ[o0,o1,o2,o3,o4]/ideal(o0*o1-o2*o3);
smallGraph = b2mToGraphMorphism bigradedReesProjection ideal(o0,o2);
smallness = contractionGraphSmallnessData smallGraph;
assert(smallness#"isSmall");
assert(not smallness#"exceptionalLocusEmpty");
assert(smallness#"exceptionalDimension" == 1);
assert(smallness#"exceptionalCodimension" == 2);

-- The diagonal graph of P1->P1 has empty exceptional locus and is small.
ID = QQ[i0,i1,j0,j1,
    Degrees=>{{1,0},{1,0},{0,1},{0,1}}];
identityGraph = new HashTable from {
    "jointRing" => ID,
    "graphIdeal" => ideal(i0*j1-i1*j0),
    "sourceVariableCount" => 2
    };
identitySmallness = contractionGraphSmallnessData identityGraph;
assert(identitySmallness#"isSmall");
assert(identitySmallness#"exceptionalLocusEmpty");
identitySource = QQ[is0,is1];
identityTarget = QQ[it0,it1];
normalizedIdentityGraph = mmpGraphMorphism new HashTable from join(
    pairs identityGraph,{
        "sourceRing" => identitySource,
        "targetRing" => identityTarget
        });
assert(instance(normalizedIdentityGraph,GraphMorphism));
assert(normalizedIdentityGraph#ambientRing === ID);
assert(normalizedIdentityGraph#definingIdeal === identityGraph#"graphIdeal");
assert(#normalizedIdentityGraph#fiberVariables == 2);
assert(#normalizedIdentityGraph#baseVariables == 2);

-- Continue the top-level driver after the independently certified divisorial
-- contraction Bl_L(P3)->P3.  The retained first graph is followed by the
-- canonical contraction P3->point, so this exercises the birational state
-- transition and the subsequent Mori-fibre termination in one driver result.
P3Target = directTargetRing;
divisorialContraction = new HashTable from {
    "conclusive" => true,
    "isBirational" => true,
    "contractionGraph" => directGraph,
    "steinAlgebraData" => new HashTable from {"ring" => P3Target}
    };
divisorialModel = relativeCanonicalModelData divisorialContraction;
divisorialStep = mmpStepRecordData(divisorialContraction,divisorialModel);
assert(divisorialStep#"stepType" == "divisorial");
assert(not divisorialStep#"contractionIsSmall");
birationalMMP = threefoldMMPData(P3Target,1,{divisorialStep});
assert(birationalMMP#"conclusive");
assert(birationalMMP#"terminationType" == "Mori fibre space");
assert(birationalMMP#"numberOfSteps" == 2);
assert((birationalMMP#"steps")#0#"stepType" == "divisorial");
assert((birationalMMP#"steps")#0#"contractionGraph" === directGraph);
assert((birationalMMP#"steps")#1#"stepType" == "fibration");
assert(try (threefoldMMPData(P3Target,1,{(birationalMMP#"steps")#1}); false)
    else true);
assert(try (threefoldMMPData(QQ[r0,r1,r2,r3],1,{divisorialStep}); false)
    else true);

print "OK smallness: blow-up divisor has codimension 1; ODP exceptional curve has codimension 2.";
print "OK smallness: identity graph has empty exceptional locus.";
print "OK birational MMP: Bl_L(P3)->P3 is retained before P3 terminates over a point.";
