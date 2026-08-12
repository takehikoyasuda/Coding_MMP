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
assert(isPrime contraction#"contractionGraph"#"graphIdeal");
assert(dim(contraction#"contractionGraph"#"jointRing"
    /contraction#"contractionGraph"#"graphIdeal") == dim X+1);

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
directGraph = new HashTable from {
    "jointRing" => BD,
    "graphIdeal" => directIdeal,
    "sourceVariableCount" => 8
    };
divisorialSmallness = contractionGraphSmallnessData directGraph;
assert(not divisorialSmallness#"isSmall");
assert(divisorialSmallness#"exceptionalDimension" == 2);
assert(divisorialSmallness#"exceptionalCodimension" == 1);

-- The diagonal graph of P1->P1 has empty exceptional locus and is small.
ID = QQ[i0,i1,j0,j1,
    Degrees=>{{1,0},{1,0},{0,1},{0,1}}];
identityGraph = new HashTable from {
    "jointRing" => ID,
    "graphIdeal" => ideal(i0*j1-i1*j0),
    "sourceVariableCount" => 2
    };
smallness = contractionGraphSmallnessData identityGraph;
assert(smallness#"isSmall");
assert(smallness#"exceptionalLocusEmpty");

print "OK smallness: blow-up divisor has codimension 1; identity graph has empty exceptional locus.";
