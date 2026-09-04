-- Xminus の通し.  mmpCanonicalDivisorInternal が入ったので, canonicalDivisor
-- の Ext (8GB 超) を経由せずに canonicalIndexData まで到達できるはず.
-- 標準イデアルの構成が約 13 分, その先は未知.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "Polyhedra"; needsPackage "WeilDivisors"; needsPackage "NormalToricVarieties";
timeIt = (l,f) -> (t0:=cpuTime(); r:=f();
    print("  " | l | ":  " | toString(cpuTime()-t0) | " s"); flush stdio; r);

rayList = {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}};
HB0 = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3]; S0 = QQ[y_1..y_(#HB0)];
I0 = ker map(L,S0,apply(HB0,h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
Tq = QQ[y_1..y_(#HB0),w,c];
br = sum apply(take(flatten entries vars Tq,#HB0+1),q -> q^4);
Wc = Tq/(sub(I0,Tq)+ideal(c^4-br));
Gm = b2mToGraphMorphism(
    bigradedReesProjection ideal(2*canonicalDivisor(Wc,IsGraded=>true)),Verbose=>false);
Xq = minimalPresentation Gm#sourceRing;
kk = ZZ/32003;
Ax = ambient Xq; AmbP = kk[gens Ax];
R = AmbP/sub(ideal Xq,AmbP);
print("Xminus (極小表示 / GF(32003)):  変数 " | toString numgens ambient R
    | ",  codim " | toString (dim ambient R - dim R)
    | ",  deg " | toString degree R);
flush stdio;

kdivFn = value(MMPComputation#"private dictionary"#"mmpCanonicalDivisorInternal");
seedKey = value(MMPComputation#"private dictionary"#"mmpCanonicalIdealSeedData");
K = timeIt("mmpCanonicalDivisorInternal",() -> kdivFn R);
print("  seed がキャッシュされたか ?  " | toString (K#cache#?seedKey));
if K#cache#?seedKey then (
    sd := K#cache#seedKey;
    print("  certificate = " | (sd#"certificate"));
    print("  embeddingDegree = " | toString (sd#"embeddingDegree")
        | ",  ideal 生成元 " | toString numgens (sd#"ideal"));
    );
flush stdio;

idx = timeIt("canonicalIndexData(limit 12)",
    () -> canonicalIndexData(R,CanonicalIndexSearchLimit=>12));
print("  conclusive = " | toString (idx#"conclusive"));
if idx#"conclusive" then print("  index = " | toString (idx#"index"));
flush stdio;
print "=== 完了 ===";
