-- Xminus の次の一歩:  指数 a = 2 が出たので K_X が nef かを判定する.
-- K は環にキャッシュされるので, canonicalIndexData のあと canonicalNefData を
-- 同じプロセスで呼べば再計算されない.

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
print("Xminus:  変数 " | toString numgens ambient R
    | ",  codim " | toString (dim ambient R - dim R) | ",  deg " | toString degree R);
flush stdio;

idx = timeIt("canonicalIndexData(limit 12)",
    () -> canonicalIndexData(R,CanonicalIndexSearchLimit=>12));
if not idx#"conclusive" then (print "  指数が出ない"; exit 0);
a = idx#"index";
print("  index = " | toString a); flush stdio;

-- 2 回目の K はキャッシュから返るはず.
kdivFn = value(MMPComputation#"private dictionary"#"mmpCanonicalDivisorInternal");
timeIt("K の再取得 (キャッシュが効けば一瞬)",() -> kdivFn R);

ample = timeIt("weightedAmpleDivisorData",() -> weightedAmpleDivisorData R);
print("  weights = " | toString (ample#"weights")
    | ",  cartierDegree = " | toString (ample#"cartierDegree"));
flush stdio;

nef = timeIt("canonicalNefData(R," | toString a | ")",
    () -> canonicalNefData(R,a,NefSearchLimit=>12));
print("  conclusive = " | toString (nef#"conclusive"));
if nef#"conclusive" then (
    print("  nef = " | toString (nef#"nef"));
    print("  witnessType = " | toString (nef#"witnessType"));
    );
flush stdio;
print "=== 完了 ===";
