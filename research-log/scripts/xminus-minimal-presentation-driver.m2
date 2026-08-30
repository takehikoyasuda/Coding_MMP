-- Xminus のイデアルは線形形式を 6 本含み, minimalPresentation は 0.33 秒で
-- 35 変数 / codim 31 を 29 変数 / codim 25 にする (環同型なので無条件に安全).
-- 以前 canonicalIndexData(Xminus) は 15.6GB OOM で落ちた.  死んだ 6 変数を
-- 落とすだけでそこを抜けられるか.
--
-- MMPFIELD = QQ | GFP,  MMPPRES = min | full

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "Polyhedra"; needsPackage "WeilDivisors"; needsPackage "NormalToricVarieties";

fieldName = getenv "MMPFIELD";
presName  = getenv "MMPPRES";

timeIt = (label,f) -> (
    t0 := cpuTime(); r := f();
    print("  " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio; r);

rayList = {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3]; S0 = QQ[y_1..y_(#HB)];
I0 = ker map(L,S0,apply(HB,h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
T = QQ[y_1..y_(#HB),w,c];
branch = sum apply(take(flatten entries vars T,#HB+1),q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));
antiGraph = b2mToGraphMorphism(
    bigradedReesProjection ideal(2*canonicalDivisor(Wcover,IsGraded=>true)),
    Verbose=>false);
Xfull = antiGraph#sourceRing;

Xq = (if presName == "min"
    then timeIt("minimalPresentation",() -> minimalPresentation Xfull)
    else Xfull);

R = (if fieldName == "GFP" then (
        Amb := ambient Xq;
        AmbP := (ZZ/32003)[gens Amb];
        timeIt("GF(32003) への還元",() -> AmbP/sub(ideal Xq,AmbP))
    ) else Xq);

print("=== " | presName | " 表示 / " | fieldName | " ===");
print("  変数 " | toString numgens ambient R
    | ",  codim " | toString (dim ambient R - dim R)
    | ",  生成元 " | toString numgens trim ideal R);
flush stdio;

K = timeIt("canonicalDivisor",() -> canonicalDivisor(R,IsGraded=>true));
print("  K = " | toString K); flush stdio;

idx = timeIt("canonicalIndexData(limit 6)",
    () -> canonicalIndexData(R,CanonicalIndexSearchLimit=>6));
print("  conclusive = " | toString idx#"conclusive"
    | (if idx#"conclusive" then ",  index = " | toString idx#"index" else ""));
flush stdio;
print "=== 完了 ===";
