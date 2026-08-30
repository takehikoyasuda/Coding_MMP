-- theta を一般線形形式にすると, t -> theta の代入で関係式行列の成分が
-- 29 変数の密な多項式になり, Hom(omega,R) が 9GB を超える.  座標変換で
-- theta を変数にすれば疎に保てるが, Xminus では 1982 秒かかる.
--
-- もっと安い可能性:  29 個の変数のうち 4 本がそのまま斉次パラメータ系に
-- なっていないか.  なっていれば座標変換は 0 秒で済む.
-- 標準次数付き CM 環では線形な hsop なら dim_k R/(theta) = deg X なので,
-- 判定は「Artin になるか」だけ.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "Polyhedra"; needsPackage "WeilDivisors"; needsPackage "NormalToricVarieties";
kk = ZZ/32003;
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
Ax = ambient Xq; AmbP = kk[gens Ax];
R = AmbP/sub(ideal Xq,AmbP);
n = numgens AmbP; d = dim R;
vs = flatten entries vars R;
print("=== Xminus:  変数 " | toString n | ",  dim " | toString d
    | ",  deg " | toString degree R | " ===");
flush stdio;

setRandomSeed 12345;
found = {};
trials = 12;
timeIt("変数 4 本の組を " | toString trials | " 通り試す",() -> (
    for tr from 1 to trials do (
        if #found >= 3 then break;
        idx := take(random toList(0..n-1), d);
        cand := apply(idx, i -> vs#i);
        q := R/ideal cand;
        len := try (numcols basis q) else -1;
        if len >= 0 then (
            found = append(found,{sort idx, len});
            print("    " | toString sort idx | ":  Artin,  dim_k = " | toString len);
            ) else print("    " | toString sort idx | ":  Artin でない");
        flush stdio;
        );
    true));
print("  hsop になった組 = " | toString (#found) | " / 試行 " | toString trials);
if #found > 0 then (
    best := first found;
    print("  例:  変数 " | toString (best#0) | ",  dim_k = " | toString (best#1)
        | "   (deg X = " | toString degree R | " と一致すれば hsop 確定)");
    );
print "=== 完了 ===";
