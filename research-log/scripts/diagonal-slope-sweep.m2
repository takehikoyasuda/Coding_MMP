-- w-対角は選択である.  b2mDiagonalData は
--     slope = max(1, 1 + max ceiling(e_j/p_j))
-- を固定で使うが, grading chamber の条件は D > max(e_j/p_j) だけなので,
-- e_j/p_j が整数でないときこの式は必要以上に大きい D を取る.
-- D を変えると Segre Hilbert 基底の個数 = flattening の変数の個数が変わる.
-- 論文の枠内 (w-対角) に留まったまま, 一番小さい表示を探せるか.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "Polyhedra"; needsPackage "WeilDivisors"; needsPackage "NormalToricVarieties";

-- segre.m2 の segreHilbertBasis と同じもの (非公開なので再実装).
segreHB = (ds,cs) -> (
    N := #ds + #cs;
    eqs := matrix {ds | apply(cs, c -> -c)};
    C := coneFromHData(id_(ZZ^N), eqs);
    apply(hilbertBasis C, v -> flatten entries v));

rayList = {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}};
HB0 = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3]; S0 = QQ[y_1..y_(#HB0)];
I0 = ker map(L,S0,apply(HB0,h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
T = QQ[y_1..y_(#HB0),w,c];
branch = sum apply(take(flatten entries vars T,#HB0+1),q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));
P = bigradedReesProjection ideal(2*canonicalDivisor(Wcover,IsGraded=>true));

us = P#fiberVariables; xs = P#baseVariables;
p = apply(us,u -> (degree u)#0);      -- fibre first weights
e = apply(us,u -> (degree u)#1);      -- fibre shifts
cs = apply(xs,x -> (degree x)#1);     -- base weights
print("fibre first weights p = " | toString p);
print("fibre shifts        e = " | toString e);
print("base weights        c = " | toString cs);
ratios = apply(#us, j -> e#j / p#j);
print("e_j/p_j = " | toString ratios | ",  max = " | toString max ratios);
codeSlope = max(1, 1 + max apply(#us, j -> ceiling(e#j / p#j)));
minSlope = floor(max ratios) + 1;     -- D > max(e/p) を満たす最小の整数
print("コードが使う D = " | toString codeSlope
    | ",  chamber が許す最小の D = " | toString minSlope);
flush stdio;

print "";
print "D ごとの Segre Hilbert 基底 (= flattening の変数の個数):";
for D from minSlope to codeSlope + 3 do (
    tw := apply(#us, j -> D * p#j - e#j);
    if any(tw, q -> q <= 0) then (
        print("  D = " | toString D | ":  chamber 外 (変換後の重み " | toString tw | ")");
        ) else (
        hb := segreHB(tw,cs);
        degs := apply(hb, v -> sum apply(#us, j -> p#j * v#j));
        print("  D = " | toString D | ":  変数 " | toString (#hb)
            | ",  座標次数 " | toString tally degs
            | (if D == codeSlope then "     <- コードの選択" else ""));
        );
    flush stdio;
    );
print "=== 完了 ===";
