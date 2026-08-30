-- canonicalDivisor(Xminus) はどちらの段で 8GB を超えるのか.
--     段1  Ext^codim_S(S/I, S(-n))
--     段2  divisor(Ext ** R)  [= embedAsIdeal]
-- Xminus は CM (dim_k R/(theta) = 124 = deg X) なので omega の生成元は
-- 少ないはずで, 段2 は安いはず.  だとすれば段1 が犯人で, それは
-- Noether ルート (omega_R = Hom_A(R,A(-4))) がまさに置き換える部分.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "Polyhedra"; needsPackage "WeilDivisors"; needsPackage "NormalToricVarieties";

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
Xq = minimalPresentation antiGraph#sourceRing;
Amb = ambient Xq;
AmbP = (ZZ/32003)[gens Amb];
S = AmbP; I = sub(ideal Xq,AmbP); R = S/I;
n = numgens S; c = codim I; dS = dim S; dR = dim R;
print("=== Xminus (極小表示 / GF(32003)):  変数 " | toString n
    | ",  codim " | toString c | " ===");
print("  自由分解の長さを " | toString(dS-dR) | " 段まで要求する");
flush stdio;

-- 段1 を分解して, どの homological degree で膨らむのかを見る.
C = timeIt("自由分解 res(S/I) の構築",() -> res(comodule I, LengthLimit => dS-dR));
print("  分解の各段のランク = " | toString apply(toList(0..length C), i -> rank C_i));
flush stdio;

M1 = timeIt("段1  Ext^" | toString(dS-dR),
    () -> Ext^(dS-dR)(comodule I, S^{-n}));
print("  omega の生成元数 = " | toString numgens M1); flush stdio;
M1R = timeIt("      Ext ** R",() -> M1 ** R);
K = timeIt("段2  divisor(...)  [= embedAsIdeal]",() -> divisor(M1R,IsGraded=>true));
print("  K = " | toString K); flush stdio;
print "=== 完了 ===";
