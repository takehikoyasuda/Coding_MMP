-- Artin 基底ルートを本物の Xminus (35 変数, codim 31 の単一次数化) に当てる.
-- 合成標的 v_4(P^3) では hsop 8.09s + Artin 剰余 3.42s + 基底 0.001s = 11.5s で
-- 通った.  Xminus が CM なら dim_k R/(theta) = deg X が出て, 次数分布が
-- Gorenstein 判定と標準因子のシフトを与えるはず.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "Polyhedra";
needsPackage "WeilDivisors";
needsPackage "NormalToricVarieties";

timeIt = (label,f) -> (
    t0 := cpuTime(); r := f();
    print("  " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio; r);

-- cyclic-cover-raw-driver-probe.m2 と同一の構成.
rayList = {{1,0,0}, {0,1,0}, {0,0,1}, {1,1,-2}};
HB = apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
    v -> flatten entries v);
L = QQ[t1,t2,t3];
S0 = QQ[y_1 .. y_(#HB)];
I0 = ker map(L,S0,apply(HB,h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
T = QQ[y_1 .. y_(#HB),w,c];
coverVars = take(flatten entries vars T,#HB+1);
branch = sum apply(coverVars,q -> q^4);
Wcover = T/(sub(I0,T)+ideal(c^4-branch));

Kbase = timeIt("canonicalDivisor(Wcover)",() -> canonicalDivisor(Wcover,IsGraded=>true));
antiProjection = timeIt("bigradedReesProjection",() -> bigradedReesProjection ideal(2*Kbase));
antiGraph = timeIt("b2mToGraphMorphism",() -> b2mToGraphMorphism(antiProjection,Verbose=>false));
Xminus = antiGraph#sourceRing;

Amb = ambient Xminus;
IX = ideal Xminus;
print "=== Xminus の素性 ===";
print("  変数 " | toString numgens Amb
    | ",  degreeLength " | toString degreeLength Amb
    | ",  dim " | toString dim Xminus
    | ",  codim " | toString (dim Amb - dim Xminus)
    | ",  生成元 " | toString numgens trim IX);
flush stdio;

-- GF(32003) に還元.  QQ のままだと Artin 剰余だけで 326s かかる.
kkp = ZZ/32003;
AmbP = kkp[gens Amb];
RP = timeIt("GF(32003) への還元",() -> AmbP/sub(IX,AmbP));
print("  還元後:  dim " | toString dim RP
    | ",  codim " | toString (numgens AmbP - dim RP)
    | ",  生成元 " | toString numgens trim ideal RP);
flush stdio;

-- CM 判定の基準値:  重複度 deg X.  R が CM なら dim_k R/(theta) = deg X,
-- CM でなければ真に大きくなる.
degX = timeIt("deg X (重複度)",() -> degree RP);
print("  deg X = " | toString degX); flush stdio;

-- 一般線形形式 4 本.  無限体上では一般の線形形式は自動的に hsop なので
-- 逐次的な dim 検査は不要で, basis が返ること自体が証明書になる.
d = dim RP;
thetas = timeIt("一般線形形式 " | toString d | " 本",() -> apply(d,i -> random(1,RP)));
Rbar = timeIt("Artin 剰余 R/(theta)",() -> RP/ideal thetas);
bas = timeIt("その k 基底  [返れば theta は hsop]",() -> basis Rbar);
degs = apply(degrees source bas, dg -> if instance(dg,List) then dg#0 else dg);
n = numcols bas;
print("  dim_k R/(theta) = " | toString n);
print("  基底の次数分布  = " | toString tally degs);
print("");
print("  CM か ?   dim_k R/(theta) = " | toString n
    | "  vs  deg X = " | toString degX
    | "   ->  " | (if n == degX then "CM" else "非 CM (差 " | toString (n - degX) | ")"));
rev = reverse sort degs;
mx = max degs;
sym = (sort degs) == (sort apply(degs, e -> mx - e));
print("  Gorenstein か ?  次数分布が反転対称 ?  " | toString sym
    | (if sym then "  ->  omega = R(" | toString (-mx) | ") の形" else "  ->  非 Gorenstein"));
flush stdio;
print "=== 完了 ===";
