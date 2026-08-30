-- noetherCanonicalModuleData の実装可否を決める一点:
-- omega への R 作用は代数生成元 (29 変数) の作用だけで決まるので, 必要なのは
-- 掛け算行列 M_{x_j} (j=1..29) の 29*124 = 3596 個の正規形だけ.
--
-- theta を座標変換で「最後の 4 変数」にし, ブロック順序 {25, 4} で Gröbner
-- 基底を 1 本取れば, 剰余は自動的に A = k[t_1..t_4] 係数になり,
-- 標準単項式がそのまま A 基底 e_1..e_124 を与える.
--
-- 測るのは:  (1) そのブロック順序 GB が現実的か
--            (2) 標準単項式がちょうど 124 個か (= A 上自由の確認)
--            (3) M_{x_j} を 1 本作るのにどれだけかかるか

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
branch = sum apply(take(flatten entries vars Tq,#HB0+1),q -> q^4);
Wcover = Tq/(sub(I0,Tq)+ideal(c^4-branch));
G = b2mToGraphMorphism(
    bigradedReesProjection ideal(2*canonicalDivisor(Wcover,IsGraded=>true)),
    Verbose=>false);
Xq = minimalPresentation G#sourceRing;
kk = ZZ/32003;
n = numgens ambient Xq;
d = dim Xq;
print("Xminus (極小表示):  変数 " | toString n | ",  dim " | toString d);
flush stdio;

-- theta を最後の 4 変数にする.  変数を u_1..u_(n-d), t_1..t_d と並べ,
-- ブロック順序 {n-d, d} で t を小さいブロックに置く.
S = kk[uu_1..uu_(n-d), tt_1..tt_d, MonomialOrder => {n-d, d}];
gl = random(kk^n,kk^n);
phi = map(S,ambient Xq,(vars S) * gl);
I = timeIt("座標変換後のイデアル",() -> phi (sub(ideal Xq, ambient Xq)));
print("  生成元 " | toString numgens I); flush stdio;

Gb = timeIt("ブロック順序 {25,4} の Groebner 基底",() -> gb I);
inI = timeIt("初期イデアル",() -> monomialIdeal leadTerm Gb);
R = S/I;
Rbar = timeIt("Artin 剰余 (t を 0 に)",
    () -> S/(I + ideal apply(d, i -> S_(n-d+i))));
bas = timeIt("標準単項式 = A 基底",() -> flatten entries basis Rbar);
print("  A 基底の個数 = " | toString (#bas) | "   (124 なら A 上自由)");
print("  基底の次数分布 = " | toString tally apply(bas, m -> first degree m));
flush stdio;

-- M_{x_j} を 1 本:  x_j * e_i を A 基底で表す.
basR = apply(bas, m -> sub(m,R));
j = 0;
col = timeIt("M_{x_1} の 124 列 (正規形 124 回)",
    () -> apply(basR, e -> (S_j * lift(e,S)) % Gb));
print("  正規形の t だけへの依存を確認:  u を含む項が残っていないか");
bad = select(col, f -> (
    supp := support f;
    any(supp, v -> (index v) < n-d)));
print("  u を含む剰余 = " | toString (#bad) | " / " | toString (#col)
    | "   (0 なら A 係数で表せている)");
flush stdio;
print "=== 完了 ===";
