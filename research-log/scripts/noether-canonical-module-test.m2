-- Noether 正規化で omega_R を計算できるか, Ext より安いか.
--
-- 有限射 A = k[t_1..t_d] -> R に対し  omega_R = Hom_A(R, omega_A)  が
-- CM 性なしで成り立つ.  Ext^codim_S(R,omega_S) は S (変数が多い) 上の
-- 自由分解を codim 段まで要求するが, こちらは d 変数の環上の Hom で済む.
--
-- case A: P^3 の 2 重 Veronese in P^9   10 変数, codim 6, depth 4 (CM)
-- case C: それを P^7 へ同型射影した像     8 変数, codim 4, depth 1 (非 CM)
--   -> A では Ext ルートが 0.6 秒, C では canonicalDivisor が返らなかった.
--
-- 正解:  omega_R = ⊕_d H^0(P^3, O(2d-4)),  Hilbert 関数 0,0,1,10,35,84,...

needsPackage "PushForward";

caseName = getenv "MMPCASE";
kk = ZZ/32003;

timeIt = (label,f) -> (
    t0 := cpuTime();
    r := f();
    print("    " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio;
    r);

shift1 = {3,-2,1,4,-5,2,-1,3,5};
shift2 = {-4,1,5,-3,2,-1,4,-2};
changeCoords = (T,shifts) -> (
    n := numgens T; lv := T_(n-1);
    map(T,T,matrix{apply(n-1,i -> T_i + shifts#i * lv) | {lv}}));
dropLastVar = (T,J) -> (
    n := numgens T; T' := kk[take(gens T,n-1)];
    (T', (map(T',T,(vars T') | matrix{{0_T'}})) J));

SP3 = kk[x0,x1,x2,x3];
T10 = kk[y_1..y_10];
JA = ker map(SP3,T10,first entries basis(2,SP3));
(T,J) = if caseName == "A" then (T10,JA) else (
    E1 := eliminate(T10_9,(changeCoords(T10,shift1)) JA);
    (T9,J9) := dropLastVar(T10,E1);
    E2 := eliminate(T9_8,(changeCoords(T9,shift2)) J9);
    dropLastVar(T9,E2));

R = T/J;
d = dim R;
print("=== case " | caseName | ":  変数 " | toString numgens T
    | ",  codim " | toString codim J | ",  dim " | toString d | " ===");
flush stdio;

hilb = (M,lo,hi) -> apply(toList(lo..hi), i -> hilbertFunction(i,M));

-- ---- Noether ルート ----
print "  [Noether ルート]  omega_R = Hom_A(R, A(-d))";
thetas = timeIt("斉次パラメータ系 (一般線形形式) を取る",() -> (
    cand := apply(d,i -> random(1,R));
    if dim(R/ideal cand) != 0 then error "not a system of parameters";
    cand));
A = kk[tt_1..tt_d];
inc = map(R,A,thetas);
M = timeIt("pushFwd (R を A 加群として)",() -> first pushFwd inc);
print("    A 加群としての生成元数 = " | toString numgens M
    | ",  生成次数 = " | toString unique flatten degrees M);
flush stdio;
omegaN = timeIt("Hom_A(M, A(-d))",() -> Hom(M,A^{-d}));
print("    omega の Hilbert 関数 (0..5) = " | toString hilb(omegaN,0,5));
flush stdio;

-- ---- Ext ルート (比較対象) ----
print "  [Ext ルート]  omega_R = Ext^codim_S(R, S(-n))";
n = numgens T;
c = codim J;
omegaE = timeIt("Ext^" | toString c | "_S(R, S(-" | toString n | "))",
    () -> Ext^c(comodule J, T^{-n}));
print("    omega の Hilbert 関数 (0..5) = " | toString hilb(omegaE,0,5));
flush stdio;

print("  一致 ?  " | toString (hilb(omegaN,0,5) == hilb(omegaE,0,5)));
print("=== case " | caseName | " 完了 ===");
