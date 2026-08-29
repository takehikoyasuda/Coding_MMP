-- Noether ルートの本来の勝負どころ = 高 codim.
--
-- P^3 の 4 重 Veronese は P^34 の中の 35 変数 / dim 4 / codim 31 で,
-- Xminus の単一次数化 (35 変数, codim 31, 280 生成元) と同じ形.
-- 記録上, Xminus のボトルネックは「codim 31 での Ext 呼び出し」だった.
--
-- omega_R = Hom_A(R, A(-4))  (A = k[t_1..t_4], 有限射) を
-- Ext^31_S(R, S(-35)) と比べる.  Noether を先に計るので, Ext が
-- 返らなくても Noether の数字は残る.
--
-- 正解:  omega_R = ⊕_d H^0(P^3, O(4d-4)),  Hilbert 関数
--        d=0: 0,  d=1: 1,  d=2: h^0(O(4))=35,  d=3: h^0(O(8))=165

needsPackage "PushForward";
kk = ZZ/32003;
m = value getenv "MMPVERONESE";     -- Veronese の次数

timeIt = (label,f) -> (
    t0 := cpuTime(); r := f();
    print("    " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio; r);

SP3 = kk[x0,x1,x2,x3];
mons = first entries basis(m,SP3);
T = kk[y_1..y_(#mons)];
J = timeIt("Veronese イデアル (ker)",() -> ker map(SP3,T,mons));
R = T/J;
n = numgens T; c = codim J; d = dim R;
print("=== v_" | toString m | "(P^3):  変数 " | toString n
    | ",  codim " | toString c | ",  dim " | toString d
    | ",  生成元 " | toString numgens trim J | " ===");
flush stdio;

hilb = (M,lo,hi) -> apply(toList(lo..hi), i -> hilbertFunction(i,M));
expected = apply(toList(0..3), i -> if m*i-4 < 0 then 0 else binomial(m*i-4+3,3));
print("  理論値 (0..3) = " | toString expected); flush stdio;

print "  [Noether ルート]";
thetas = timeIt("斉次パラメータ系",() -> (
    cand := apply(d,i -> random(1,R));
    if dim(R/ideal cand) != 0 then error "not a system of parameters";
    cand));
A = kk[tt_1..tt_d];
M = timeIt("pushFwd",() -> first pushFwd map(R,A,thetas));
print("    A 加群の生成元数 = " | toString numgens M); flush stdio;
omegaN = timeIt("Hom_A(M,A(-4))",() -> Hom(M,A^{-d}));
hn = hilb(omegaN,0,3);
print("    Hilbert 関数 (0..3) = " | toString hn);
print("    理論値と一致 ?  " | toString (hn == expected)); flush stdio;

print "  [Ext ルート]";
omegaE = timeIt("Ext^" | toString c | "_S(R,S(-" | toString n | "))",
    () -> Ext^c(comodule J, T^{-n}));
he = hilb(omegaE,0,3);
print("    Hilbert 関数 (0..3) = " | toString he);
print("    理論値と一致 ?  " | toString (he == expected)); flush stdio;
print "=== 完了 ===";
