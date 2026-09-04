-- pushFwd が codim 31 で返らない.  だが R が A 上自由なら, その基底は
-- Artin 剰余 R/(theta_1..theta_4) の k 基底を持ち上げたもので, これは
-- 汎用の押し出しよりずっと安いはず.  そこだけ計る.
--
-- 期待:  dim_k R/(theta) = deg v_m(P^3) = m^3   (m=3 -> 27, m=4 -> 64)

kk = ZZ/32003;
m = value getenv "MMPVERONESE";
timeIt = (label,f) -> (
    t0 := cpuTime(); r := f();
    print("    " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio; r);

SP3 = kk[x0,x1,x2,x3];
mons = first entries basis(m,SP3);
T = kk[y_1..y_(#mons)];
J = timeIt("Veronese イデアル",() -> ker map(SP3,T,mons));
R = T/J;
d = dim R;
print("=== v_" | toString m | "(P^3):  変数 " | toString numgens T
    | ",  codim " | toString codim J | ",  dim " | toString d | " ===");
flush stdio;

thetas = timeIt("斉次パラメータ系",() -> (
    cand := apply(d,i -> random(1,R));
    if dim(R/ideal cand) != 0 then error "not a system of parameters";
    cand));
Rbar = timeIt("Artin 剰余 R/(theta)",() -> R/ideal thetas);
bas = timeIt("その k 基底",() -> basis Rbar);
print("    dim_k R/(theta) = " | toString numcols bas
    | "   (理論値 deg = " | toString (m^3) | ")");
print("    基底の次数分布 = " | toString tally flatten flatten degrees source bas);
flush stdio;
print "=== 完了 ===";
