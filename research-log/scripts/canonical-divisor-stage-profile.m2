-- canonicalDivisor は 2 段:
--     M1 = Ext^(dS-dR)(S^1/I, S^{-sum deg})     -- 自由分解を codim 段まで
--     divisor(M1 ** R, IsGraded=>true)          -- embedAsIdeal
-- case C (P^7 への射影像, depth 1) でどちらが詰まるのかを分離する.

needsPackage "WeilDivisors";
kk = ZZ/32003;
caseName = getenv "MMPCASE";

timeIt = (label,f) -> (
    t0 := cpuTime(); r := f();
    print("    " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio; r);

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
print("=== case " | caseName | ":  変数 " | toString numgens T
    | ",  codim " | toString codim J | ",  depth "
    | toString (numgens T - pdim ((ring J)^1/J)) | " ===");
flush stdio;

dS = dim T; dR = dim R;
degList = apply(first entries vars T, q -> (degree q)#0);
M1 = timeIt("段1  Ext^" | toString(dS-dR) | "(S/I, S(-" | toString(sum degList) | "))",
    () -> Ext^(dS-dR)(T^1/J, T^{-(sum degList)}));
print("    Ext の生成元数 = " | toString numgens M1); flush stdio;

M2mod = timeIt("      M1 ** R",() -> M1 ** R);
print("    R 加群としての生成元数 = " | toString numgens M2mod); flush stdio;

K = timeIt("段2  divisor(M1**R, IsGraded=>true)  [= embedAsIdeal]",
    () -> divisor(M2mod, IsGraded=>true));
print("    K = " | toString K); flush stdio;
print "=== 完了 ===";
