-- 「非正規表示で driver が止まるのは (a) 非正規性のせいか (b) 係数膨張のせいか」
-- の切り分け.  環境変数 MMPCASE (A/B/C) と MMPFIELD (QQ/GFP) で 1 セルを走らせる.
--
--   A: P^3 の 2 重 Veronese in P^9 をそのまま        10 変数, 正規,   係数疎
--   B: A に C と同じ座標変換だけ掛ける (消去しない)  10 変数, 正規,   係数密
--   C: さらに 2 回消去して P^7 へ                     8 変数, 非正規, 係数密
--
-- 決定的なのは C/GFP:  有限体では係数膨張が起きないので, そこでも遅ければ
-- 原因は非正規性 (構造的), 速ければ原因は QQ の係数膨張.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "WeilDivisors";

caseName  = getenv "MMPCASE";
fieldName = getenv "MMPFIELD";
kk = if fieldName == "GFP" then ZZ/32003 else QQ;

timeIt = (label,f) -> (
    t0 := cpuTime();
    r := f();
    print("    " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio;
    r);

-- QQ と GF(p) で同一の変換を使うため, 係数は決め打ちにする.
shift1 = {3,-2,1,4,-5,2,-1,3,5};       -- 9 個:  y_1..y_9 -> y_i + c_i*y_10
shift2 = {-4,1,5,-3,2,-1,4,-2};        -- 8 個:  y_1..y_8 -> y_i + c_i*y_9

changeCoords = (T,shifts) -> (
    n := numgens T;
    lastVar := T_(n-1);
    map(T,T,matrix{apply(n-1,i -> T_i + shifts#i * lastVar) | {lastVar}})
    );

dropLastVar = (T,J) -> (
    n := numgens T;
    T' := kk[take(gens T,n-1)];
    into := map(T',T,(vars T') | matrix{{0_T'}});
    (T',into J)
    );

print("=== case " | caseName | " over " | fieldName | " ===");
flush stdio;

SP3 = kk[x0,x1,x2,x3];
mons = first entries basis(2,SP3);
T10 = kk[y_1..y_(#mons)];
(T,J) = timeIt("build (ker of the Veronese parametrization)",() -> (
    J0 := ker map(SP3,T10,mons);
    if caseName == "A" then (T10,J0)
    else (
        J1 := (changeCoords(T10,shift1)) J0;
        if caseName == "B" then (
            -- 座標変換だけ:  A と環同型 (正規) だが係数は C と同程度に密.
            J2 := (changeCoords(T10,shift2 | {0})) J1;
            (T10,J2)
            ) else (
            -- C:  2 回消去して 8 変数へ.
            E1 := eliminate(T10_(numgens T10 - 1),J1);
            (T9,J9) := dropLastVar(T10,E1);
            J9b := (changeCoords(T9,shift2)) J9;
            E2 := eliminate(T9_(numgens T9 - 1),J9b);
            dropLastVar(T9,E2)
            )
        )
    ));

R = T/J;
print("  変数 " | toString numgens T
    | ",  極小生成元 " | toString numgens trim J
    | ",  dim " | toString dim R);
print("  Hilbert 多項式 " | toString hilbertPolynomial(R,Projective=>false));
flush stdio;

K = timeIt("canonicalDivisor",() -> canonicalDivisor(R,IsGraded=>true));
idx = timeIt("canonicalIndexData(limit 2)",
    () -> canonicalIndexData(R,CanonicalIndexSearchLimit=>2));
print("  conclusive = " | toString idx#"conclusive"
    | (if idx#"conclusive" then ",  index = " | toString idx#"index" else ""));
flush stdio;

print("  正規か ?  " | toString isNormal R); flush stdio;
print("=== case " | caseName | "/" | fieldName | " 完了 ===");
