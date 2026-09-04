-- 「projective normality は本当に必要か」の決定実験.
--
-- X = P^3 を O(2) で P^9 に埋める (= 2 重 Veronese, 正規 = projectively normal).
-- そこから一般の点を中心に 2 回同型射影して P^7 に落とす.  像は X と同型
-- (Hilbert 多項式一致 = coker 有限長 = 閉埋め込み) だが, 斉次座標環は非正規.
--
-- その非正規表示に threefoldMMPData をかけ, 正規表示と同じ答えが出るかを見る.
--   出る   -> 正規性は実は不要.  線形射影が使える (P^34 -> P^7 級の削減).
--   出ない -> どこが壊れるかが分かる (切断の数え落とし = 不完全線形系のはず).

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");

timeIt = (label,f) -> (
    t0 := cpuTime();
    r := f();
    print("    " | label | ":  " | toString(cpuTime()-t0) | " s"); flush stdio;
    r);

-- 点 (-c_0 : ... : -c_(n-2) : 1) を中心とする射影:  y_i -> y_i + c_i*y_last の
-- あと y_last を消去.  変数変換が二項式なので疎さを壊さない.
projectFromGeneralPoint = (T,J) -> (
    n := numgens T;
    last := T_(n-1);
    subs := apply(n-1,i -> T_i + random(-5,5)*last);
    phi := map(T,T,matrix{subs | {last}});
    Jmoved := phi J;
    Jelim := eliminate(last,Jmoved);
    T' := (coefficientRing T)[take(gens T,n-1)];
    into := map(T',T,(vars T') | matrix{{0_T'}});
    (T',into Jelim)
    );

describe' = (name,T,J) -> (
    R := T/J;
    print("  " | name | ":  変数 " | toString numgens T
        | ",  極小生成元 " | toString numgens trim J
        | ",  dim " | toString dim R
        | ",  Hilbert 多項式 " | toString hilbertPolynomial(R,Projective=>false));
    flush stdio;
    R);

runDriver = (name,R) -> (
    print("--- driver on " | name | " ---"); flush stdio;
    idx := timeIt("canonicalIndexData",() -> canonicalIndexData(R,CanonicalIndexSearchLimit=>6));
    print("    conclusive = " | toString idx#"conclusive"); flush stdio;
    if not idx#"conclusive" then return;
    a := idx#"index";
    print("    canonical index = " | toString a); flush stdio;
    contr := timeIt("canonicalContractionData",() -> canonicalContractionData(R,a));
    print("    contractionType   = " | toString contr#"contractionType");
    print("    sourceDimension   = " | toString contr#"sourceDimension");
    print("    targetDimension   = " | toString contr#"targetDimension");
    flush stdio;
    mmp := timeIt("threefoldMMPData",() -> threefoldMMPData(R,a));
    print("    terminationType = " | toString mmp#"terminationType"
        | ",  steps = " | toString mmp#"numberOfSteps");
    flush stdio;
    );

SP3 = QQ[x0,x1,x2,x3];
mons = first entries basis(2,SP3);
T9 = QQ[y_1..y_(#mons)];
J9 = ker map(SP3,T9,mons);

print "=== 正規表示 (2 重 Veronese in P^9) ===";
R9 = describe'("P^9",T9,J9);

print "";
print "=== 同型射影で落とす ===";
(T8,J8) = projectFromGeneralPoint(T9,J9);
R8 = describe'("P^8 への射影像",T8,J8);
print("  閉埋め込みの証明書 (Hilbert 多項式一致) ?  "
    | toString (hilbertPolynomial(R9,Projective=>false)
        == hilbertPolynomial(R8,Projective=>false)));
flush stdio;

(T7,J7) = projectFromGeneralPoint(T8,J8);
R7 = describe'("P^7 への射影像",T7,J7);
print("  閉埋め込みの証明書 (Hilbert 多項式一致) ?  "
    | toString (hilbertPolynomial(R9,Projective=>false)
        == hilbertPolynomial(R7,Projective=>false)));
flush stdio;

print "";
runDriver("正規表示 P^9 (10 変数)",R9);
print "";
runDriver("非正規表示 P^7 (8 変数)",R7);

print "";
print "=== 正規性 (最後に:  isNormal は重いことがある) ===";
print("  P^9 表示 (2 重 Veronese):  正規 " | toString isNormal R9); flush stdio;
print("  P^7 表示 (射影像):          正規 " | toString isNormal R7); flush stdio;

print "";
print "=== 完了 ===";
