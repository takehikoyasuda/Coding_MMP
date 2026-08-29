-- de-Veronese による埋め込み次元削減:  既知の答えがある小例での検証.
--
-- 主張: X = Proj R の座標環を固定したまま変数を減らすことはできない
-- (変数の最小個数 = mu(R_+) は R の不変量).  正規性 = 同型を保って
-- 埋め込み次元を落とす唯一の道は偏極 w を割ること:  w = m*A ならば
-- R(w) = R(A)^(m) であり, Veronese 部分環は生成元を爆発させる.
--
-- Part 1 は 4 つの既知例で "R(A) -> R(A)^(m)" の爆発量を測る.
-- Part 4 は同じ 3-fold の 2 通りの表示で threefoldMMPData の時間を比べる.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");

stamp = label -> (print(label | "  cpu=" | toString cpuTime()); flush stdio);

-- R(A)^(m) を A の斉次座標環から直接作る:  次数 m の単項式基底で張られる
-- 部分代数の表示 = その parametrization の核.
veroneseSubring = (SA,IA,m,varname) -> (
    A := SA/IA;
    basisMatrix := basis(m,A);
    gensList := first entries basisMatrix;
    n := #gensList;
    T := (coefficientRing SA)[varname_1..varname_n];
    J := ker map(A,T,gensList);
    (T,J,n)
    );

report = (name,ambientCount,idealGens,codimValue) -> (
    print("  " | name
        | ":  変数 " | toString ambientCount
        | ",  極小生成元 " | toString idealGens
        | ",  codim " | toString codimValue);
    flush stdio);

presentationSize = (T,J) -> (
    Jt := trim J;
    (numgens T, if Jt == 0 then 0 else numgens Jt, if Jt == 0 then 0 else codim Jt)
    );

print "=== Part 1:  de-Veronese の効き方 (既知の答えがある小例) ===";

-- (A) P^1:  A = O(1) は 2 変数 0 式.  m 次 Veronese = 有理正規曲線 in P^m.
print "";
print "(A) X = P^1,  A = O(1)";
SP1 = QQ[s,t];
report("A 自身 (P^1)",numgens SP1,0,0);
for m in {2,3,4} do (
    (T,J,n) := veroneseSubring(SP1,ideal(0_SP1),m,getSymbol "u");
    (nv,ng,cd) := presentationSize(T,J);
    report("m = " | toString m | " (有理正規 " | toString m | " 次曲線)",nv,ng,cd);
    );

-- (B) P^2:  m=2 が Veronese 曲面 in P^5.
print "";
print "(B) X = P^2,  A = O(1)";
SP2 = QQ[x,y,z];
report("A 自身 (P^2)",numgens SP2,0,0);
for m in {2,3} do (
    (T,J,n) := veroneseSubring(SP2,ideal(0_SP2),m,getSymbol "v");
    (nv,ng,cd) := presentationSize(T,J);
    report("m = " | toString m,nv,ng,cd);
    );

-- (C) P(1,1,2):  重み付きだと 3 変数 0 式.  O(2) で埋めると P^3 内の二次錐.
print "";
print "(C) X = P(1,1,2) (重み付き: 3 変数 0 式)";
SW = QQ[u,v,w0,Degrees=>{1,1,2}];
report("A 自身 (P(1,1,2), O(1) は very ample でない)",numgens SW,0,0);
(TW,JW,nW) = veroneseSubring(SW,ideal(0_SW),2,getSymbol "q");
(nvW,ngW,cdW) = presentationSize(TW,JW);
report("m = 2 (P^3 内の二次錐)",nvW,ngW,cdW);

-- (D) 負のコントロール:  Segre P^1 x P^2 の O(1,1) は Pic = Z^2 で原始的
--     なので割れない.  m = 1 のまま.
print "";
print "(D) 負のコントロール:  Segre P^1 x P^2 in P^5,  O(1,1) は原始的";
SSeg = QQ[z00,z01,z02,z10,z11,z12];
ISeg = minors(2,matrix{{z00,z01,z02},{z10,z11,z12}});
(nvS,ngS,cdS) = presentationSize(SSeg,ISeg);
report("そのまま (割れない)",nvS,ngS,cdS);

stamp("Part 1 done");

print "";
print "=== Part 2:  常に安全な操作 = 冗長生成元の消去 (minimalPresentation) ===";
-- わざと冗長な変数を足した表示を作り, minimalPresentation が元に戻すことを確認.
SRed = QQ[a,b,c,d];
IRed = ideal(d - a*0 - b);          -- d = b:  d は冗長
Rred = SRed/IRed;
print("  冗長な表示:  変数 " | toString numgens SRed);
print("  minimalPresentation 後:  変数 "
    | toString numgens ambient minimalPresentation Rred);
stamp("Part 2 done");

print "";
print "=== Part 3:  非正規性の確認 (線形射影が壊すもの) ===";
-- 有理正規 4 次曲線を P^3 に同型射影する.  像は元と同型 (Hilbert 多項式が
-- 一致 = coker が有限長 = 閉埋め込み) だが, 座標環は正規性を失う.
(T4,J4,n4) = veroneseSubring(SP1,ideal(0_SP1),4,getSymbol "yy");
-- ランダムな中心からの射影 = 一般線形座標変換のあと最後の変数を消去.
g = random(QQ^n4,QQ^n4);
J4moved = ideal apply(first entries gens J4, f -> sub(f,(vars T4) * g));
J4elim = eliminate(T4_(n4-1),J4moved);
-- 消去した変数を落として, 本当に P^3 の中で見る.
T3 = QQ[zz_1..zz_(n4-1)];
intoT3 = map(T3,T4,(vars T3) | matrix{{0_T3}});
J4proj = intoT3 J4elim;
hpSource = hilbertPolynomial(T4/J4,Projective=>false);
hpImage  = hilbertPolynomial(T3/J4proj,Projective=>false);
print("  P^4 内の有理正規 4 次曲線:  Hilbert 多項式 = " | toString hpSource);
print("  P^3 への射影像:              Hilbert 多項式 = " | toString hpImage);
print("  一致 (= coker 有限長 = 閉埋め込みの証明書) ?  "
    | toString (hpSource == hpImage));
print("  元の環は正規か ?      " | toString isNormal(T4/J4));
print("  射影像の環は正規か ?  " | toString isNormal(T3/J4proj));
stamp("Part 3 done");

print "";
print "=== 完了 ===";
