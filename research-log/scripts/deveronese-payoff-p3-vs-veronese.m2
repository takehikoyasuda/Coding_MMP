-- 同じ 3-fold (P^3) を 2 通りの正規な斉次座標環で表示し, driver の時間を比べる.
--   (a) 極小表示:            4 変数, 0 式        (A = O(1))
--   (b) 2 重 Veronese:      10 変数, codim 6    (w = O(2) = 2A)
-- どちらも正規 = projectively normal なので, パッケージの仮定を満たしたまま
-- "偏極を割る" ことの効果だけを測れる.

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");

timeIt = (label,f) -> (
    t0 := cpuTime();
    r := f();
    print("  " | label | ":  " | toString(cpuTime()-t0) | " s");
    flush stdio;
    r);

runDriver = (name,R) -> (
    print("--- " | name | " ---");
    print("  変数 " | toString numgens ambient R
        | ",  極小生成元 " | toString (if ideal R == 0 then 0 else numgens trim ideal R)
        | ",  正規 " | toString isNormal R);
    flush stdio;
    idx := timeIt("canonicalIndexData",() -> canonicalIndexData(R,CanonicalIndexSearchLimit=>6));
    if not idx#"conclusive" then (print "  index inconclusive"; return);
    a := idx#"index";
    print("  canonical index = " | toString a);
    nef := timeIt("canonicalNefData",() -> canonicalNefData(R,a));
    print("  nef = " | toString nef#"nef");
    mmp := timeIt("threefoldMMPData",() -> threefoldMMPData(R,a));
    print("  terminationType = " | toString mmp#"terminationType"
        | ",  steps = " | toString mmp#"numberOfSteps");
    flush stdio;
    );

SP3 = QQ[x0,x1,x2,x3];
runDriver("(a) P^3, A = O(1):  4 変数",SP3);

print "";
mons = first entries basis(2,SP3);
TV = QQ[yv_1..yv_(#mons)];
JV = ker map(SP3,TV,mons);
RV = TV/JV;
runDriver("(b) P^3, w = O(2):  P^9 内 2 重 Veronese",RV);

print "";
print "=== 完了 ===";
