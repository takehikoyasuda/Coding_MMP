-- canonicalIndexData(Xminus, limit 12) が conclusive=false を返した.
-- 指数が本当に 12 超なのか, それとも Cartier 判定が汎用の遅い経路に
-- 落ちているだけなのかを分ける.
--
-- canonicalIndexData の isCartierAtIndex は 3 段:
--   1. principalShiftCartierCertificateInternal(m*K)   (証明書, true か null)
--   2. canonicalIdealSeedInvertibleInternal(R,K,m)     (seed の反射的べき)
--   3. B があれば isCartierSaturatedInternal, なければ isCartier
-- 今回 B を渡していなかったので 3 は毎回 WeilDivisors の汎用 isCartier.
-- K は一度だけ作り (13-19 分), 各段を m ごとに計る.

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
br = sum apply(take(flatten entries vars Tq,#HB0+1),q -> q^4);
Wc = Tq/(sub(I0,Tq)+ideal(c^4-br));
Gm = b2mToGraphMorphism(
    bigradedReesProjection ideal(2*canonicalDivisor(Wc,IsGraded=>true)),Verbose=>false);
Xq = minimalPresentation Gm#sourceRing;
kk = ZZ/32003;
Ax = ambient Xq; AmbP = kk[gens Ax];
R = AmbP/sub(ideal Xq,AmbP);
print("Xminus:  変数 " | toString numgens ambient R
    | ",  codim " | toString (dim ambient R - dim R));
flush stdio;

dict = MMPComputation#"private dictionary";
kdivFn = value(dict#"mmpCanonicalDivisorInternal");
princFn = value(dict#"principalShiftCartierCertificateInternal");
seedInvFn = value(dict#"canonicalIdealSeedInvertibleInternal");
satFn = value(dict#"isCartierSaturatedInternal");

K = timeIt("mmpCanonicalDivisorInternal",() -> kdivFn R);
B = ideal vars R;
print("  B = ideal vars R  (単一次数なので無関係イデアルはこれ)");
flush stdio;

-- 段 2 が false を返しても段 3 を必ず走らせ, 食い違うかを見る.
-- canonicalIndexData は段 2 の false をそのまま判定にするので, もし
-- 食い違えば「certificates can only return true or null, never false」という
-- 自身のコメントの不変条件が破れていることになる.
for m from 1 to 6 do (
    print("--- m = " | toString m | " ---"); flush stdio;
    D := m*K;
    p := timeIt("  1. principalShift 証明書",() -> princFn D);
    print("     -> " | toString p); flush stdio;
    s2 := timeIt("  2. seed 反射的べき (単項イデアルか)",() -> seedInvFn(R,K,m));
    print("     -> " | toString s2); flush stdio;
    t3 := timeIt("  3. isCartierSaturated (B つき, 本来の判定)",() -> satFn(D,B));
    print("     -> " | toString t3); flush stdio;
    if s2 =!= null and s2 =!= t3 then
        print("  *** 食い違い:  seed = " | toString s2
            | " だが 本来の判定 = " | toString t3 | " ***");
    if t3 then (print("*** 指数 = " | toString m); break);
    );
print "=== 完了 ===";
