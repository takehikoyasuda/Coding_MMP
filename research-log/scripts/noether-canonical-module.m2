-- Noether データから omega_R を R 加群として組み立て, canonicalDivisor の
-- 答えと突き合わせる.
--
--   R = ⊕_i A e_i  (A = k[theta], 自由, 階数 rank0)
--   x_j e_i = Σ_l c_{li} e_l                       (掛け算行列)
--   omega = Hom_A(R, A(-d)) は双対基底 f_i を持ち, deg f_i = d - a_i,
--   x_j f_l = Σ_i c_{li} f_i                       (転置)
--   よって omega = coker N,  N の (j,l) 列は  x_j g_l - Σ_i c_{li} g_i.
--
-- 実装上の要が二つ.
--   (1) theta を「一般線形形式」ではなく座標変換で実際の変数 4 本にしておく.
--       そうしないと c_{li}(theta) が密な高次式に展開される.
--   (2) その座標変換は内部的な都合でしかないので, omega を組んだあとに
--       元の (疎な) 座標へ戻す.  線形変換は環同型なので, 関係式行列の成分に
--       逆置換をかけるだけ.  戻さないと divisor/embedAsIdeal が稠密座標の上で
--       走ることになり, 10 変数の小例ですら 19 分で返らない.
--
-- MMPTARGET = veronese2 | xminus

needsPackage("MMPComputation",FileName=>"MMPComputation.m2");
needsPackage "Polyhedra"; needsPackage "WeilDivisors"; needsPackage "NormalToricVarieties";

tgt = getenv "MMPTARGET";
kk = ZZ/32003;
timeIt = (l,f) -> (t0:=cpuTime(); r:=f();
    print("  " | l | ":  " | toString(cpuTime()-t0) | " s"); flush stdio; r);

buildRing = () -> (
    if tgt == "veronese2" then (
        SP := kk[x0,x1,x2,x3]; T := kk[y_1..y_10];
        T/(ker map(SP,T,first entries basis(2,SP))))
    else (
        rayList := {{1,0,0},{0,1,0},{0,0,1},{1,1,-2}};
        HB0 := apply(hilbertBasis dualCone coneFromVData transpose matrix rayList,
            v -> flatten entries v);
        L := QQ[t1,t2,t3]; S0 := QQ[y_1..y_(#HB0)];
        I0 := ker map(L,S0,apply(HB0,h -> t1^(h#0)*t2^(h#1)*t3^(h#2)));
        Tq := QQ[y_1..y_(#HB0),w,c];
        br := sum apply(take(flatten entries vars Tq,#HB0+1),q -> q^4);
        Wc := Tq/(sub(I0,Tq)+ideal(c^4-br));
        Gm := b2mToGraphMorphism(
            bigradedReesProjection ideal(2*canonicalDivisor(Wc,IsGraded=>true)),
            Verbose=>false);
        Xq := minimalPresentation Gm#sourceRing;
        Ax := ambient Xq; AmbP := kk[gens Ax];
        AmbP/sub(ideal Xq,AmbP)));

R0 = timeIt("環の構成",buildRing);
Amb0 = ambient R0; n = numgens Amb0; d = dim R0;
print("=== " | tgt | ":  変数 " | toString n | ",  dim " | toString d | " ===");
flush stdio;

-- theta を「最後の d 変数」にする座標変換.
gl = random(kk^n,kk^n);
while det gl == 0 do gl = random(kk^n,kk^n);
fwd0 = map(Amb0,Amb0,(vars Amb0)*gl);
R = timeIt("一般線形座標変換 (theta = 最後の " | toString d | " 変数)",
    () -> Amb0/(fwd0 ideal R0));
-- 逆置換:  R -> R0.  omega を元の疎な座標へ戻すのに使う.
backToR0 = map(R0,R,first entries ((vars R0) * (inverse gl)));
vs = flatten entries vars R;
thetas = take(vs,{n-d,n-1});

Rbar = timeIt("Artin 剰余",() -> R/ideal thetas);
basBar = timeIt("A 基底  [返れば theta は hsop]",() -> first entries basis Rbar);
es = apply(basBar, m -> sub(m,R));
as = apply(basBar, m -> first degree m);
rank0 = #es;
print("  階数 = " | toString rank0 | ",  次数分布 " | toString tally as);
flush stdio;

basisCache = new MutableHashTable;
degBasis = m -> (if not basisCache#?m then basisCache#m = basis(m,R); basisCache#m);
Apoly = kk[tt_1..tt_d];
thetaMonos = e -> if e < 0 then {} else first entries basis(e,Apoly);
toR = q -> product apply(d, i -> thetas#i ^ ((exponents q)#0#i));
coordsBatch = (fs,m) -> (if #fs == 0 then map(kk^0,kk^0,0)
    else lift(last coefficients(matrix{fs}, Monomials => degBasis m), kk));

maxDeg = max as + 1;
basisMatrix = new MutableHashTable;
timeIt("次数 0.." | toString maxDeg | " の基底変換",() -> (
    for m from 0 to maxDeg do (
        elts := {};
        for i from 0 to rank0-1 do
            for q in thetaMonos(m - as#i) do elts = append(elts,(toR q) * es#i);
        basisMatrix#m = coordsBatch(elts,m));
    true));

-- c_{li}:  x_j e_i = Σ_l c_{li} e_l.  A 係数を Apoly で持つ.
cmat = timeIt("掛け算行列 (次数ごとに一括)",() -> (
    out := new MutableHashTable;
    for m from 1 to maxDeg do (
        prods := {}; keysm := {};
        for j from 0 to (#vs)-1 do for i from 0 to rank0-1 do
            if as#i + 1 == m then (
                prods = append(prods, vs#j * es#i); keysm = append(keysm,{j,i}));
        if #prods > 0 then (
            V := solve(basisMatrix#m, coordsBatch(prods,m));
            N := #keysm; rowsSoFar := 0; blocks := {};
            for l from 0 to rank0-1 do (
                ml := thetaMonos(m - as#l);
                if #ml == 0 then blocks = append(blocks, map(Apoly^1,Apoly^N,0))
                else (blocks = append(blocks,
                        (matrix{ml}) * sub(V^(toList(rowsSoFar..rowsSoFar+(#ml)-1)),Apoly));
                    rowsSoFar = rowsSoFar + #ml));
            M := fold(blocks,(a,b) -> a||b);
            for p from 0 to N-1 do out#(keysm#p) = M_{p}));
    out));

-- omega = coker N.  生成元 g_l の次数は d - a_l.
toRing = map(R,Apoly,thetas);
Nmat = timeIt("関係式行列 N (" | toString rank0 | " x " | toString (#vs * rank0) | ")",() -> (
    cols := {};
    for j from 0 to (#vs)-1 do
        for l from 0 to rank0-1 do (
            col := new MutableList from toList(rank0 : 0_R);
            for i from 0 to rank0-1 do
                if cmat#?{j,i} then (
                    cc := (cmat#{j,i})_(l,0);
                    if cc != 0 then col#i = col#i - toRing cc);
            col#l = col#l + vs#j;
            cols = append(cols, transpose matrix {toList col}));
    fold(cols,(a,b) -> a|b)));

omegaDeg = apply(as, a -> a - d);          -- 生成元 g_l は次数 d - a_l
-- 元の疎な座標に戻してから omega を作る.
Nmat0 = timeIt("N を元の座標へ戻す",() -> backToR0 Nmat);
omega = timeIt("omega = coker N  (元の座標)",() -> (
    F := R0^omegaDeg;
    coker map(F, , Nmat0)));
print("  omega:  生成元 " | toString numgens omega); flush stdio;
omegaMin = timeIt("極小化",() -> minimalPresentation omega);
print("  極小生成元 " | toString numgens omegaMin
    | ",  次数 " | toString tally flatten flatten degrees omegaMin);
flush stdio;
print("  Hilbert 関数 (0..5) = "
    | toString apply(toList(0..5), i -> hilbertFunction(i,omegaMin)));
flush stdio;

-- 突き合わせ:  Hilbert 関数は理論値と既に一致しているので, ここでは
-- divisor(omega) が既存の canonicalDivisor(R) と線形同値かだけを見る.
-- (Ext 加群の hilbertFunction は密な座標だと自由分解を要求して重く,
--  検証としては冗長なので取らない.)
if tgt == "veronese2" then (
    expected := apply(toList(0..5), i -> binomial(2*i-4+3,3));
    expected = apply(toList(0..5), i -> if 2*i-4 < 0 then 0 else binomial(2*i-4+3,3));
    print("  理論値 h^0(O(2d-4)) (0..5) = " | toString expected);
    print("  一致 ?  " | toString (
        apply(toList(0..5), i -> hilbertFunction(i,omegaMin)) == expected));
    flush stdio;
    K1 := timeIt("divisor(omega)  [Noether 版]",() -> divisor(omegaMin,IsGraded=>true));
    K2 := timeIt("canonicalDivisor(R0)  [既存]",() -> canonicalDivisor(R0,IsGraded=>true));
    print("  Noether 版 K = " | toString K1);
    print("  既存の    K = " | toString K2);
    print("  線形同値か ?  " | toString (isLinearEquivalent(K1,K2)));
    );
flush stdio;
print "=== 完了 ===";
