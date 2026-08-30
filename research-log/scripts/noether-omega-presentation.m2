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
-- 座標変換 (theta を実際の変数にする) は関係式行列を R 上で疎に保つための
-- もので, Xminus では 1982 秒かかる.  生成元が 5 個に落ちた今は関係式が
-- 数本しかないので密度は問題にならず, 既定では行わない (MMPCOORD=on で有効).
useCoord = (getenv "MMPCOORD") == "on";
R = (if useCoord then (
        timeIt("一般線形座標変換 (theta = 最後の " | toString d | " 変数)",() -> (
            gl := random(kk^n,kk^n);
            while det gl == 0 do gl = random(kk^n,kk^n);
            Amb0/((map(Amb0,Amb0,(vars Amb0)*gl)) ideal R0)))
        ) else R0);
vs = flatten entries vars R;
thetas = (if useCoord then (
        take(vs,{n-d,n-1})
        ) else (
        timeIt("一般線形形式 " | toString d | " 本",() -> apply(d,i -> random(1,R)))
        ));

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

-- ここから: 関係式行列 (124 x 3596) を作る前に, omega の R 上の極小生成元を
-- k 上の線形代数だけで求める.
--
--   m*omega = sum_j x_j*omega,  theta_i は変数そのものなので
--   theta_i*omega = t_i*omega ⊆ (t)*omega.  よって
--
--       omega/m*omega = k^rank0 / sum_{j: theta 以外} colspace(T_j mod t)
--
--   T_j = C_j^T,  (C_j)_{l,i} = c_{li}  (x_j e_i = Σ_l c_{li} e_l).
--   同時に C_{theta_i} = t_i * I  (theta 由来の関係式が恒等的に 0) も検算する.

toK = map(kk,Apoly,toList(d:0_kk));

Cmatrix = j -> (
    cols := apply(rank0, i -> if cmat#?{j,i} then cmat#{j,i}
        else map(Apoly^rank0,Apoly^1,0));
    fold(cols,(a,b) -> a|b));

thetaIdx = if useCoord then toList((#vs-d)..(#vs-1)) else {};
if useCoord then (
    print "  [theta 由来の関係式が自明か検算]";
    okTheta := timeIt("C_{theta_i} = t_i * I か",() -> (
        all(d, s -> (
            j := thetaIdx#s;
            entries Cmatrix(j) == entries ((Apoly_s) * id_(Apoly^rank0))))));
    print("    " | toString okTheta);
    flush stdio;
    );
nonTheta = select(toList(0..(#vs)-1), j -> not member(j,thetaIdx));
gensData = timeIt("omega/m*omega  (k 上の線形代数)",() -> (
    blocks := apply(nonTheta, j -> toK transpose Cmatrix(j));
    B := fold(blocks,(a,b) -> a|b);
    r := rank B;
    {B, r, rank0 - r}));
print("    stack した行列 = " | toString rank0 | " x "
    | toString (#nonTheta * rank0)
    | ",  rank " | toString (gensData#1));
print("    dim omega/m*omega = " | toString (gensData#2)
    | "   ( = R 上の極小生成元の個数 )");
flush stdio;

-- 生成元を次数ごとに明示的なベクトルとして取り出す.
degF = apply(as, a -> d - a);                 -- f_l の次数
Bfull = gensData#0;
genVecs = timeIt("生成元ベクトルを取り出す",() -> (
    acc := {};
    for g in sort unique degF do (
        rows := select(toList(0..rank0-1), l -> degF#l == g);
        subB := Bfull^rows;
        mg := mingens coker subB;
        for c from 0 to (numcols mg)-1 do (
            v := new MutableList from toList(rank0 : 0_kk);
            for r from 0 to (#rows)-1 do v#(rows#r) = mg_(r,c);
            acc = append(acc,{g,toList v})));
    acc));
print("    生成元 " | toString (#genVecs) | " 個,  次数 "
    | toString tally apply(genVecs, p -> p#0));
flush stdio;

-- psi: R^5 -> omega を A 加群の写像 A^(rank0*#gens) -> A^rank0 として作る.
-- 列は e_i * w_k で, T_j の行列・ベクトル積を高々 max(a_i) 回繰り返すだけ.
Tcache = new MutableHashTable;
Tmat = j -> (if not Tcache#?j then Tcache#j = transpose Cmatrix(j); Tcache#j);
expOf = i -> (exponents basBar#i)#0;

psiMat = timeIt("psi の行列 (e_i * w_k)",() -> (
    cols := {};
    for pr in genVecs do (
        w0 := sub(transpose matrix {pr#1}, Apoly);
        for i from 0 to rank0-1 do (
            v := w0;
            ev := expOf i;
            for j from 0 to (#vs)-1 do
                for c from 1 to ev#j do v = (Tmat j) * v;
            cols = append(cols,v)));
    fold(cols,(a,b) -> a|b)));
print("    psi の大きさ = " | toString numrows psiMat | " x " | toString numcols psiMat);
flush stdio;

-- 次数付き写像にして核を取る (4 変数環上の syzygy 計算).
srcDeg = flatten apply(genVecs, pr -> apply(as, a -> -(a + pr#0)));
tgtDeg = apply(degF, g -> -g);
psiMap = map(Apoly^tgtDeg, Apoly^srcDeg, psiMat);
Kmod = timeIt("ker psi  (A = k[t_1.." | toString d | "] 上)",() -> ker psiMap);
Ksyz = gens Kmod;
kdegs = apply(degrees source Ksyz, dg -> first dg);
print("    A 上の関係式 " | toString numcols Ksyz | " 本"
    | "   (rank = " | toString (numcols psiMat) | " - " | toString rank0
    | " = " | toString (numcols psiMat - rank0) | " なので A 上は極小)");
print("    次数分布 = " | toString tally kdegs);
flush stdio;

-- R 上で極小化する.  生成元のときと同じ k 上の線形代数を一段上に適用する.
-- K は自由 (psi 全射 + A^rank0 自由 -> 列が分裂) なので Ksyz は自由基底で,
-- K/(t)K -> A^src/(t) は単射.  よって x_j の K 上の作用行列は
--     X_j mod t = solve(K0, (C_j^{(ng)} mod t) K0),   K0 = Ksyz mod t
-- で k 上だけで求まる.  そして
--     Rel/m*Rel = k^496 / Σ_j colspace(X_j mod t).
ng = #genVecs;
nsyz = numcols Ksyz;
K0 = toK Ksyz;
blockC = j -> (
    Cj := toK Cmatrix(j);
    zz := map(kk^rank0,kk^rank0,0);
    matrix apply(ng, a -> apply(ng, b -> if a == b then Cj else zz)));
Xmats = timeIt("x_j の K 上の作用 (k 上, " | toString (#vs) | " 本)",
    () -> apply(#vs, j -> ((blockC j) * K0) // K0));
if nsyz > 0 then (
    exact := all(#vs, j -> (blockC j) * K0 == K0 * (Xmats#j));
    print("    除算が厳密か (C_j^{(ng)} K0 = K0 X_j) ?  " | toString exact);
    flush stdio;
    );
relData = timeIt("Rel/m*Rel  (k 上の線形代数)",() -> (
    B2 := fold(Xmats,(a,b) -> a|b);
    {B2, rank B2, nsyz - rank B2}));
print("    stack した行列 = " | toString nsyz | " x " | toString (#vs * nsyz)
    | ",  rank " | toString (relData#1));
print("    dim Rel/m*Rel = " | toString (relData#2)
    | "   ( = R 上の極小関係式の本数 )");
flush stdio;

-- 次数ごとに極小関係式のベクトルを取り出す.
B2 = relData#0;
relVecs = timeIt("極小関係式ベクトル",() -> (
    acc := {};
    for g in sort unique kdegs do (
        rows := select(toList(0..nsyz-1), r -> kdegs#r == g);
        mg := mingens coker (B2^rows);
        for c from 0 to (numcols mg)-1 do (
            v := new MutableList from toList(nsyz : 0_kk);
            for r from 0 to (#rows)-1 do v#(rows#r) = mg_(r,c);
            acc = append(acc,{g,toList v})));
    acc));
print("    極小関係式 " | toString (#relVecs) | " 本,  次数 "
    | toString tally apply(relVecs, pr -> pr#0));
flush stdio;

Kred = (if #relVecs == 0 then map(Apoly^(numrows Ksyz),Apoly^0,0)
    else Ksyz * sub(fold(apply(relVecs, pr -> transpose matrix {pr#1}),
        (a,b) -> a|b), Apoly));
Ksyz = Kred;
print("    縮約後の関係式行列 (A 上) = " | toString numrows Ksyz
    | " x " | toString numcols Ksyz);
flush stdio;

-- 各関係式を R^(#gens) の元に変換.  スロット k は Σ_i v_(i,k)(t) e_i.
toRfromA = map(R,Apoly,thetas);
relMat = timeIt("関係式を R 上へ",() -> (
    ng := #genVecs;
    cols := {};
    for c from 0 to (numcols Ksyz)-1 do (
        entry := apply(ng, k -> sum apply(rank0, i ->
            (toRfromA (Ksyz_(k*rank0+i,c))) * es#i));
        cols = append(cols, transpose matrix {entry}));
    if #cols == 0 then map(R^ng,R^0,0) else fold(cols,(a,b) -> a|b)));
print("    R 上の関係式行列 = " | toString numrows relMat | " x "
    | toString numcols relMat);
flush stdio;

omegaGenDeg = apply(genVecs, pr -> -(pr#0));
omega = timeIt("omega = coker (5 生成元の表示)",
    () -> coker map(R^omegaGenDeg,,relMat));
-- 極小化は必須ではない.  Xminus では成分が密で 2900 秒かかったので既定で外す
-- (MMPMIN=on で有効).  欲しいのは Hom(omega,R) で, 非極小な表示でも計算できる.
omegaMin = (if (getenv "MMPMIN") == "on" then (
        timeIt("極小化",() -> minimalPresentation omega)
        ) else omega);
if (getenv "MMPMIN") == "on" then (
    print("    極小生成元 " | toString numgens omegaMin
        | ",  次数 " | toString tally flatten flatten degrees omegaMin);
    flush stdio;
    );

print "  [Hom(omega,R) -> 標準イデアル]"; flush stdio;
dualOmega = timeIt("Hom(omega,R)",() -> Hom(omegaMin,R^1));
hdegs = apply(degrees dualOmega, dg -> first dg);
print("    Hom の生成元 " | toString numgens dualOmega | ",  次数 " | toString tally hdegs);
flush stdio;
ord = sort apply(#hdegs, i -> {hdegs#i, i});
embedding = null; embDeg = null; canIdeal = null;
timeIt("最小次数の埋め込み",() -> (
    for pr in ord do (
        if embedding === null then (
            f := homomorphism dualOmega_(pr#1);
            J := trim ideal matrix f;
            if J != ideal 0_R then (embedding = f; embDeg = pr#0; canIdeal = J)));
    true));
if canIdeal === null then (
    print "    ** 非零の埋め込みが見つからない **";
    ) else (
    print("    埋め込み次数 e = " | toString embDeg);
    print("    標準イデアル:  生成元 " | toString numgens canIdeal
        | ",  次数 " | toString tally apply(first entries gens canIdeal,
            q -> first degree q));
    -- Hilbert 関数の突き合わせ (重い場合があるので最後に).
    hfI := timeIt("hf(I)",() ->
        apply(toList(0..6), m -> hilbertFunction(m, module canIdeal)));
    print("    hf(I)         = " | toString hfI);
    flush stdio;
    hfW := timeIt("hf(omega)",() -> apply(toList(0..6), m -> (
        if m-embDeg < 0 then 0 else hilbertFunction(m-embDeg, omegaMin))));
    print("    hf(omega(-e)) = " | toString hfW);
    print("    一致 ?  " | toString (hfI == hfW));
    );
flush stdio;
print "=== 完了 ===";
