-- R = ⊕_i A e_i (A = k[theta_1..theta_d], e_i は Artin 剰余の基底の持ち上げ)
-- の掛け算構造を, ブロック順序の Groebner 基底 (Xminus で 2382 秒) を使わずに
-- 次数ごとの線形代数だけで作る.
--
--     R_m = ⊕_i A_{m-a_i} e_i
--
-- なので, 次数 m の k 基底の中で { theta^alpha e_i : |alpha| + a_i = m } は
-- 別の k 基底になる.  その基底変換を各 m で 1 回だけ作れば, 任意の f in R_m
-- を A 係数で書ける.  x_j e_i の次数は高々 max(a_i)+1 なので m はそこまで.
--
-- 重要な実装上の点が二つ.
--   (1) coefficients も行列解法も「要素ごと」ではなく「次数ごとに一括」.
--       要素ごとだと Xminus で 3596 回の 1275x1275 級の行列積になる.
--   (2) A 係数は R の元ではなく 4 変数多項式環 Apoly = k[t_1..t_d] の元として
--       持つ.  R (29 変数の商環) 上で積を取ると復号だけで 900 万回の環演算に
--       なり, 28 分経っても終わらない.  行は e_l ごとに連続しているので,
--       走査ではなくブロックごとの行列積で一度に片付く.
--       omega = Hom_A(R,A) を作るにも A 上の表現がそもそも必要.
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
        SP := kk[x0,x1,x2,x3];
        T := kk[y_1..y_10];
        T/(ker map(SP,T,first entries basis(2,SP)))
        ) else (
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
        Ax := ambient Xq;
        AmbP := kk[gens Ax];
        AmbP/sub(ideal Xq,AmbP)
        ));

R = timeIt("環の構成",buildRing);
d = dim R;
print("=== " | tgt | ":  変数 " | toString numgens ambient R
    | ",  dim " | toString d | " ===");
flush stdio;

thetas = timeIt("一般線形形式 " | toString d | " 本",() -> apply(d,i -> random(1,R)));
Rbar = timeIt("Artin 剰余",() -> R/ideal thetas);
basBar = timeIt("A 基底 (Artin 剰余の標準単項式)",() -> first entries basis Rbar);
es = apply(basBar, m -> sub(m,R));
as = apply(basBar, m -> first degree m);
rank0 = #es;
print("  階数 = " | toString rank0 | ",  次数分布 " | toString tally as);
flush stdio;

basisCache = new MutableHashTable;
degBasis = m -> (
    if not basisCache#?m then basisCache#m = basis(m,R);
    basisCache#m);

-- A 係数はここに住む.  theta_i <-> tt_i.
Apoly = kk[tt_1..tt_d];
thetaMonos = e -> if e < 0 then {} else first entries basis(e,Apoly);
toR = q -> product apply(d, i -> thetas#i ^ ((exponents q)#0#i));

-- 次数ごとに 1 回だけ coefficients を呼ぶ.
coordsBatch = (fs,m) -> (
    if #fs == 0 then map(kk^0,kk^0,0)
    else lift(last coefficients(matrix{fs}, Monomials => degBasis m), kk));

maxDeg = max as + 1;
basisMatrix = new MutableHashTable;   -- 次数 m の基底変換行列
rowLabels   = new MutableHashTable;   -- その列に対応する {i, theta 単項式}

timeIt("次数 0.." | toString maxDeg | " の基底変換 (一括)",() -> (
    for m from 0 to maxDeg do (
        elts := {}; lbls := {};
        for i from 0 to rank0-1 do
            for q in thetaMonos(m - as#i) do (
                elts = append(elts, (toR q) * es#i);
                lbls = append(lbls, {i,q}));
        M := coordsBatch(elts,m);
        if #elts > 0 and numrows M != numcols M then
            error("次数 " | toString m | " で正方でない: "
                | toString numrows M | " x " | toString numcols M);
        basisMatrix#m = M; rowLabels#m = lbls);
    true));
print("  各次数の R_m の k 次元 = "
    | toString apply(toList(0..maxDeg), m -> numcols degBasis m));
flush stdio;

-- 掛け算行列.  x_j*e_i を次数ごとにまとめ, 次数ごとに 1 回だけ solve する.
vs = flatten entries vars R;
matsByDeg = timeIt("掛け算行列 " | toString (#vs) | " 本 x " | toString rank0
    | " 列 (次数ごとに一括 solve + ブロック行列積)",() -> (
    out := new MutableHashTable;
    for m from 1 to maxDeg do (
        prods := {}; keysm := {};
        for j from 0 to (#vs)-1 do
            for i from 0 to rank0-1 do
                if as#i + 1 == m then (
                    prods = append(prods, vs#j * es#i);
                    keysm = append(keysm, {j,i}));
        if #prods > 0 then (
            C := coordsBatch(prods,m);
            V := solve(basisMatrix#m, C);          -- dim R_m x N,  k 係数
            N := #keysm;
            rowsSoFar := 0;
            blocks := {};
            for l from 0 to rank0-1 do (
                ml := thetaMonos(m - as#l);
                if #ml == 0 then
                    blocks = append(blocks, map(Apoly^1,Apoly^N,0))
                else (
                    Vsub := V^(toList(rowsSoFar..rowsSoFar+(#ml)-1));
                    blocks = append(blocks, (matrix{ml}) * sub(Vsub,Apoly));
                    rowsSoFar = rowsSoFar + #ml));
            out#m = {fold(blocks, (a,b) -> a||b), keysm}));
    out));
print("  次数ごとの成分数 = "
    | toString apply(sort keys matsByDeg, m -> {m, #((matsByDeg#m)#1)}));
flush stdio;

-- (j,i) -> A 係数のリスト
lookupMul = (j,i) -> (
    m := as#i + 1;
    pair := matsByDeg#m;
    p := position((pair#1), q -> q == {j,i});
    apply(rank0, l -> ((pair#0)_(l,p))));

verifyMul = () -> (
    ok := true;
    for trial from 1 to 20 do (
        j := random(#vs); i := random(rank0);
        coeffs := lookupMul(j,i);
        recon := sum apply(rank0, l -> (
            cl := coeffs#l;
            if cl == 0 then 0_R
            else sum apply(terms cl, tm -> (
                cc := lift(leadCoefficient tm, kk);
                sub(cc,R) * (toR(tm // (leadCoefficient tm))) * es#l))));
        if recon != vs#j * es#i then ok = false);
    ok);
print("  検算 (無作為 20 点で x_j*e_i = Σ c_l e_l):  " | toString verifyMul());
flush stdio;
print "=== 完了 ===";
