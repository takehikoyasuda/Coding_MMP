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

thetaIdx = toList((#vs-d)..(#vs-1));
print "  [theta 由来の関係式が自明か検算]";
okTheta = timeIt("C_{theta_i} = t_i * I か",() -> (
    all(d, s -> (
        j := thetaIdx#s;
        entries Cmatrix(j) == entries ((Apoly_s) * id_(Apoly^rank0))))));
print("    " | toString okTheta
    | "   (true なら " | toString (d*rank0) | " 本の関係式は落とせる)");
flush stdio;

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

-- 生成元の次数:  f_l の次数は d - a_l.  余核の基底がどの次数に出るか.
degF = apply(as, a -> d - a);
gensDeg = timeIt("生成元の次数",() -> (
    B := gensData#0;
    piv := set flatten entries (transpose (matrix{{}})); -- placeholder
    -- 余核の次数分布:  各次数ごとに部分行列の rank を取る.
    tally flatten apply(unique degF, g -> (
        rows := select(toList(0..rank0-1), l -> degF#l == g);
        sub1 := B^rows;
        toList((#rows - rank sub1) : g)))));
print("    生成元の次数分布 (上界) = " | toString gensDeg);
flush stdio;
print "=== 完了 ===";
