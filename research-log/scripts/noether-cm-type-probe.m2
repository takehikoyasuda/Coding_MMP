-- omega_R の極小生成元の個数 = R の Cohen-Macaulay type = dim_k socle(R/(theta)).
-- omega を R 加群として組むときの行列の大きさを決めるので, 先に測る.
-- 次数付きの socle は omega の生成次数も与える (graded local duality).
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

R = timeIt("環の構成",buildRing);
d = dim R;
print("=== " | tgt | ":  変数 " | toString numgens ambient R | ",  dim " | toString d | " ===");
flush stdio;
thetas = timeIt("一般線形形式",() -> apply(d,i -> random(1,R)));
Rbar = timeIt("Artin 剰余",() -> R/ideal thetas);
bas = first entries basis Rbar;
as = apply(bas, m -> first degree m);
print("  階数 = " | toString (#bas) | ",  基底次数分布 " | toString tally as);
flush stdio;

mbar = ideal vars Rbar;
soc = timeIt("socle = (0 : m)",() -> trim (ideal(0_Rbar) : mbar));
socBasis = timeIt("socle の k 基底",() -> first entries mingens soc);
socDegs = apply(socBasis, f -> first degree f);
print("  Cohen-Macaulay type = dim_k socle = " | toString (#socBasis));
print("  socle の次数分布 = " | toString tally socDegs);
print("  Gorenstein ?  " | toString (#socBasis == 1));
-- graded local duality:  omega の極小生成元は socle と双対で, 次数は
-- (theta の次数の和) - (socle の次数) = d - s.
print("  => omega の極小生成元:  " | toString (#socBasis) | " 個,  次数 "
    | toString tally apply(socDegs, s -> d - s));
flush stdio;
print "=== 完了 ===";
