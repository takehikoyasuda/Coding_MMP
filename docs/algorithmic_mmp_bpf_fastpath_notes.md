# Algorithmic MMP における singular 3-fold 上の BPF 判定高速化メモ

## 0. 問題設定

Algorithmic MMP の Macaulay2 実装では、Mori cone を先に計算せず、basepoint free (BPF) な線型系を見つけて contraction を構成し、その後に flip 等を計算する。

現在のボトルネックは、terminal singularities をもつ 3-fold 上で、主に

\[
D=aK_X+bH
\]

型の \(\mathbb Q\)-Cartier divisor（あるいはその Cartier multiple）について BPF を確認する処理である。Effective BPF の「何倍を取ればよいか」については松下の結果を利用できるため、問題は **候補となる因子について実際に BPF を確認する計算そのもの** にある。

目標は、従来の

\[
D \to \mathcal O_X(D)\text{ の graded module} \to H^0(X,D)\text{ 全体} \to \text{base ideal} \to \text{saturation}
\]

という重い流れを、できるだけ

\[
(a,b) \to \text{少数の実際の section} \to \text{共通零点が空か？}
\]

という軽い流れに置き換えることである。

---

## 1. まず重要な整理：Mori cone / flipping curve は事前には分からない

通常の理論的 MMP では extremal ray や supporting divisor を先に考えるため、exceptional/null locus に BPF 判定を局所化する発想が自然である。しかし現在の Algorithmic MMP では順序が逆で、BPF な線型系を見つけることが contraction を発見する前段階である。

したがって、

- extremal ray を既知と仮定する
- flipping curve を既知と仮定する
- exceptional locus に BPF 判定を制限する

という高速化は、そのままでは使えない。

もし将来、BPF より安い計算から contracted-curve candidate locus を先に絞れるなら別であるが、現段階では **線型系そのものを安く扱う方向** が本命である。

---

## 2. BPF 証明には全切断は不要：3-fold なら高々 4 本でよい

3-dimensional projective variety \(X\) と line bundle \(L\) を考える。

\(L\) が globally generated なら、十分一般の高々 4 本の切断

\[
s_0,s_1,s_2,s_3\in H^0(X,L)
\]

を選べば共通零点を空にできる。逆に、実際に 4 本の genuine sections を見つけて

\[
V_X(s_0,s_1,s_2,s_3)=\varnothing
\]

と確認できれば、それだけで \(L\) は BPF である。

したがって BPF 判定に本当に必要なのは

\[
V\subset H^0(X,L),\qquad \dim V\le 4
\]

という basepoint-free 部分空間を一つ見つけることであり、\(H^0(X,L)\) の全 basis や graded module presentation ではない。

### Las Vegas 型の安全な判定

1. genuine section をランダムに 4 本作る。
2. その共通零点を計算する。
3. 空なら **certified YES**。
4. 空でなければ別の 4 本を試す。
5. 数回失敗した場合のみ従来法へ fallback。

ランダム性は「YES をどれだけ早く発見できるか」にしか影響しない。空集合を得た場合の結論には誤判定がない。

これは base ideal の generator 数を数十・数百本から 4 本程度に落とせるため、Gröbner basis / saturation の大幅な軽量化が期待できる。

---

## 3. 有限体への reduction

Gröbner basis、saturation、syzygy、resolution、Ext などは \(\mathbb Q\) より \(\mathbb F_p\) 上で大幅に速くなることが多い。主因は \(\mathbb Q\) 上での coefficient swell と多倍長整数・gcd 計算を避けられることである。

したがって

\[
\mathbb Q \longrightarrow \mathbb F_p
\]

への reduction は有力である。

### BPF の characteristic-zero への持ち上げ

proper flat model

\[
\pi:\mathcal X\to \operatorname{Spec}\mathbb Z[1/N]
\]

と line bundle \(\mathcal L\) を考える。良い素数 \(p\) について

\[
L_p\text{ BPF},\qquad H^1(X_p,L_p)=0
\]

なら cohomology and base change により、特殊ファイバーの切断が相対的切断から来る。relative evaluation map の cokernel の support と properness を使えば、generic fiber 上でも evaluation が全射となり、

\[
L_{\mathbb Q}\text{ BPF}
\]

を導ける。

より本質的には、必要なのは

\[
(\pi_*\mathcal L)\otimes k(p)\to H^0(X_p,L_p)
\]

の surjectivity であり、\(H^1=0\) はその便利な十分条件である。

よって有限体計算は単なる heuristic ではなく、条件を付ければ **one-sided rigorous certificate** にできる。

---

## 4. F-singularity の利用について

Globally \(F\)-regularity は今回の用途には強すぎる。Terminality は局所的条件であるのに対し、global \(F\)-regularity は全体に強い positivity を要求するため、一般の MMP 中間モデルに期待するのは不自然である。

一方、terminal \(\Rightarrow\) klt であり、reduction mod \(p\) では strong \(F\)-regularity と密接な関係がある。しかし local strong \(F\)-regularity だけから一般の nef line bundle の \(H^1\)-vanishing は出ない。

したがって現時点では、F-singularity は BPF 高速化の本丸というより、

- local Frobenius / Fedder-type tests
- F-adjunction / F-pure center
- vanishing や local generation の補助 certificate

として検討するのが妥当である。

---

## 5. Q-Gorenstein index と terminal singularities

Terminal の定義式

\[
K_Y=f^*K_X+\sum_E a(E,X)E
\]

は \(K_X\) が \(\mathbb Q\)-Cartier であることを前提としており、そこから index の値が直接出るわけではない。

局所 index は

\[
r_P=\min\{m>0\mid \omega_X^{[m]}\text{ is invertible at }P\}
\]

である。

3-dimensional terminal singularities では分類が非常に強い。Index-one cover は Gorenstein terminal、すなわち isolated cDV hypersurface であり、non-Gorenstein terminal germ は cyclic quotient として記述される。

代表的な型と index は

| type | index |
|---|---:|
| \(cA/r\) | \(r\) |
| \(cAx/2\) | 2 |
| \(cAx/4\) | 4 |
| \(cD/2\) | 2 |
| \(cD/3\) | 3 |
| \(cE/2\) | 2 |

である。

したがって index \(\ge5\) の場合、本質的に \(cA/r\) 型だけが残る。

ただし arbitrary affine equations から Mori–Reid の analytic normal form を認識する処理自体は軽くない。そのため分類は、毎回 normal form を求めるためではなく、候補の枝刈りや metadata として使う方が実装向きである。

---

## 6. Flip 前後の singularity data

3-fold terminal flip では、flip 後の singularities は flip 前の単なる singularity basket だけでは決まらず、flipping curve の index-one cover 上での埋め込まれ方など extremal neighborhood の局所データが必要である。

しかし現在の Algorithmic MMP では flipping curve は BPF/contraction の後で初めて見えるため、flip 前の分類データを BPF 判定に直接使うことはできない。

一方、いったん flip を構成した後は、singularity type/index を metadata として保存し、次の MMP step で再計算しない設計は有望である。

---

## 7. 本命：\(D=aK_X+bH\) という特殊形を徹底的に利用する

ここが最重要である。

\[
D=aK_X+bH
\]

なら、一般の Weil divisor module を毎回構成する必要はない可能性が高い。

### 7.1 \(a=1\)：canonical module の必要次数部分だけを計算

\(X=\operatorname{Proj}R\subset\mathbf P^N\)、\(R=S/I\) とする。

通常

\[
\omega_R=\operatorname{Ext}^c_S(R,S(-N-1))
\]

を module 全体として計算する。しかし欲しいのが

\[
H^0(X,\omega_X(b))
\]

だけなら、free resolution \(F_\bullet\to R\) を dualize した complex の degree \(b\) 部分だけ取ればよい。

すなわち

\[
(\omega_R)_b
=
\frac{\ker A_b}{\operatorname{im}B_b}
\]

という有限次元ベクトル空間の kernel/image 計算に落ちる。

これは full canonical module presentation を構成するより大幅に軽い可能性がある。さらに \(\mathbb F_p\) 上では sparse linear algebra になる。

Macaulay2 の resolution の `LengthLimit`, `DegreeLimit`, `FastNonminimal` などを利用して、必要な homological degree / internal degree だけ計算する実装が候補である。

### 7.2 \(a>1\)：reflexive power が難所

欲しいのは

\[
\omega_X^{[a]}=(\omega_X^{\otimes a})^{**}.
\]

一般的な `reflexivePower` 的処理は重い。

しかし terminal 3-fold では singular locus は有限集合であり、

\[
F_a=(\omega_X^{\otimes a})/\text{torsion}
\]

とすると

\[
0\to F_a\to\omega_X^{[a]}\to Q_a\to0
\]

の \(Q_a\) は有限個の singular points に support を持つ finite-length sheaf である。

したがって reflexification の差は

\[
\boxed{\text{smooth locus 上の普通の tensor power} + \text{有限個の点での local correction}}
\]

と考えられる。

固定した \(a\) について \(Q_a\) は \(b\) に依存しないので、\(aK+bH\) で \(b\) を変えても correction data を再利用できる。

---

## 8. Canonical index を使えば \(a\) 方向も有限化できる

global canonical index を \(r\) とすると

\[
a=qr+s,\qquad0\le s<r.
\]

\(rK_X\) は Cartier なので

\[
\omega_X^{[a]}
\simeq
\omega_X^{[s]}\otimes\mathcal O_X(qrK_X).
\]

したがって singularity に由来する本質的な reflexive data は

\[
s=0,1,\dots,r-1
\]

だけでよい。

各 terminal point \(P\) でも local index \(r_P\) に対して

\[
[aK_X]_P
\]

は \(a\bmod r_P\) だけで決まる。

よって各 singular point について有限個の local states を cache できる。

---

## 9. Canonical cover と character decomposition

局所 terminal germ \(P\in X\) の index を \(r\) とし、canonical/index-one cover

\[
\pi:(Y,Q)\to(X,P)
\]

を考える。\(Y\) は isolated cDV hypersurface で、\(\mu_r\) が作用する。

局所的に

\[
\pi_*\mathcal O_Y
\simeq
\bigoplus_{j\in\mathbf Z/r}M_j,
\]

各 \(M_j\) は \(\mathcal O_X(jK_X)\) に対応する rank-one reflexive eigensheafである（符号は convention に依存）。

したがって

\[
\boxed{\mathcal O_X(aK_X)\text{ は canonical cover 上の character }a\bmod r\text{ の部分}}
\]

として扱える。

これにより、毎回

\[
\omega_X^{\otimes a}\to(\omega_X^{\otimes a})^{**}
\]

を計算する代わりに、character arithmetic で local type を追跡できる可能性がある。

### Cyclic quotient case

例えば cover coordinates に

\[
(x_1,\dots,x_n)\mapsto(\zeta^{w_1}x_1,\dots,\zeta^{w_n}x_n)
\]

という作用があれば monomial

\[
x_1^{e_1}\cdots x_n^{e_n}
\]

の character は

\[
\sum_i e_iw_i\pmod r.
\]

したがって \(aK\) に対応する local section candidate は単なる合同条件で列挙できる。

ここでは Gröbner basis や double dual は不要である。

---

## 10. 「global seed + local character correction」という設計

局所 character 条件だけでは global section は作れない。したがって canonical cover を各点で知るだけでは不十分である。

有望なのは

\[
\boxed{\text{global canonical datum を一度だけ計算} + \text{各 terminal point の local character correction}}
\]

という構成である。

例えば rational top form \(\eta\) など、\(K_X\) を表す global seed を function field 内で一度保持できれば、\(aK+bH\) の section は概念的に

\[
f\eta^a
\]

として探せる。

\(H\) が projective embedding の hyperplane class なら、未知部分を ambient homogeneous polynomial space に押し込める可能性がある。

理想的には

\[
S_d\supset V_{a,b}
\]

という有限次元線形部分空間として section candidate space を表し、terminal points が \(V_{a,b}\) に local linear/character conditions を課すだけにする。

---

## 11. Castelnuovo–Mumford regularity と section の再利用

固定した

\[
\mathcal F_a=\mathcal O_X(aK_X)
\]

について \(b\) が十分大きければ、Castelnuovo–Mumford regularity により

\[
H^0(\mathcal F_a(b))\otimes H^0(\mathcal O_X(1))
\to
H^0(\mathcal F_a(b+1))
\]

が surjective になる。

したがって一度

\[
H^0(aK+b_0H)
\]

の seed sections を得れば、以後の \(b>b_0\) は ambient linear forms/polynomials を掛けて生成できる。

これは

\[
\boxed{\text{expensive seed computation once} + \text{cheap multiplication thereafter}}
\]

という構造を与える。

BPF の YES certificate には全生成元は不要なので、seed sections とランダム ambient polynomials の積から 4 本程度を作ればよい。

---

## 12. Tjurina (Tyurina) 代数の役割

Index-one cover \(Y\) は isolated hypersurface

\[
Y=(f=0)\subset\mathbb A^4
\]

なので Tjurina algebra

\[
T_f=
 k[[x_1,x_2,x_3,x_4]]/
(f,\partial_1f,\dots,\partial_4f)
\]

は有限次元である。

Characteristic 0 の isolated hypersurface singularity では Mather–Yau theorem により、Tjurina algebra の algebra structure が analytic germ を決定する。

したがって Tjurina algebra は

\[
\boxed{\text{index-one cover の analytic/cDV type recognition}}
\]

に非常に強い。

ただし ordinary Tjurina algebra は cover \(Y\) を決めるだけで、元の quotient

\[
X=Y/\mu_r
\]

の \(\mu_r\)-action を一般には決めない。よって index や canonical character を Tjurina algebraだけから直接読むことは期待できない。

---

## 13. Equivariant / graded Tjurina algebra

Canonical cover に \(\mu_r\) が作用すると Jacobian ideal も invariant なので、Tjurina algebraにも作用が誘導される：

\[
T_f=\bigoplus_{\chi\in\widehat{\mu_r}}(T_f)_\chi.
\]

この **equivariant/graded Tjurina data** は今回の用途にかなり適している。

- algebra structure：cover の analytic type
- grading group：index 候補
- character decomposition：quotient action
- character \(a\)：\(\omega_X^{[a]}\) の local type

を同時に保持できる可能性がある。

Huge graded module の代わりに、各 singular pointについて有限次元 Artinian algebra と grading data を metadata として保存する構想である。

---

## 14. Tjurina より安い invariants を classifier の前段に置く

毎回 full Tjurina algebra を比較する必要はない。安い不変量から順に使う decision tree がよい。

候補：

1. Jacobian ideal / singular locus
2. embedding dimension
3. multiplicity
4. tangent cone / low-order jet
5. Hessian rank / corank
6. 一般 hyperplane section の ADE type
7. Milnor number \(\mu\)
8. Tjurina number \(\tau=\dim T_f\)
9. full Tjurina algebra structure
10. 必要なら equivariant/higher Tjurina data

cDV singularity は一般 hyperplane section が Du Val singularityになるため、4-variable germ 全体より 3-variable ADE section を先に分類するのが軽い可能性がある。

Positive characteristicでは classical Mather–Yau をそのまま使えないため、Tjurina number は filter として使い、必要なら higher Tjurina algebra / finite determinacy の結果を certificate 側に使う。

---

## 15. Finite jet 条件への還元というさらに強い可能性

最も魅力的な最終形は、各 terminal point \(P_i\) で admissible local sections を有限 jet space の線形部分空間

\[
V_i\subset \mathcal O_{X,P_i}/\mathfrak m_{P_i}^N
\]

として記述することである。

Ambient polynomial space \(S_d\) から jet map

\[
S_d\to
\bigoplus_i\mathcal O_{X,P_i}/\mathfrak m_i^N
\]

を作り、

\[
f_{P_i}\in V_i
\]

という条件を課せば、section candidate space は **有限次元の線形方程式の kernel** になる。

すなわち最終的に

\[
\boxed{\text{Ext / syzygy / double dual / reflexive module}}
\]

を

\[
\boxed{\text{sparse matrix kernel}}
\]

へ置き換えられる可能性がある。

Finite determinacy と Tjurina/Milnor invariants は、必要な jet order \(N\) を有限に抑える理論的裏付けとして使える可能性がある。

---

## 16. Local correction \(Q_a\) の table 化

\[
0\to F_a\to\omega_X^{[a]}\to Q_a\to0
\]

で \(Q_a\) は terminal points に support を持つ finite-length sheaf である。

Canonical cover の character descriptionから、\(Q_a\) は singularity type と \(a\bmod r\) だけで決まる可能性がある。

もし

\[
q_{\mathrm{type}}(a)=\operatorname{length}Q_a
\]

や、より強く \(Q_a\) の local module structure を terminal type ごとに事前計算できれば、global reflexification を毎回実行する必要がなくなる。

最初の実験対象としては cyclic quotient terminal singularity

\[
\frac1r(1,-1,c)
\]

が適している。Semi-invariant monomialsを明示的に列挙できるため、

- tensor power
- reflexive hull
- character eigenspace

の差を直接比較できる。

その後 \(cA/r\) へ拡張するのが自然である。

---

## 17. 提案する `section oracle` 設計

従来の「module を返す API」ではなく、少数の genuine sections を返す primitive を中心にする。

```text
randomSection(a,b):

    1. (a,b) の cached section があれば random combination

    2. より小さい b0 の seed があれば
       ambient polynomial of degree b-b0 を掛ける

    3. a を canonical index で reduce
       a = qr+s
       local state は s のみ使用

    4. a=1 等なら truncated Ext の必要次数だけ計算

    5. terminal points の character / finite-jet conditions を課す

    6. sparse linear algebra で section candidate を生成

    7. full reflexive module computation は最終 fallback
```

BPF 判定：

```text
isBPF(a,b):

    repeat several times:
        s0,s1,s2,s3 = randomSection(a,b)

        if V_X(s0,s1,s2,s3) is empty:
            return TRUE   # rigorous certificate

    fallback to exact/full computation
```

有限体 fast path を組み合わせるなら、section generation と共通零点計算を \(\mathbb F_p\) 上で行い、必要な base-change 条件を確認して characteristic zero へ戻す。

---

## 18. 実験ロードマップ

### Phase 1: 最小の proof of concept

1. Smooth/Gorenstein case \((r=1)\) で `canonicalModule` 全体と truncated-degree Ext を比較。
2. \((\omega_R)_b\) を finite-dimensional linear algebraだけで生成。
3. Full BPF ideal と random 4 sections の計算時間を比較。
4. QQ と GF(p) を比較。

### Phase 2: cyclic quotient terminal singularities

1. \(\frac1r(1,-1,c)\) の local canonical characters を実装。
2. Semi-invariant monomial generator を作る。
3. Macaulay2 の reflexive power と出力を比較。
4. \(Q_a\) の length/module structure を計算し table 化可能性を検証。

### Phase 3: \(cA/r\)

1. Index-one cover \(xy+f(z,t)=0\) と cyclic actionを扱う。
2. Character eigenspacesから local sections を生成。
3. Hessian / ADE section / Tjurina invariantsで型認識を試す。

### Phase 4: general terminal points

1. Cheap invariants による classifier。
2. Equivariant Tjurina data。
3. Finite-jet admissibility spaces \(V_i\) の構成。
4. Global ambient polynomial spaceとの線形条件として section を生成。

---

## 19. 現時点で最も有望な仮説

最終的に目指すべき形は次である。

> **Terminal 3-fold \(X\subset\mathbf P^N\) と \(D=aK_X+bH\) に対し、\(H^0(X,D)\) の graded module presentation を構成せず、global canonical seed と有限個の terminal points における character / finite-jet conditionsから、BPF certificate に必要な高々 4 本の global sections を sparse linear algebra で直接生成する。**

この仮説が実装可能なら、現在の

\[
\text{QQ 上の reflexive graded module}
\to
\text{全 global sections}
\to
\text{大きな base ideal}
\to
\text{saturation}
\]

を

\[
\text{precomputed local terminal data}
\to
\text{small linear system}
\to
\text{4 sections}
\to
\text{small common-zero computation}
\]

へ置き換えられる。

これは Algorithmic MMP に特化した **canonical-section engine / BPF oracle** として独立したアルゴリズム上の成果になる可能性がある。

---

## 20. 注意点・未解決事項

- Local character conditions だけで global section を特徴づけられるわけではない。global canonical datum との接続を厳密化する必要がある。
- Canonical cover を arbitrary equations から毎回構成すると、避けたい reflexive-module computation が再登場する可能性がある。cover/type data は一度計算して cache する設計が望ましい。
- Ordinary Tjurina algebra は cover の analytic type を決めるが quotient action を一般には決めない。Equivariant data が必要。
- Finite-jet condition だけで \(\mathcal O_X(aK)\) の local admissibility を記述できる具体的な bound とアルゴリズムは未確立。
- Random 4 sections 法は YES に対して安全だが、失敗は NO を意味しない。Fallback が必要。
- Reduction mod \(p\) で得た BPF を characteristic zero に持ち上げるには base change の条件を確認する必要がある。
- 実際の速度向上は Macaulay2 の内部実装（QQ 上で modular algorithm を既に使っているか等）にも依存するため benchmark が必須。

---

## 参考となる理論キーワード

- 3-fold terminal singularities; Mori–Reid classification
- index-one / canonical cover
- cDV hypersurface singularities
- rank-one reflexive sheaves and divisor class groups
- canonical modules and truncated Ext
- Castelnuovo–Mumford regularity
- minimal reductions / analytic spread
- cohomology and base change
- modular Gröbner basis computation
- strong/global F-regularity, Fedder criterion
- Tjurina algebra, Mather–Yau theorem
- equivariant singularity theory
- finite determinacy, higher Tjurina algebras
- semi-invariant monomials and cyclic quotient singularities

---

## 21. Chartwise canonical-form probe（cyclic-cover例）

既存の degree-four cyclic-cover 例で、Jacobian minor から canonical-form atlas の
codimension-one 部分を実際に検証した。

[`scripts/cyclic-cover-differential-chart-probe.m2`](../scripts/cyclic-cover-differential-chart-probe.m2)
の結果は次のとおり。

- affine cone は7変数・4関係式・次元4。
- Jacobian は一般点で rank 3。
- 非零の3次Jacobian minor は trim 後の ideal では68生成元、重複を含む局所チャート表では96個あり、その非零開集合が smooth locus を覆う。
- Jacobian singular locus は affine 次元1（Proj上は有限個の点）。
- `canonicalDivisor` の結果は `-P_1-P_2+(c)` で、`K` は非Cartier。
- `K` の non-Cartier locus も affine 次元1で、Jacobian singular locusと radical が一致。
- `K` は各Jacobian chart上ではCartierであり、non-Cartier locusは全てchartの外にある。
- `isQCartier(8,K,IsGraded=>true)` は `0`。この例では有限の周期的な index-one correction に落ちるとは限らない。

したがって、少なくともこの非hypersurface cyclic-cover presentationでは、

```text
smooth charts の局所有理 top form
+ 有限個の singular-point correction
```

という分解のうち、smooth locus の atlas 部分は実際に成立する。ただし `K` が
非-\(\mathbb Q\)-Gorenstein の例なので、特異点補正を有限周期データとみなすことはできない。
従って、この方法が直ちに `K` 自体の global double dual を置換するわけではなく、
まずは次の二枝に分ける必要がある。

1. `isQCartier(n,K)` が有限の index を返す場合：index-one cover / character data を
   cache し、chartwise form と有限 local correction から section oracle を作る。
2. index が存在しない場合：chartwise data は codimension-one の seed に限定し、
   singular locus 上の reflexive closure または別の canonical-module certificate を
   fallback として使う。

この分岐は、一般化可能なアルゴリズムに必要な安全条件を明示する。

## 22. canonical ideal / reflexive-power fast path の実装

チャート atlas 単独では global section の完全性を保証できないため、BPF全体には
canonical module の ideal embedding を接続した。`MMPComputation.m2` の内部経路では、
まず一度だけ

```text
omega_R = Ext^codim(R, omega_S),
I_K = image(omega_R -> R)
```

を計算し、候補 `mK+bH` を

```text
reflexivePower(m, I_K) ** R^(m*embeddingDegree+b*classDegree(H))
```

として degree-zero evaluation に渡す。`I_K` は canonical divisor に cache され、
各 multiplier の巨大な module double dual を繰り返さない。

`H` の class degree は、まず homogeneous principal support から読み、必要なら
`OO(H)` が単一 shift であることを確認して復元する。復元できない場合はこの shortcut
を使わず、従来の `divisorToModule` に戻る。

rank-2 toric hypersurface 例では、class degree を明示しなくても
`canonicalScaledNefData(...,t=1/2)` が約1.9秒で完了し、従来と同じ
`nef=false`、`multipliersTested={1,2,3,4,5,6}` を返した。
この経路を含む `canonicalNefData` 全体も約2.9秒で完了し、従来と同じ
`witnessType="non-nef positive perturbation"` を返した。

この経路は `tests/canonical-seed-bpf-fastpath.m2` で回帰検証している。normal domain と
canonical ideal embedding が成立する範囲では exact な reflexive power を使うため、
YES/NO の近似判定ではない。seed または H の shift が取れない場合は安全に一般経路へ
fallback する。なお、non-\(\mathbb Q\)-Gorenstein 例に対する chartwise atlas のみの
処理は、依然として codimension-one seed に限定される。
