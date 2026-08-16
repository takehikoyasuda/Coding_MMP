# Cox ring における base locus / BPF 判定の高速化：試すべき戦略

## 問題設定

Cox ring
\[
S=k[x_1,\ldots,x_n]
\]
と irrelevant ideal
\[
B=B_\Sigma=(m_1,\ldots,m_s)
\]
を考える。線形系を定める homogeneous ideal を \(I\subset S\) とする。

現在は
\[
I^{\mathrm{sat}}=I:B^\infty
\]
を計算し、
\[
I^{\mathrm{sat}}=S
\]
かどうかによって base-point-free (BPF) を判定している。

しかし BPF 判定だけが目的なら
\[
I:B^\infty=S
\iff
B\subseteq\sqrt I
\]
なので、saturated ideal 全体を計算する必要はない。

## Strategy 0: 現行法を benchmark baseline にする

Macaulay2 の通常の
\[
I:B^\infty
\]
を計算する。

記録するもの：
- 変数数
- \(I\) の生成元数・次数
- \(B\) の生成元数
- Gröbner basis 計算時間
- saturation 計算時間
- memory usage
- BPF / non-BPF

以下の方法をすべて同じ実例で比較する。

---

## Strategy 1: Singular / OSCAR の saturation と比較

同じ
\[
I:B^\infty
\]
を

- Macaulay2
- Singular
- OSCAR

で計算して benchmark する。

目的：
「Macaulay2 の実装が遅い」のか、
「saturation という問題自体が重い」のかを切り分ける。

Singular の `satstd` が利用できる特殊な場合も別途試す。

---

## Strategy 2: principal saturation + F4SAT

\[
B=(m_1,\ldots,m_s)
\]
に対して
\[
I:B^\infty
=
\bigcap_i(I:m_i^\infty)
\]
を利用する。

各 principal saturation
\[
I:m_i^\infty
\]
を F4SAT (`msolveSaturate`) で計算し、最後に intersection を取る。

通常の non-principal saturation と比較する。

注意：
F4SAT は現在 principal saturation に特化しているので、
intersection のコストがボトルネックになる可能性がある。

---

## Strategy 3: saturation を計算せず radical membership を判定する

BPF 判定だけなら
\[
I:B^\infty=S
\iff
B\subseteq\sqrt I.
\]

したがって
\[
B=(m_1,\ldots,m_s)
\]
の各 generator について
\[
m_i\in\sqrt I
\]
だけ判定する。

Rabinowitsch trick により
\[
m_i\in\sqrt I
\iff
1\in(I,1-tm_i)\subset S[t].
\]

したがって各 \(i\) について ideal が unit ideal かだけを判定する。

利点：
- saturated ideal の生成元が不要
- full Gröbner basis が不要な可能性
- \(1\) が得られた時点で停止可能
- 各 \(m_i\) の計算を並列化可能
- 一つでも失敗すれば non-BPF と判定して早期終了可能

BPF 判定では最優先で試す。

---

## Strategy 4: toric affine chart ごとの emptiness test

Cox irrelevant ideal を
\[
B_\Sigma=(x^{\widehat\sigma}\mid\sigma\in\Sigma_{\max})
\]
と書く。

各 maximal cone \(\sigma\) について
\[
V(I)\cap D(x^{\widehat\sigma})
\]
が空かどうかだけ判定する。

これは
\[
x^{\widehat\sigma}\in\sqrt I
\]
と同値。

したがって Cox quotient 全体で saturation を計算せず、
各 toric affine chart で base locus の emptiness を判定する。

fan の combinatorics を利用して
- 冗長な chart の削除
- 判定順序の最適化
- chart ごとの並列化
を検討する。

---

## Strategy 5: radical-membership / emptiness 専用アルゴリズム

Strategy 3, 4 の Gröbner basis を汎用 GB として最後まで計算せず、
「unit ideal かどうか」だけに特化する。

候補：
- F4
- F5 / signature-based Gröbner basis
- msolve
- Groebner.jl
- Singular
- modular methods
- Nullstellensatz certificate
- finite-field computation + lifting

特に
\[
1\in(I,1-tm_i)?
\]
という decision problem に特化した early termination を試す。

---

## Strategy 6: Cox multigrading を利用する

Cox ring の
\[
\deg(x_i)\in\operatorname{Cl}(X)
\]
という multigrading を Gröbner/Macaulay matrix 計算に利用する。

候補：
- matrix-weighted Gröbner basis
- multigraded Macaulay matrices
- multigraded Hilbert function
- Hilbert-driven saturation / membership test

不要な multidegree の Macaulay matrix を生成しない方法を検討する。

---

## Strategy 7: fan combinatorics + monomial structure を利用する

\(B_\Sigma\) は任意の ideal ではなく、
fan から決まる squarefree monomial ideal である。

この特殊性を利用して
\[
B_\Sigma\subseteq\sqrt I
\]
を効率的に判定する。

検討項目：
- minimal generators のみを使う
- support inclusion による冗長 generator の除去
- Stanley-Reisner combinatorics
- maximal cone 間で Gröbner 計算を共有
- chart の計算順序の最適化
- non-BPF になりやすい chart を先に調べる

---

## Strategy 8: incremental / tracing

MMP の各ステップで類似した ideal に対する BPF 判定を繰り返すなら、
毎回 Gröbner basis をゼロから計算しない。

候補：
- Gröbner tracing
- incremental Gröbner basis
- previous GB の再利用
- previous Macaulay matrices の再利用
- signature の再利用

MMP 全体での総計算時間を評価する。

---

# 優先順位

まず以下を実験する。

1. 現行 Macaulay2 `saturate` を baseline 化
2. Singular / OSCAR の通常 saturation
3. F4SAT による principal decomposition
4. saturation-free radical membership
5. affine toric chart ごとの emptiness test
6. F4/F5/msolve を使った高速 emptiness test

特に 3–6 を比較する。

最終的な研究方向としては

(A) non-principal / monomial F4SAT

(B) Cox multigrading を利用した saturation / radical membership

(C) fan combinatorics を利用した saturation-free BPF test

(D) MMP の連続するステップ間での Gröbner 情報の再利用

が候補。

重要な観点：

「saturation をどう高速化するか」だけでなく、

    BPF 判定のために saturation をそもそも計算する必要があるか？

を最初に検討する。