# 被覆なしで log MMP（境界因子付きペア）を扱うための設計案

**Status**: Design only（未実装）。投資判断のための material。
**Date**: 2026-08-15
**動機**: [CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md](CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md) の巡回被覆例は、
自然な多重次数表示のまま自動化しようとすると `canonicalScaledNefDataInternal` の
BPF 判定が非常に重くなることが分かった（2026-08-15 の実験、[ITERATED-MULTIGRADING-MMP-PLAN.md](ITERATED-MULTIGRADING-MMP-PLAN.md) 参照）。
この文書は「巡回被覆を実際に取らずに、同じ効果を境界因子付きペア $(W,\Delta)$ として直接扱えないか」を検討した設計案である。

## 結論を先に

数学的には正しいが、**既存コードでは近道にならない**。理由は `FlipComputation` の
`computeFlip`（Algorithm 3 の実装）が裸の正準因子 $K_R$ にハードコードされているため。
ただし、コードを詳しく読むと、**core algorithm 自体は変更せずに、$K$ の代わりに
「$K':=r\cdot K_R+\Delta'$」という積分因子を supply できる入口を追加するだけで済む**
という、当初想定より遥かに小さい設計で実現できることが分かった。これを以下に記録する。

## 数学的背景

巡回被覆で達成したこと（`K_{W'}=\pi^*(K_W+3A)`）は、log MMP の言葉で言えば
「境界因子付きペア $(W,\Delta)$、$\Delta=\frac34 B_0$（$B_0\in|4A|$ の一般元）」を
「裸の $K$ の問題」に変換する標準的な道具（巡回被覆）を使っただけである。
$\Delta$ を分母 $r$ で払った積分因子を $\Delta'=r\Delta$ と書けば（今回の例では $r=4$,
$\Delta'=3B_0$）、$(W,\Delta)$ に対する相対 log 標準模型は

$$X^{\log} = \mathrm{Proj}\bigoplus_{n\ge0} \mathcal O_W(\lfloor n(K_W+\Delta)\rfloor)$$

である。ここで鍵となる事実は、**Veronese部分環は同じ Proj を与える**という標準的な
事実である：$r\,|\,n$ の項だけを取り出した部分環

$$\bigoplus_{k\ge0}\mathcal O_W(k\cdot r(K_W+\Delta)) = \bigoplus_{k\ge0}\mathcal O_W(k\cdot K')\qquad(K':=rK_W+\Delta')$$

は、$K'$ が（$\Delta'$ を積分因子として選んだので）**正真正銘の積分 Weil 因子**であるため、
$\lfloor\cdot\rfloor$ の端数処理を一切必要とせず、しかも元の log Proj と同じ多様体を与える
（Veronese部分環はProjを変えない）。

**つまり、$K'=rK_W+\Delta'$ を「あたかも $W$ の正準因子であるかのように」既存の
`computeFlip`/`canonicalNefData`/`canonicalContractionData` に渡せば、それらのコードを
一切変更せずに $(W,\Delta)$ の log MMP ステップがそのまま計算される。** 必要なのは
「$K$ をどこから取ってくるか」という配管を変えることだけで、アルゴリズム本体
（`computeFlip` の multiplier loop、`canonicalNefDataCore` の探索ロジック等）は無傷で使える。

## 何が変わらないか

- `computeFlip` の multiplier loop（`divisorialIdeal`, `bigradedReesProjection`,
  `isSmallProjection`, `isS2Source` の呼び出し順序）：**無変更**。
- `canonicalNefDataCore`/`canonicalScaledNefDataInternal` の探索アルゴリズム：**無変更**。
- 実際に払う計算コストは、巡回被覆のような「新しい変数・新しい高次関係式」を持つ
  大きな環ではなく、**元の（小さい）環 $W$ の中で完結する**——これが本来の目的である
  「計算コストを避ける」ことに直結するはずの部分。

## 何を変える必要があるか

### 1. `FlipComputation`（third-party）

`canonicalDivisorData`, `flipDivisorData` は内部で
`K := canonicalDivisor(R, IsGraded => o.BaseIsProjective)` を呼んでいる
（[divisors.m2:14](../third_party/flip-computation/FlipComputation/divisors.m2#L14),
[divisors.m2:73](../third_party/flip-computation/FlipComputation/divisors.m2#L73)）。
ここに `CanonicalDivisorOverride => null` のような option を追加し、supply されれば
それを $K$ の代わりに使うようにする。`divisorialIdeal`/`computeFlip` 自体は
`Edata`（{prime, coefficient} のリスト）だけを見ているので変更不要。

### 2. `canonicalIdeal` の一般化（最大の技術的難所）

現状の `canonicalIdeal`（[divisors.m2:45-55](../third_party/flip-computation/FlipComputation/divisors.m2#L45-L55)）は、
$\omega_R$ を **`Ext^{codim}(R,\ldots)` という具体的な公式**で計算し、そこから
「次数最小の埋め込み」を選ぶ最適化を行っている。このコメント自体が

> "the whole computation drops from 'unfinished after seventeen minutes' to a
> twentieth of a second"

と明記しており、この最適化は死活的に重要である。しかし `Ext^{codim}(R,\ldots)` の公式は
$\omega_R$（＝$K_R$ 一本）専用であり、任意の因子類 $K'=rK_R+\Delta'$ には直接使えない。

一般化するには、`weilDivisorToModule(K')` から出発して、`canonicalIdeal` と同じ
「次数最小の埋め込みを Hom から選ぶ」手順を **一般の WeilDivisor 向けに書き直す**
必要がある（`antiCanonicalSection` のフォールバック経路に近いが、次数最小化の
最適化を保ったまま）。この一般化された関数（`leastDegreeEmbeddingIdeal(R,K')` のような
名前を想定）が既存の `canonicalIdeal` と同等の速度を再現できるかは **未検証**であり、
最初に取り組むべき実験はここになる。

### 3. `MMPComputation.m2`（自分たちのパッケージ）

`canonicalNefData`, `canonicalNefThresholdData`, `canonicalContractionData`,
`canonicalIndexData` はいずれも内部で `canonicalDivisor(R,IsGraded=>true)` を呼んでいる。
これらに同様の override 入口（`CanonicalDivisorOverride=>K'`、および $r$ を記録する
`CanonicalDivisorDenominator=>r` のような option）を追加する。

`a`（Cartier 指数の倍数）の意味は、override 使用時は「$K'=rK_W+\Delta'$ の Cartier 指数」
になる点に注意——呼び出し側は $r$ を自分で管理し、結果を元のペア $(W,\Delta)$ の言葉に
戻す責任を持つ。この変換（$r$ の掛け算・割り算）は現時点では caller 側の責任とし、
コード側で自動化はしない（根拠のない自動変換を避けるという、このプロジェクトの
既存方針 [[iterated-multigrading-mmp-plan]] と一致させる）。

### 4. 呼び出し側が用意すべきデータ

$\Delta$（正確には $r$ と積分因子 $\Delta'=r\Delta$）は、コードが自動的に導出できる
ものではない——「$B_0\in|rA|$ の一般元」という選択自体が数学的判断であり、
巡回被覆の分岐因子を選ぶのと同じ重みを持つ。したがってこの設計は
「境界因子を自動発見する」ものではなく、**呼び出し側が既に知っている $(r,\Delta')$ を
安く検証・実行できるようにする**ものである。

## 未検証のリスク・確認すべき点

1. **`canonicalIdeal` 一般化の速度**：上記の通り、最大の未知数。最初に小さい例
   （既存の `tests/relative-model.m2` の例など）で「override 経路が既存の $\Delta=0$
   相当の場合に既存結果を再現し、かつ速度が同等か」を確認するのが最初の一歩。
2. **正しさの検証**：$(W,\Delta)$ が log terminal（もしくは少なくとも既存の停止定理が
   適用できる程度に良い特異点）であることは、コードでは検証されず、呼び出し側の
   数学的責任として明示する必要がある。
3. **多重次数レイヤーとの整合性**：[ITERATED-MULTIGRADING-MMP-PLAN.md](ITERATED-MULTIGRADING-MMP-PLAN.md) の
   Phase 1-4 で進めている `IrrelevantIdeal`/`H` の受け渡しと、この override 機構は
   直交する（互いに干渉しない）はずだが、`canonicalNefData(R,a,H,IrrelevantIdeal=>B)`
   のような多重次数入口に override を追加する際は、両方のオプションが同時に
   正しく機能することを別途テストする必要がある。
4. **既存テストへの影響**：override を追加しても、supply しない限り既存の挙動と
   完全に一致することを回帰テストで確認する（他の Stage 2 作業と同じ方針）。

## 見積もりと位置づけ

今日実装した Phase 1（多重次数トップレベル入口）や `negativeCurveWitnessData` より
**大きい**投資である。特に第2項（`canonicalIdeal` の一般化）は、既存の
「17分→0.05秒」の最適化を再現できるかどうかにかかっており、これ自体が
数日規模の実験を要する可能性がある。実装するかどうかは、cyclic-cover 例を
上回る具体的な境界因子付き例（$r,\Delta'$ が明示的に分かっているもの）が
用意できてから判断するのが妥当。

## 次のアクション候補（実装はまだしない）

1. `canonicalIdeal` 一般化の実験を、まず **override なしで既存結果を再現できるか**
   だけを対象に小さく試す（$\Delta'=0,r=1$ の場合に既存 `canonicalIdeal` と
   一致し、速度も同等か）。
2. 上記が通れば、cyclic-cover 例の $r=4,\Delta'=3B_0$（$B_0=\{y_1^4+\cdots+w^4=0\}$）
   を使って、$W$（5–7変数、被覆なし）に対して直接 `computeFlip` 相当を試し、
   35変数の平坦化や9変数の双次数表示より速いかを実測する。
