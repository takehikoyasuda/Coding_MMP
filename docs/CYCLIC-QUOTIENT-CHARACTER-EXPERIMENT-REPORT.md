# Cyclic Quotient Singularityにおけるcharacter予測とQ_aテーブル化仮説の検証

**Status**: Completed, mixed result — theory confirmed locally, core speed hypothesis refuted
**Date**: 2026-08-13
**Work location**: Scratchpad only (no repo changes, no commits)
**Branch**: `feature/multigraded-stage1` (unchanged)

---

## 背景・目的

`docs/algorithmic_mmp_bpf_fastpath_notes.md` §7–16 は、$D=aK_X+bH$ 型divisorのBPF判定を、
`weilDivisorToModule`によるfull reflexive hull構成を避け、各terminal特異点でのcanonical cover
上のcharacter/jet条件から直接section を構成する、という設計（"section oracle"）を提案していた。
その本命の仮説（§16）は:

$$0\to F_a\to\omega_X^{[a]}\to Q_a\to0,\qquad F_a=(\omega_X^{\otimes a})/\text{torsion}$$

において、特異点にsupportを持つ有限長層 $Q_a$ は「特異点の型と $a\bmod r$（$r$=局所index）
だけで決まり、事前計算・table化できる」というものだった。

`docs/BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md` で、実際のボトルネックが
`weilDivisorToModule`のreflexive hull構成そのもの（n=14で全体の98.9%）にあることを確認済み
であり、この $Q_a$ のtable化が本当に機能するかどうかが、`algorithmic_mmp_bpf_fastpath_notes.md`
の設計全体（§7–17）の投資価値を決める試金石だった。

本実験はこの仮説を、最も単純な具体例（3-fold terminal cyclic quotient singularity）で
直接検証する。

---

## 使用した例

**$\frac12(1,1,1)$（Veronese錐）**: $X=\mathbb C^3/(\mathbb Z/2)$、作用
$(x,y,z)\mapsto(-x,-y,-z)$。Reid–Tai条件（$k=1$: $\{1/2\}\times3=3/2>1$）を満たすisolated
terminal quotient singularity。不変環は次数2の6単項式 $x^2,y^2,z^2,xy,xz,yz$ で生成される
古典的なVeronese cone。

**$\frac13(1,2,1)=\frac13(1,-1,1)$**（比較対象、2つ目の型）: 同様にterminalな
cyclic quotient singularity、7個の生成元を持つ不変環。

両方とも**2通りの方法で構成し一致を確認**した:
- (a) 不変式環として直接構成（$\ker$ of ring map）
- (b) toric構成として（`coneFromVData`/`hilbertBasis`/`dualCone`、Stage 2のZ環と同じPolyhedra
  パッケージの手法を、より細かい格子 $N'=\mathbb Z^3+\mathbb Z\cdot\frac12(1,1,1)$ に適用）

両者は生成元の指数ベクトル集合として完全に一致し、次元・特異点構造も一致（正しさの確認済み）。

$\dim X=3$、特異点は原点のみ（Jacobian idealのradicalが$\mathfrak m$）、$K_X$は非Cartier、
$2K_X$（$\frac12(1,1,1)$の場合）/ $3K_X$（$\frac13(1,2,1)$の場合）はCartier
——理論通りindex $r$ と一致。

---

## 結果1: character予測(§9)は厳密に正しい

$J=\mathcal O_X(K)$（reflexive）に対し、3つの構成を比較:

- **(A)** 素朴なtensor power（reflexivize前）: $F_a=J^a$
- **(B)** 実際のreflexive hull: `WeilDivisors`の`ideal(WeilDivisor)`/`reflexify(J^a)`
  （既存コードそのまま）
- **(C)** character予測: canonical cover（この例では$\mathbb C^3$自身）上のcharacter
  $a\bmod r$ の部分を、reflexive hull計算を一切使わず直接予測

$a=1..6$（両方の特異点型）で、**(B)と(C)は完全に一致**（idealとして、生成元レベルで）。
$Q_a$のHilbert関数も予測 $\bigoplus_{0\le m<a,\ m\equiv a\,(r)}S_m$ と完全一致。

**§9の主張（$\mathcal O_X(aK_X)$はcanonical cover上のcharacter $a\bmod r$の部分として
記述できる）は、この具体例において一切の食い違いなく検証された。**

---

## 結果2: $Q_a$のテーブル化仮説(§16)は明確に反証された

$\operatorname{length}Q_a$ を $a=1..14$ で計算:

| 特異点 | $a=1$ | $2$ | $3$ | $4$ | $5$ | $6$ | $7$ | $8$ | $9$ | $10$ | $11$ | $12$ | $13$ | $14$ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| $\frac12(1,1,1)$ | 0 | 1 | 3 | 7 | 13 | 22 | 34 | 50 | 70 | 95 | 125 | 161 | 203 | 252 |
| $\frac13(1,2,1)$ | 0 | 2 | 7 | 16 | 31 | 53 | 83 | 123 | 174 | 237 | 314 | 406 | 514 | 640 |

$a\bmod r$ でグループ化しても定数にならない（例: $\frac12(1,1,1)$で$a\bmod2=1$の列
$\{1,7,22,50,95,\dots\}$は増加し続ける）。成長は漸近的に $\Theta(a^3)$
（$\sim a^3/(6r)$）——**$Q_a$は有限の局所状態ではなく、$a$について3次で無限に増大する**。

**§16の仮説は、文字通りの意味では誤りである。テーブル化できるものは何もない。**

### 生き残った部分（ただし新しい武器ではない）

- **exact mod-$r$縮約(§8)**: $\mathcal O(aK)=\mathcal O(sK)\cdot\mathcal O(rK)^q$
  （$a=qr+s$）が、補正項ゼロの**厳密なideal恒等式**として全ケースで成立。ただしこれは
  「$rK$がCartier」という既知の事実の言い換えに過ぎず、新しい高速化のレバーではない。
- **one-step補正の周期性**: $C_a=\mathcal O(aK)/(\mathcal O((a-1)K)\cdot\mathcal O(K))$の
  lengthは、$\frac12(1,1,1)$で$0,1,0,1,\dots$、$\frac13(1,2,1)$で$0,2,1,0,2,1,\dots$と、
  **確かに$a\bmod r$で周期的**（型ごとに異なる）。これは§16の主張のうち唯一正しい形だが、
  §16が想定していた「$Q_a$全体の周期性」とは別物であり、この周期性だけでは
  reflexive hull構成全体を代替できない。

### 決定的な問題: これは既に否定済みのアイデアと同一

「$a$を$\bmod r$に縮約し、cacheした invertible ideal $\mathcal O(rK)^q$ を掛ける」という、
この局所実験が唯一正当化できる高速化案は、**`docs/INVERTIBLE-IDEAL-CACHING-EXPERIMENT-REPORT.md`
で既に実験・否定済みのアイデアと全く同一**である。あちらの実験は、この同じアイデアを
Stage 2のグローバルな次数付き環で実際に試し、「正しいが4–6倍遅い」（`ann`/`saturate`側の
コストがグローバル設定で爆発する）という結果を得ていた。今回の局所的な正しさの確認は、
グローバル設定で速くなることへの新しい根拠を一切与えない。

### 速度比較（局所・アフィンの小さい例、参考情報)

| | $\frac12(1,1,1)$ | $\frac13(1,2,1)$ |
|---|---|---|
| 既存`ideal(-aK)`（package） | 約4–5ms、$a$によらずflat | 約5ms、flat |
| `reflexify(J^a)`（素朴） | 4ms→95ms（$a$とともに増大） | 4ms→213ms（増大） |
| character/table | 約0.2ms、flat |約0.25ms、flat |

character予測は既存package比で約20倍、素朴なreflexive powerに対しては約400–900倍速いが、
**これは全て局所・アフィンの1点における数ミリ秒規模の絶対値**であり、実際のボトルネック
（グローバルな次数付き環、数十秒〜数分規模）とはスケールが全く異なる。さらに重要なことに、
既存の`idealPower`は生成元のべき乗を取るのであって$J^a$そのものを構成しないため、
**$a$についてもとから既にflat**——つまり$Q_a$が3次成長するという「問題」自体、
本番コードは最初から踏んでいない。

---

## 結論・設計全体への影響

`algorithmic_mmp_bpf_fastpath_notes.md` §7–17（character/jet局所補正によるsection oracle設計）
は、**測定されたボトルネック（グローバルなreflexive hull構成コスト）を解消する手段としては
機能しないことが、この実験によって具体的に確定した**。

生き残るのは:
- §9のcharacter記述そのもの（**correctness oracle**としての価値——`weilDivisorToModule`の
  結果を独立に検算する手段として、テストコード等に使える可能性はある）
- §8のmod-$r$縮約（新しい高速化のレバーにはならないが、事実としては正しい）

投資すべきでないもの:
- §16の$Q_a$テーブル化（反証済み）
- §17のsection oracle全体（局所データだけではglobal sectionを特徴づけられないという
  §10自身の限界が、今回の実験で速度面からも裏付けられた）

このセッションを通じて残る、実際に投資価値のある方向は:
- **`docs/GFP-REDUCTION-BENCHMARK-REPORT.md`**（GF(p)還元、検証済みの約2.3倍の定数倍改善、
  ただしcharacteristic 0への厳密な持ち上げは未実装）
- **§7.1（truncated Ext、$a=1$/Gorenstein/index-1の場合に限定した、canonical moduleの
  次数を絞った計算）**——これは今回の実験が扱った「$a>1$の反射べき」問題とは別物であり、
  まだ検証されていない

---

## ファイル

全て scratchpad（リポジトリ非変更）:
- `step0.m2`/`step0.log` — 両構成方法、次元・特異点・Cartier index確認
- `step1.m2`/`step1.log` — (A)(B)(C)比較、$a=1..6$、$\frac12(1,1,1)$
- `step2.m2`/`step2.log` — 一般化版、両特異点、mod-$r$恒等式検証
- `step3.m2`/`step3.log` — 速度比較、$a=1..20$
- `step4.m2`/`step4.log` — one-step/$r$-step補正の周期性
- `step5.m2`/`step5.log` — $\operatorname{length}Q_a$の成長、$a=14$まで
- 関連する既存文書:
  - `docs/algorithmic_mmp_bpf_fastpath_notes.md`（§7–16）
  - `docs/INVERTIBLE-IDEAL-CACHING-EXPERIMENT-REPORT.md`
  - `docs/BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md`
  - `docs/GFP-REDUCTION-BENCHMARK-REPORT.md`
