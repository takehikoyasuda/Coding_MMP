# isCartier/canonicalIndexDataへのfastpath拡張と、巡回被覆例の自然な表示での検証

**Status**: 一部実装・コミット済み、一部は反証されて撤回、中心的なボトルネックは未解決のまま。
**Date**: 2026-08-16
**関連**: [`BPF-HOM-BOTTLENECK-ROOT-CAUSE-SUMMARY.md`](BPF-HOM-BOTTLENECK-ROOT-CAUSE-SUMMARY.md)、
[`CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md`](CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md)、
[`ITERATED-MULTIGRADING-MMP-PLAN.md`](ITERATED-MULTIGRADING-MMP-PLAN.md)

## 1. 何を調べていたか

前回のセッションで`canonicalScaledNefDataInternal`（BPFのmultiplierスイープ）に
canonical-ideal-seed / class-degree fastpathを実装し、劇的な高速化を達成した。
今回はその延長で、(1) 同じ発想を`isCartier`／`canonicalIndexData`にも拡張できるか、
(2) それが元々の動機だった`Xminus`（cyclic-cover flipの35変数monograded表示）や、
平坦化前の自然な9変数bigraded表示`Xnatural`で実際に効くか、を検証した。

## 2. `canonicalIndexData`へのfastpath拡張（コミット済み: `2193262`）

`canonicalIndexData`（`i=1,2,\ldots`と`i\cdot K`のCartier性を順に試す指数探索）に、
2つの安価な十分条件を追加した。

1. `principalShiftCartierCertificateInternal`：`D`が単項式prime（Cox変数の消滅）の和なら、
   `O(D)`は自由加群なので無条件にCartier。`Hom`・`Ext`不要。
2. `canonicalIdealSeedInvertibleInternal`：キャッシュ済みcanonical ideal seed`I_K`の
   `i`乗のreflexive power`reflexivePower(i,I_K)`が`trim`後に単項イデアルなら、
   同じ理由で無条件にCartier。`reflexivePower`と`trim`のみ、`Hom(\mathrm{dualModule},R^1)`の
   二重双対は不要。

どちらも「証明可能なyesだけを早く見つける」設計で、失敗時（`null`）は既存の一般判定に
フォールバックするため、既存挙動は一切変えない。6変数のrank-2 toric hypersurface例で
検証：`canonicalIndexData`が0.01秒で完走（`tests/cartier-index-fastpath.m2`）。

同時に、`IrrelevantIdeal`オプションを追加し、供給時は`isCartierSaturatedInternal`
（正しい`B`を使う版）にフォールバックするようにした。これは別途見つかった
「`WeilDivisors`の`getIrrelevantIdeal(R)`が混合符号次数付けで誤ったBを使う」
という既知の不具合を、`B`が既知の呼び出し側に対して副次的に修正する。

## 3. `Xminus`（35変数、余次元31）での再検証：期待通りには効かず、クラッシュ

前回文書化した「`canonicalIndexData(Xminus)`が生の`isCartier`呼び出しで
30分超・多GBハングする」問題に、上記のfastpathが効くか試した。

結果：**効かず、むしろ悪化した**。`canonicalIdealSeedDataInternal`（seedの構築、
`\mathrm{Ext}^{\mathrm{codim}}(\ldots)+\mathrm{Hom}(\omega,R^1)`）自体が、
メモリ使用量15.6GBまで急増して2分弱でクラッシュ（OSによる無言のkill）した。

原因を定量的に特定した：`Xminus`の余次元は**31**（35変数、次元4）、定義イデアルの
生成元は**280個**——完全交叉（余次元と同数の生成元で足りる状態）から極端にかけ離れた
埋め込みである。一方、平坦化前の自然な表示（`antiProjection#ambientRing`、9変数）は
余次元わずか4、生成元11個。`\mathrm{Ext}^{31}`まで自由分解を追いかけること自体が、
Hom計算のどの生成元を選ぶかとは無関係に、根本的に高コストだった。

**結論**：「monograded化して35変数になること」自体が原因ではなく、その平坦化経路が
生む**余次元31・生成元280という埋め込みの複雑さ**が真犯人。この事実は、Rees環
経由の平坦化を避け、自然な表示のまま扱う入口を作ることの重要性を裏付ける。

## 4. `Xnatural`（自然な9変数bigraded表示）での再検証

平坦化前の`Xnatural = antiProjection#totalRing`（余次元4）に対し、**既に実装済みだった**
多重次数トップレベル入口（`threefoldMMPData(R,a,H,IrrelevantIdeal=>B)`、
`ITERATED-MULTIGRADING-MMP-PLAN.md`のPhase 1、2026-08-15実装）を、今回のBPF fastpath込みで
再実行した（`scripts/cyclic-cover-multigraded-driver-probe.m2`、M2のスクリプト読み込みモードの
`try/else`・複数行`if/then/else`構文の落とし穴を修正して実行）。

| 段階 | 結果 |
| --- | --- |
| `canonicalNefData` | **約3.3秒で完走**、`nef=false`（fastpathの直接的な勝利。旧基準は95秒〜15分超で打ち切り） |
| `canonicalNefThresholdData` | 75分超・約5GBでユーザー指示により停止 |

### 根本原因：`K`・`H`自体が単項式的でない

`Xnatural`上で`K`・`H`を直接印字すると、支持素因子（プライム）に**4次式**
（巡回被覆の分岐方程式そのもの）を含む、複数生成元のprimeが現れる。
`principalShiftCartierCertificateInternal(K)=false`、`(H)=false`と確認した。

`t=1,2,4,8`と個別に計測すると、コストが指数的にエスカレートするパターン
（1.2秒→1.5秒→16秒→73秒超）が再現した。これは、以前root-causeした
「複数の高さ1primeを組み合わせる`weilDivisorToModule`のコスト爆発」が、
今回のfastpathの前提（単項式支持）を満たさない、genuinely非トーリックな
（巡回被覆由来の）入力で再発したものである。

**結論**：今回のfastpathは、トーリック的な入力（Cox座標＝単項式）には非常によく効くが、
巡回被覆のような非トーリックな入力では`K`・`H`自体が単項式で表現できず、
fastpathの土俵に乗らない。

## 5. MMP理論の前提の明確化（副次的な訂正）

調査の途中で、以下の理論的な整理を行った（実装ではなく理解の訂正）。

- 本プロジェクトのMMPは、Q-factorial性は仮定せず、**Q-Gorenstein性のみ**を仮定する。
- ストーリーは「Q-Gorensteinな$X$をsmall contractionすると、収縮先$W$は
  一般に**非Q-Gorenstein**になる。flip（$W$上のrelative canonical model）を取ると、
  $X^+$としてQ-Gorensteinに戻る」というもの。
- したがって、`Wcover`（収縮先）が指数8まで試してもCartierにならなかったのは
  バグではなく、**理論通りの挙動**。Q-Gorensteinと仮定されるべきは`Xminus`/`Xnatural`
  （収縮の始点）の方であり、これは一般には計算しないと分からない
  （terminal特異点の分類（Mori, Reid）では指数は非有界であり、今回の指数2は
  この具体例に対する個別の作業——トーリック回路の組合せ論＋étale被覆の議論——の
  成果であって、一般論の帰結ではない）。

## 6. `canonicalIdealSeedDataInternal`の最小次数embedding修正（未コミット、健全）

third-partyの`FlipComputation`パッケージ（`third_party/flip-computation/FlipComputation/divisors.m2`）
の`canonicalIdeal`関数に、私たち自身の`canonicalIdealSeedDataInternal`が
真似ていなかった最適化が見つかった：`\mathrm{Hom}(\omega,R^1)`が複数の生成元を
持つ場合、**次数最小のものを選ぶ**（`minPosition`）。third-party自身のコメントに
「この最適化だけで17分→0.05秒」との実績が明記されている。

私たちのコードは単に最初の生成元（インデックス0）を取っていたため、この修正を適用した
（多重次数への一般化として、各生成元の次数ベクトルの**和**を比較キーに使用）。
`make test-core`は全通過。ただし、これは`Xminus`（seed構築自体が余次元31で高コスト）にも
`Xnatural`（seed構築はそもそも0.005秒と高速）にも直接の効果はなかった——
「`Hom`が複数の生成元を持ち、かつ`Ext`自体はそこまで高コストでない」という、
より限定的なケースへの改善である。

## 7. `saturate(I,B)`の生成元ごと分解：見かけ上の3000倍高速化は測定の誤りと判明（反証・撤回）

`Xnatural`のBPF査定（`basePointFreeModuleInternal`の最終ステップ、
`saturate(\mathrm{ann}(\mathrm{cokernel}),B)`）が、`reflexivePower`等ではなく
この`saturate`自体で支配的にコストがかかっている（kCoeff=2で14.3秒、
kCoeff=4で39.4秒、`reflexivePower`自体は常に0.01秒未満）ことを突き止めた。

数学的に厳密な等価変形として、
$$\mathrm{saturate}(I,B)=(1) \iff \forall\, g_i\in(\text{$B$の生成元}),\ \mathrm{saturate}(I,(g_i))=(1)$$
（$\mathrm{radical}(I)$がイデアルであることから、$B$の生成元ごとにチェックすれば
十分）を用い、多生成元の`B`（14生成元）を単一生成元の`saturate`14回に分解する
`saturatesToUnitIdealInternal`を実装。**最初の測定では12.5秒→0.004秒という
約3000倍の高速化に見えた。**

しかし、これは**ベンチマークの罠**による誤りだった：最初の測定では
「重い一括`saturate`を先に計算 → その後に生成元ごとのテストを実行」という順序で
測っていたため、後半のテストはM2内部のGröbner基底キャッシュが温まった状態で
走っており、不当に速く見えていただけだった。**キャッシュの影響を排除し、
生成元ごとのテストを新鮮なイデアルに対して最初に実行し直すと、合計は約12.68秒**——
元の一括`saturate`とほぼ同じで、実質的な高速化efectはなかった。

この修正は`MMPComputation.m2`から**撤回済み**（コミットしていない）。

**教訓**：可変な内部キャッシュ（Gröbner基底など）を持つオブジェクトに対して
2つの計算方法を比較する際は、両方を独立した新鮮なオブジェクトに対して測るか、
順序を入れ替えて確認しない限り、劇的な差は測定アーティファクトを疑うべきである。
M2の`isCartier`・`nonCartierLocus`・`saturate`はいずれも入力オブジェクトに
結果をキャッシュするため、常にこのリスクがある。

## 8. 残る未解決の問題

`Xnatural`の真のボトルネックは、`\mathrm{ann}(\mathrm{evaluationCokernel})`という
イデアルが（trim前で）**1859個もの生成元**を持つこと自体にある。`saturate`を
どう構成し直しても、この巨大なイデアルを処理するコスト自体は変わらなかった。
なぜこの`ann`がこれほど複雑になるのか（`\mathrm{evaluationCokernel}`自体の表示、
あるいは別の計算経路がないか）は、今回調査していない。この調査を再開する場合の
自然な次の的である。

## 9. まとめ

| 項目 | 結果 |
| --- | --- |
| `canonicalIndexData`へのfastpath拡張 | 実装・検証済み、コミット済み（`2193262`） |
| `Xminus`（余次元31）への適用 | 効かず、根本原因（`\mathrm{Ext}^{31}`自体のコスト）を特定 |
| `Xnatural`（自然な9変数表示）での`canonicalNefData` | fastpathで3.3秒に短縮、成功 |
| `Xnatural`での`canonicalNefThresholdData` | 非トーリック（`K`・`H`が非単項式）のため未解決 |
| MMP理論の前提整理 | Q-Gorensteinは$X$（収縮元）の仮定、$W$（収縮先）は非Q-Gorensteinで正常 |
| 最小次数embedding修正 | 健全・実装済み（未コミット）、限定的だが実在する改善 |
| `saturate`の生成元ごと分解 | 反証・撤回。ベンチマークの罠（GBキャッシュの温まり）による誤った結論だった |
| `Xnatural`の真因（1859生成元の`ann`） | 未解決 |
