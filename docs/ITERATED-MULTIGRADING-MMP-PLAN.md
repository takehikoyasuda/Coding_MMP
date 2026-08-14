# MMP 全体で多重次数を積み重ねるための実装方針

**Status**: Proposed implementation plan  
**Date**: 2026-08-14  
**Primary acceptance example**:
[`scripts/cyclic-cover-one-flip-minimal.m2`](../scripts/cyclic-cover-one-flip-minimal.m2)

## 結論

MMP の各段階で得られる Rees 環や relative Proj を、途中で単次数環へ
flatten してから次の段階へ渡すのではなく、自然な多重次数表示のまま
MMP の状態として保持する。

作業中の状態は少なくとも

```text
(R, a, H, B, grading data)
```

を持つ。

- `R`: 現在の射影多様体の斉次座標環
- `a`: `a*K_R` が Cartier となる既知の正の整数
- `H`: nef threshold と MMP with scaling に用いる ample Cartier class
- `B`: 現在の多重射影表示の irrelevant ideal
- `grading data`: 次数行列、変数ブロック、許容される再次数付けの情報

relative Proj や Rees 構成を一回行うごとに、新しい相対次数をこの状態へ
追加する。その後の nef 判定、threshold 計算、収縮、Stein factorization、
relative canonical model は、同じ状態を引き継いで計算する。

ここでいう「積み重ねる」は次数軸を無条件に増やし続けるという意味では
ない。幾何学的情報を保つことが証明された明示的な再次数付けがある場合に
限り、冗長な次数方向を取り除いてよい。単次数化を暗黙の既定動作にはしない。

## この方針が必要になった理由

一回だけ flip して minimal model で終了する循環被覆の例では、最初の
flipping side は自然には **9 変数の双次数 Rees 表示**である。しかし現在の
top-level driver は、呼出側が `H` と `B` を与える入口を持たない。そのため
最初の収縮を通常の driver に再発見させるには、先に単次数化する必要がある。

この単次数化により表示は 35 変数へ膨張し、大域切断と
base-point-free 判定の既知のボトルネックが再び現れる。現在の再現スクリプトは
この問題を避けるため、最初の収縮と flip を構成・検証して `flipStep` として
driver に渡している。

```m2
threefoldMMPData(Xplus,1,{flipStep})
```

これは contraction、relative canonical model、flip、最後の nef 判定までを
同じ実行で計算するが、driver が最初の extremal contraction を入力から自動で
発見する形ではない。詳細は
[`CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md`](CYCLIC-COVER-ONE-FLIP-MINIMAL-REPORT.md)
を参照。

したがって今回の例は、多重次数対応が単なる最適化ではなく、MMP の自然な
中間表現を壊さずにアルゴリズム全体を接続するための要件であることを示して
いる。

## 既に実装されている部分

基礎部分の多くは既に `MMPComputation.m2` にある。

- block lower triangular かつ対角成分が正である grading を
  `multigradedBlockData` が認識する。
- 多重次数の場合の幾何学的次元を `dim R - degreeLength R` として扱える。
- base-point-free 判定は `B` による saturation を用いる。
- `canonicalNefData(R,a,H,IrrelevantIdeal=>B)` が存在する。
- `canonicalNefThresholdData` と `canonicalContractionData` にも、`H` と `B`
  を受け取る多重次数用の入口がある。
- `completeLinearSystemGraphDataMultigraded` は、必要な境界で caller-supplied
  polarization に沿った diagonal subalgebra を構成できる。
- `bigradedReesProjection` は相対次数を含む grading を既に生成している。
- `GraphMorphism` は irrelevant ideal を保持できる。

これらの現状と測定結果は
[`MULTIGRADED-DESIGN.md`](MULTIGRADED-DESIGN.md) と
[`STAGE1-MEASUREMENT-RESULTS.md`](STAGE1-MEASUREMENT-RESULTS.md) に記録されて
いる。

不足している中心部分は、これらの多重次数対応関数を top-level MMP loop に
接続し、各 birational step の出力から次の状態を自動的に作ることである。

## 状態データの設計

最初は新しい class を導入せず、検査可能な `HashTable` として実装してよい。
概念上は次の形になる。

```m2
state = new HashTable from {
    "ring" => R,
    "canonicalIndexMultiple" => a,
    "polarization" => H,
    "irrelevantIdeal" => B,
    "gradingData" => gradingData
    }
```

`gradingData` は少なくとも次を記録する。

- 次数行列と `degreeLength R`
- block lower triangular 構造を与える変数ブロック
- 各ブロックに対応する irrelevant ideal の因子
- 現在までに行った regrading の写像
- 元の表示へ戻る、または divisor class を移送するために必要な写像

### 状態の不変条件

すべての MMP iteration の入口と出口で、次を確認する。

1. `R` は正に次数付けられた許容可能な block lower triangular 表示を持つ。
2. `B` は `R` の ideal であり、現在の多重射影表示の irrelevant locus を表す。
3. `H` は `R` 上の divisor であり、Cartier 性と ample 性の証明データを持つ。
4. `a > 0` であり、`a*K_R` の Cartier 性が `B` を使って検証されている。
5. 幾何学的次元は grading rank を引いた値で計算される。
6. birational map、contraction graph、relative model graph の次数写像が互換で
   ある。

特に `B` は後から次数行列だけを見て毎回推測するのではなく、各構成が明示的に
返す。非等次数生成 ideal の Rees 環などでは、構成時に分かっていた irrelevant
ideal を失うべきではない。

## MMP の一段で行う状態遷移

現在の `threefoldMMPData` は `currentRing` と `currentIndex` を主状態として
いる。これを `currentState` に置き換え、各段階で次のように処理する。

```text
currentState
  -> canonical nef test using (R, a, H, B)
  -> nef threshold using (R, a, H, B)
  -> contraction using (R, a, H, B)
  -> relative canonical model preserving the grading tower
  -> construct and validate nextState
  -> next iteration
```

### Nef 判定と threshold

既存の多重次数 overload をそのまま top-level loop から呼ぶ。

```m2
canonicalNefData(R,a,H,IrrelevantIdeal=>B)
canonicalContractionData(R,a,H,IrrelevantIdeal=>B)
```

これにより、global sections は自然な multidegree strand として計算され、
base-point-free 判定は `B` の外側で行われる。

### Contraction と relative Proj

新しい Rees または relative Proj grading は、既存の grading の右に一成分を
付け加える。変数ブロックは block lower triangular のまま保持する。

新しい irrelevant ideal は、構成が返す新ブロックの irrelevant factor と、
旧 `B` の像から組み立てる。単に ambient ring の全変数 ideal へ置き換えない。

### Flip 後の状態

`relativeCanonicalModelData` は `nextRing` だけでなく `nextState` を返すように
拡張する。少なくとも次を含める。

- flip 後の多重次数環
- flip 後の irrelevant ideal
- 新しい grading data
- 新しい canonical index multiple
- 次の iteration で使う ample Cartier class とその証明データ

最後の polarization の自動選択は、残っている数学的な設計課題である。相対的
ample class と基底からの ample class の十分正な組合せを使うか、許容 grading
の ample chamber の内部から Cartier class を選ぶ必要がある。最初の実装では
構成関数が生成した候補を検証して採用し、自動選択できない場合には
`inconclusive` と証明データを返す。根拠なしに「十分大きい」係数を固定しない。

## 再次数付けと grading の圧縮

次数 rank の増加自体は誤りではないが、不要な rank と変数増加は抑える。
ただし圧縮は次のデータを返せる場合だけ行う。

- 元 grading から新 grading への整数行列
- irrelevant locus が保たれることの検査
- `K`、`H`、contraction divisor の移送
- 必要な multidegree strand が同一の section ring を与えることの検査

この条件を満たさない diagonalization や flattening は、MMP state を更新する
操作としては使用しない。外部 package が単次数または双次数入力しか受けない
場合には、一時的な境界表現を作ってもよいが、計算後は元の `currentState` と
明示的な対応を保つ。

## Stein factorization との境界

現在の `SteinFactorization` は、変数が `(positive,0)` または
`(0,positive)` に分かれる block diagonal な双次数入力を仮定する。一方、MMP
が自然に生成する tower は rank `r` の block lower triangular grading である。

反復的な多重次数 MMP を完成させるには、次のどちらかが必要になる。

1. global Hom の構成を rank `r` の block lower triangular grading に一般化する。
2. Stein 境界だけで証明付きの一時的 regrading を行い、結果を元の grading
   tower へ戻す。

Stage 1 では後者として polarization に沿う diagonal subalgebra を使用した。
小さい例では有効だったが、循環被覆例の 35 変数化や、別途測定された
`steinHomData` の高コストを考えると、これをすべての段階の既定解にはできない。

既知の normal connected target が構成そのものから得られる場合には、同じ
target を再発見する重い global Hom 計算を避けられる fast path も検討する。
ただし target の正規性、連結ファイバー、graph との整合性を検証し、単なる
caller assertion にはしない。

## 段階的な実装計画

### Phase 1: top-level の多重次数入口

最小の公開 API を追加する。

```m2
threefoldMMPData(R,a,H,IrrelevantIdeal=>B)
```

この overload は最初の iteration で必ず
`canonicalNefData(R,a,H,IrrelevantIdeal=>B)` と
`canonicalContractionData(R,a,H,IrrelevantIdeal=>B)` を呼ぶ。既存の
`threefoldMMPData(R,a)` と certified-prefix API は互換性のため維持する。

### Phase 2: `currentState` と `nextState`

top-level loop の内部状態を `Ring` 中心から state 中心へ変更する。
`mmpStepRecordData` と `relativeCanonicalModelData` に grading、`B`、polarization
の遷移情報を追加し、次の iteration で再推測せず利用する。

### Phase 3: grading-preserving relative model

relative canonical algebra と Rees algebra が、入力 grading を残したまま新しい
相対次数を追加するよう統一する。すべての ring map に degree map を付け、
source、target、graph の irrelevant ideal を明示的に保持する。

### Phase 4: Stein 境界の解消

rank `r` の global Hom、証明付き regrading、または検証済み target fast path
を実装する。少なくとも、自然な 9 変数の循環被覆入力を 35 変数の恒久的な
作業状態へ変換せずに最初の contraction を完了できるようにする。

### Phase 5: 安全な grading 圧縮

同値な次数方向や不要になった相対方向を検出し、証明データ付きで rank を下げる
補助関数を追加する。これは正しさに必要な Phase 1--4 の後に行う。

## テスト方針

### 単体テスト

- caller-supplied `H` と `B` が top-level からすべての BPF 判定まで同一 object
  として渡る。
- grading rank `r` に対して幾何学的次元が `dim R-r` になる。
- Rees/relative Proj 後に grading rank、変数ブロック、`B` が期待どおり更新
  される。
- 非等次数生成 ideal でも `B` を誤って再推測しない。
- `H` または `B` が別の ring 上にある場合は明示的に失敗する。
- monograded の既存 API と結果が変わらない。

### 結合テスト

1. `P1 x P2` と `Bl_p(P3)` で既存の多重次数 nef/threshold の結果を再現する。
2. Rees/relative Proj を二回続ける小例で grading rank が一段ずつ増え、その
   状態のまま BPF 判定まで進める。
3. Stein 境界を通る例で、一時的表現から返った target と元の grading state
   の対応を検証する。
4. 既存の monograded MMP テスト一式を回帰試験として実行する。

### 最重要の受け入れテスト

循環被覆の flipping side の自然な多重次数表示を直接入力し、事前に作った
`flipStep` を渡さず、一回の top-level 呼出しで次を得る。

```text
input X-
  -> nef=false
  -> small K-negative contraction
  -> nonidentity relative canonical model
  -> stepType=flipping
  -> X+
  -> nef=true
  -> terminationType="minimal model"
  -> numberOfSteps=1
```

期待する呼出し形は次である。

```m2
result = threefoldMMPData(
    Xminus,index,Hminus,IrrelevantIdeal=>Bminus)
```

合格条件は以下。

- certified prefix を使用しない。
- contraction graph と post-flip ring を手書きしない。
- 最初の入力を恒久的な 35 変数 monograded state に flatten しない。
- 一般の nef 判定が最終モデルで `true` を返す。
- 記録される MMP step は一つだけである。
- 実行時間と各主要段階の変数数・grading rank を測定して記録する。

## 完了条件

この方針の最初の実装は、次をすべて満たした時点で完了とする。

1. top-level MMP driver が caller-supplied `H` と `B` を受け取る。
2. MMP loop が各段階で `Ring` ではなく検証済み state を引き継ぐ。
3. relative Proj/flip が新しい grading、irrelevant ideal、polarization を含む
   `nextState` を返す。
4. flattening は明示的で検証可能な package 境界に限定される。
5. 循環被覆の一回 flip 例が raw input から最後まで一回の driver 呼出しで走る。
6. 既存の monograded API とテストが維持される。

## 非目標

- 任意の Cox ring や任意の多重次数環を最初から扱うこと。
- toric fan の専用判定を一般 MMP driver の正しさの根拠にすること。
- 証明なしの固定 truncation bound や固定された「十分大きい」係数に依存する
  こと。
- 論文の monograded output specification を直ちに変更すること。

当面の対象は、MMP の Rees、product、relative Proj 構成が自然に生成する
block lower triangular で正の対角成分を持つ grading tower に限定する。この
限定でも今回の一回 flip 例を含み、現状の end-to-end 実行を妨げている主要な
表現上の問題を直接解消できる。
