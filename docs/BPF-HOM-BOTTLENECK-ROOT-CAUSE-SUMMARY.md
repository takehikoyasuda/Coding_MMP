# BPF/nef判定停滞の根本原因：まとめ（2026-08-15）

**Status**: セッションのまとめ。詳細な計測ログは各節末尾のリンク先を参照。
**関連**: [`TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md`](TORIC-HYPERSURFACE-FLIP-MMP-DESIGN.md)
10節、[`ITERATED-MULTIGRADING-MMP-PLAN.md`](ITERATED-MULTIGRADING-MMP-PLAN.md)、
メモリ `bpf-construction-dominates-assessment` / `multigrading-rank-not-hom-cost-driver`。

## 1. 何を調べていたか

新しい three-dimensional flip の例（6変数・rank2のVGIT toric ambient
hypersurface候補）を、既知の縮約先や certified prefix を一切与えない
「raw driver」（`threefoldMMPData(R,a,H,IrrelevantIdeal=>B)`）で最初から
最後まで自動的に走らせようとした。

## 2. 候補の検証は成功した

以下は全て cpu 2秒以内で正しく通過した（
[`scripts/toric-hypersurface-rank2-probe.m2`](../scripts/toric-hypersurface-rank2-probe.m2)）。

- 方程式が素イデアルを生成し、座標環が正規整域である。
- `multigradedBlockData` が、`IrrelevantIdeal` オプションを与えずに
  `B=(u0,u1)*(x,y0,y1,y2)` と `geometricDimension=3` を自動導出した。
- `canonicalDivisor` が `K_X=(-1,0)`（設計どおりのadjunction予想と一致）を
  返し、しかも **`K`自体が既に Cartier**（指数1。循環被覆例より単純）。
- 偏極 `H=(1,1)` も Cartier。

## 3. しかし raw driver の nef 判定は完走しなかった

`canonicalNefData(R,1,H,IrrelevantIdeal=>B)` は27分以上・メモリ5GB超で
打ち切りとなった。

## 4. 詰まっている場所を特定した

コードを読み、実際に呼ばれているのは `canonicalScaledNefDataInternal` 内の
「$L=2K+H$ の倍数 $m\cdot L$（$m=1,2,\ldots$）に対して
`isBasePointFreeDivisor` を順に試す」ループだと判明。3次元では
negative-curve shortcut が常にコード上到達不能（dead code）であることも
確認した。

このループを [`scripts/toric-hypersurface-bpf-sweep-probe.m2`](../scripts/toric-hypersurface-bpf-sweep-probe.m2)
で直接再現・計測：

| $m$ | 所要 cpu 時間 |
| --- | ---: |
| 1 | 約0.09秒 |
| 2 | 約69秒（約770倍） |
| 3 | 27分超で打ち切り |

これは、構造的に全く異なる巡回被覆例（$m=1$: 約95秒、$m=2$: 7分超で打ち切り）
とほぼ同じコスト増大パターンである。6変数という入力サイズの小ささは、この
ボトルネックを一切軽減しなかった。

## 5. `divisorToModule` 内部を段階ごとに計測した

[`scripts/toric-hypersurface-divisortomodule-profile.m2`](../scripts/toric-hypersurface-divisortomodule-profile.m2)
で `divisorToModule`（`WeilDivisors.m2`）と `isBasePointFreeDivisorInternal`
（`MMPComputation.m2`）の全ステップを再実装し、$m=2$（cpu約71秒）の内訳を
計測した。

| ステップ | 割合 |
| --- | ---: |
| `positivePart`/`negativePart`、`idealPower`、積、最初の`Hom`、テンソル積 | 0.2% |
| **最終 `Hom(dualModule,R^1)`（二重双対 = reflexive hull完成）** | **84%（約59.5秒）** |
| `basis`/`ann`（査定側） | 15% |

`positivePart` は予想どおり `x=0` の2つの既約成分（{quadratic(u)=0}と
{quartic(y)=0}、これは**この超曲面族の一般次数(-2,4)の単項式が3種類しか
ないことから幾何学的に強制される、係数選びとは無関係の構造**）に分解して
いた。コストのほぼ全てが「3つの異なる height-one prime を組み合わせた後の
最終 `Hom`」という一点に集中していることが判明した。査定側（`ann`/
`saturate`）は既存メモリの知見どおり小さい割合にとどまった。

## 6. 多重次数のランク自体は原因ではないと確認した

同じ超曲面方程式を変数名だけ変え、rank 1（単一次数、$F$ の斉次性を自動的に
保つ線形汎関数 $(a,b)\mapsto a+2b$ で構成）にregradingし、同じ計測を
[`scripts/toric-hypersurface-monograded-comparison-profile.m2`](../scripts/toric-hypersurface-monograded-comparison-profile.m2)
で再実行した。

| ステップ | rank 2 | rank 1 |
| --- | ---: | ---: |
| `Hom(dualModule,R^1)` | 約59.5秒 | **約59.5秒** |

ほぼ完全に一致した。この`Hom`計算は irrelevant ideal `B` を一切参照しない
ため（`B`は後続の`ann`/`saturate`でのみ使う）、これはrank以外を揃えた
クリーンな比較になっている。

## 7. 結論

1. **入力サイズ（変数の少なさ）はこのボトルネックを軽減しない。**
   6変数の候補でも35変数級の循環被覆例と同じコスト増大が起きた。
2. **ボトルネックは変数数でも多重次数のランクでもなく、divisorが組み合わせる
   height-one primeの個数・複雑さに応じて`Hom(Module,R^1)`（Macaulay2コア
   自体のHom/Ext実装）が急増することにある。**
3. これにより、[`ITERATED-MULTIGRADING-MMP-PLAN.md`](ITERATED-MULTIGRADING-MMP-PLAN.md)
   の中心仮説（「単次数への恒久的flatteningを避ければBPF/nef判定コストが
   改善する」）は、**このボトルネックに関しては反証された**。Phase 1--3で
   実装したgrading保存の入口自体はソフトウェア設計として無駄ではないが、
   速度改善という動機での追加投資は正当化されない。
4. cost-aware threshold探索（Phase C）は別のループ（候補有理数の試行順序）
   を最適化するものであり、この$m$-sweepには直接効かない。
5. 循環被覆・toric hypersurfaceという構造的に異なる二つの族で同じ
   `Hom`ボトルネックが再現したことから、**別の族を探しても同じ壁に当たる
   可能性が高い**。

## 8. 次に投資すべき方向（未着手）

`Hom(Module,R^1)`（二重双対）のコストが、組み合わされるprimeの個数・codim・
次数にどう依存するかを直接調べ、そこを回避・高速化する方向。GF(p)還元は
1.2--2.3倍止まりで桁違いに足りない（`gfp-reduction-benchmark-positive`）ため、
より大きい投資（アルゴリズムの見直し、あるいは`Hom`を経由しない代替の
reflexive hull構成）が必要になる。
