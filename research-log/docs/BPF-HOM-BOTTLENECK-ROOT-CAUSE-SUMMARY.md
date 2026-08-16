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

## 8. 残る課題（一般 Weil divisor の場合）

`Hom(Module,R^1)`（二重双対）のコストが、組み合わされるprimeの個数・codim・
次数にどう依存するかを直接調べ、そこを回避・高速化する方向。GF(p)還元は
1.2--2.3倍止まりで桁違いに足りない（`gfp-reduction-benchmark-positive`）ため、
より大きい投資（アルゴリズムの見直し、あるいは`Hom`を経由しない代替の
reflexive hull構成）が必要になる。

## 9. 実装した回避策（class-degree fast path）

一般の Weil divisor について `Hom`/double dual を取り除くことはできないが、
今回のように $K$ と $H$ の divisor class degree が既知の場合は、候補
$D=q aK+a pH$ を直接 free graded shift

$$
\mathcal O_X(mD) \simeq R^{\,m(qa\deg K+ap\deg H)}
$$

として表せる。この経路では `divisorToModule`、`Hom`、double dual を一切呼ばず、
degree-zero evaluation と irrelevant-ideal saturation だけを実行する。

`canonicalNefData` と `canonicalScaledNefData` に
`DivisorClassDegrees=>{degree(K),degree(H)}` を渡すとこの経路を利用する。
これは caller-supplied certificate として扱い、未指定時の既存挙動は変えない。
また、各 support prime が homogeneous principal と機械的に確認できる場合は、
通常の `isBasePointFreeDivisor` にも同じ shift fast path を適用する。

rank-2 toric hypersurface の同一例では、`m=1,...,6` の BPF sweep が従来の
`m=2` 約69秒、`m=3` 27分超の状態から、全体約2秒で完了した。判定結果は既存の
false と一致し、`make test-core` の既存回帰テストも全て通過した。

`Hom(I_{D_+},I_{D_-})` という一回の `Hom` に置き換える案も実測したが、今回の
入力では約64秒かかり、double dual 回避による実用的な改善にはならなかった。

なお、$H$ だけを class degree shift とし、$K$ 部分を通常の
`divisorToModule` で構成してから tensor する中間案も同じ例では約1.8秒で
完了した。ただしこれは $K=-\operatorname{div}(u_0)$ が特に単純な例だからであり、
一般の $K$ の double dual コストを消すものではない。

## 10. 実装した canonical-ideal / reflexive-power fast path

class degree を caller が与えない場合にも、$H$ が単一の homogeneous shift として
認識できるときは、canonical module の embedding を一度だけ計算して

$$
I_K=\operatorname{im}(\omega_R\to R),\qquad
\mathcal O_X(mK+bH)
\simeq
\operatorname{reflexivePower}(m,I_K)\otimes R^{m e+b h}
$$

という ideal 表現を使う経路を追加した。各 multiplier ごとの巨大な
`Hom(dualModule,R^1)` は呼ばず、`reflexivePower` と degree-zero evaluation のみを
行う。canonical seed は $K$ に cache するため、$m=1,\ldots,7$ の sweep で再利用される。

rank-2 toric hypersurface の同じ例では、class degree を渡さない場合でも
`canonicalScaledNefData(...,t=1/2)` の BPF sweep が約1.9秒で完了し、従来の
27分超の経路と同じ `nef=false`、multiplier列 `{1,2,3,4,5,6}` を返した。
同じ経路を含む `canonicalNefData` 全体も約2.9秒で完了し、従来どおり
`witnessType="non-nef positive perturbation"` を返した。

この shortcut は normal domain と canonical ideal embedding が利用できる場合に限り、
seed または $H$ の shift を構成できない場合は従来の一般 Weil divisor 経路へ戻る。
従って未検証の近似判定ではなく、適用条件を満たした場合だけ使う証明可能な高速化である。
