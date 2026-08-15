# Toric hypersurface flip 候補と多重次数 MMP の実装方針

**Status**: Working design note; end-to-end で完走する新しい flip 例は未確立  
**Date**: 2026-08-15  
**Branch at investigation**: `feature/multigraded-stage1`

## 1. 目的

このメモは、計算量の小さい三次元 MMP の実例を探す過程で得られた知見と、
今後の実装方針をまとめたものである。

求めている例は、単に flip の出力を個別に計算できる例ではない。次の全段階を、
入力環から top-level driver が自動的に実行できる必要がある。

1. `K_X` の nef 性を判定する。
2. nef threshold を入力から計算する。
3. threshold divisor の線形系から縮約を構成する。
4. Stein 分解により連結ファイバー化する。
5. 縮約が small であることを判定する。
6. relative canonical model として flip を構成する。
7. flip 後のモデルへ状態を移し、minimal model または Mori fibre space まで続ける。

次の入力・近道は、この目的には使用しない。

- 既知の縮約先を caller から与えること。
- 既知の Rees projection を正解として再利用すること。
- certified prefix として最初の MMP step を与えること。
- flipping curve や extremal ray を入力時点で既知と仮定すること。

これらは既存の部分実装を検証するテストには有用だが、MMP が縮約を自力で発見して
最初から最後まで計算した例にはならない。

## 2. これまでの例の状況

### 2.1 巡回被覆例

既存の四次巡回被覆例は、局所 toric circuit

```text
v1 + v2 = 2 v3 + v4
```

を大域化し、flip 後に `K` が nef になるようにしたものである。幾何学的には目的に
近いが、計算量が大きい。

自然な多重次数表示では9変数に抑えられるが、記録された主な所要時間は次のとおりで
ある。

- 環の構成: 約1.2秒。
- Cartier 判定: 約0.2秒。
- `2K` の BPF 判定: 約0.3秒。
- `canonicalScaledNefDataInternal` の最初の候補: 約95秒。
- 次の候補: 7分以上で未完了。
- full scaled-nef call: 15分で未完了。

したがって、35変数への恒久的な単次数化を避けても、reflexive divisor module と BPF
判定が依然としてボトルネックになる。

### 2.2 被覆を外した自然な Rees 表示

同じ局所 circuit を被覆なしで自然な Rees 表示にすると、8変数・6関係式まで小さく
できる。選んだ偏極では `canonicalNefData` が約65秒で完了した。しかし、threshold
および縮約は6分以上で完了しなかった。

この例は数学的には小さいが、現行 driver が end-to-end で完走する例ではない。

また、この例の縮約先は Rees 構成から既知であるが、それを使って縮約計算を省略する
fast path は今回の目的と異なるため採用しない。

### 2.3 同じ circuit 族をさらに小さくする限界

primitive な4-ray circuit を調べた範囲では、dual semigroup の Hilbert basis の最小数は
5であり、既存の `v1+v2=2v3+v4` が既にこの最小値を達成する。

二次・三次被覆、反復二重被覆も試したが、自然な Rees 表示での nef/BPF 計算は改善
しなかった。このため、同じ circuit と巡回被覆の組合せを縮小する探索は一旦終了し、
別の flip 族へ移る。

## 3. 対角線形系は何のためにあるか

### 3.1 幾何学的に必須ではない

現在の multigraded contraction path は、偏極 `H` に沿う diagonal subalgebra を作り、
source を一時的に単次数環へ変換する。

```text
R  (Z^r-graded)
  -> R^(H)  (Z-graded)
  -> graph of |D|
  -> Stein factorization
```

この `H`-diagonalization は、縮約の幾何そのものに必要なのではない。現在の
`SteinFactorization` が、source block と target block に分かれた block-diagonal な
双次数環だけを受け取るという実装上の制約を満たすために使われている。

該当箇所は
[`completeLinearSystemGraphDataMultigraded`](../MMPComputation.m2#L1005-L1058)
であり、内部で
[`diagonalSubalgebraData`](../MMPComputation.m2#L963-L978)
を無条件に呼んでいる。

### 3.2 多重次数を積み重ねれば避けられる部分

relative Proj または Rees 構成のたびに新しい相対次数を追加し、graph にもさらに一つ
の次数を追加すれば、概念上は次の形にできる。

```text
R  (Z^r-graded)
  -> graph ring  (Z^(r+1)-graded)
  -> multigraded Stein factorization
```

この経路では source を `H` に沿って単次数化する必要はない。

ただし、縮約先が未知の場合、threshold divisor `D` の ray section algebra

```text
direct sum over n >= 0 of R_(nD)
```

に相当する情報は依然として必要である。避けられるのは source 全体の `H`-diagonal
展開であり、縮約を定める `D` の切断計算そのものではない。

## 4. 別族としての toric ambient hypersurface

完全 toric な正次元射影多様体では `K` は nef にならないため、「純 toric で一回 flip
した直後に minimal model」という設計には構造的な限界がある。一方、toric ambient
の中の hypersurface では adjunction により `K_X` を調整できる。

このため、次の候補を検討している。

### 4.1 階数2 VGIT hypersurface 候補

6個の Cox 変数に次の次数を与える。

| 変数 | 個数 | 次数 |
| --- | ---: | --- |
| `u0,u1` | 2 | `A=(1,0)` |
| `x` | 1 | `B=(0,1)` |
| `y0,y1,y2` | 3 | `C=(-1,1)` |

ambient は階数2の toric 4-fold である。初期 chamber を

```text
cone(A,B)
```

とし、irrelevant ideal を

```text
(u0,u1) * (x,y0,y1,y2)
```

とする。

この中に multidegree `(-2,4)` の hypersurface を取る。一般形は概ね

```text
x^2 * quadratic(y)
+ x * linear(u) * cubic(y)
+ quadratic(u) * quartic(y)
```

の形である。

adjunction による期待される canonical class は

```text
K_X = (-1,0)
```

である。初期偏極として

```text
H = (1,1)
```

を取ると、期待される threshold は `1`、threshold divisor は

```text
K_X + H = B = (0,1)
```

となる。

VGIT の壁通過では、一方の例外集合が `P^1`、反対側が平面二次曲線になることが期待
される。`K_X` は壁の両側で符号を変えるので、期待される変換は flop ではなく flip
である。

### 4.2 入力サイズ

この候補の利点は次のとおりである。

- Cox 変数6個。
- 関係式1本。
- threshold divisor `B` の strand は7切断。
- 初期偏極 `H=(1,1)` の strand は11切断。

正規整域になる一般的な方程式を用いた診断では、complete-linear-system graph の構成
までに次が確認された。

- `B` の Cox strand: 7切断。
- `OO(D)` の multidegree-zero strand: 同じ7切断。
- `H` の strand: 11切断。
- graph の source variables: 11。
- graph の target variables: 7。
- graph ideal generators: 91。
- graph 構成時間: 約0.28秒。

Stein 分解、smallness、flip、flip 後の MMP はまだ完走していない。

### 4.3 無効になった初期測定

最初の probe では Macaulay2 の改行規則を誤解し、複数行の hypersurface 方程式を括弧
で囲まなかった。その結果、実際には先頭項

```text
x^2 * quadratic(y)
```

だけが方程式として代入され、環は非整域になっていた。

この無効な環で得られた nef、threshold、BPF の時間は、候補の性能評価には使用しない。
特に、そこで観測された分数ごとの具体的な時間は破棄する。

今後の probe では最低限、計算開始前に次を検証する。

```text
isPrime ideal(F)
isDomain R
isNormal R
```

`WeilDivisors` を使う処理は、正規整域の確認後にのみ実行する。

## 5. Threshold 候補の探索順序

### 5.1 現在の問題

現在の threshold algorithm は、rationality theorem が与える候補を値でソートし、その
リスト上で二分探索を行う。

これは BPF test の回数を減らすが、各 test の計算量が一様であることを暗黙に仮定して
いる。

候補 `t=p/q` では、実際に調べる Cartier divisor は

```text
L = q*a*K_X + a*p*H
```

であり、base-point-free theorem に現れる整数も

```text
N = a*q
```

となる。分母 `q` が大きいほど、divisor module、reflexive hull、必要な graded strand
が急速に大きくなる可能性がある。

したがって、候補数だけを最小化する二分探索は、wall-clock time を最小化しない。

### 5.2 正しさを保つ低コスト順探索

単に「分母の小さい順に調べ、最初に nef だった候補を threshold とする」ことはでき
ない。値の小さい未検査候補が残る可能性があるためである。

正しい cost-aware algorithm は次の形にする。

1. 非 nef と証明された下端 `alpha` と、nef と証明された上端 `beta` を保持する。
2. 開区間 `(alpha,beta)` 内の未検査候補に cost score を付ける。
3. 最も安い候補を選ぶ。
4. nef なら `beta` を更新し、非 nef なら `alpha` を更新する。
5. 新しい区間外の候補を削除する。
6. 区間内に候補がなくなれば `beta` を threshold とする。

最初の cost score は、少なくとも次の辞書式順序でよい。

```text
(denominator q,
 estimated section-strand size,
 divisor-expression size)
```

これにより厳密性を保ったまま、小さい分母を優先できる。

### 5.3 分母順だけでは解消しない場合

真の threshold の直前に、rationality theorem 上許される高分母候補がある場合、その
候補が非 nef であることを最終的には証明する必要がある。探索順の変更だけでは、その
test 自体を消せない。

この場合は、安い候補の base locus から負曲線を抽出し、

```text
(K_X + t H).C < 0
```

が成り立つ区間全体を一度に非 nef と証明する方法を併用する必要がある。

この曲線は入力から計算によって発見されるので、flipping curve を事前に与える近道
ではない。

現状では `canonicalScaledNefDataInternal` の negative-curve shortcut は三次元で到達
不能になっている。三次元でも、通常の BPF loop の途中で得た base locus に対して
negative-curve witness を試すように接続する必要がある。

## 6. Divisor module と multigraded section の診断

### 6.1 `divisorToModule` がしていること

`WeilDivisors` の内部関数 `divisorToModule` は、Weil divisor `D` の正部分と負部分を
height-one prime ideals の積として構成し、`Hom` と double dual を使って

```text
O_Spec(R)(D)
```

に対応する階数1反射的加群を返す。

`MMPComputation` の BPF 判定は
[`isBasePointFreeDivisorInternal`](../MMPComputation.m2#L230-L235)
で次を行う。

1. `M=divisorToModule(D)` を作る。
2. `basis((0,...,0),M)` を取る。
3. evaluation cokernel の annihilator を作る。
4. その ideal を irrelevant ideal `B` で saturate する。

bare integer の `basis(0,M)` ではなく、完全な長さの零ベクトルを使っている点は正しい。

### 6.2 最初に疑われた不一致と、その訂正

無効な非整域 probe では、Cox strand が7本なのに `mapToProjectiveSpace` が1本だけを
返した。この結果から一時的に divisor module と Cox strand の不一致を疑った。

しかし、正規整域となる方程式へ修正すると、

```text
basis({0,1},R)
```

と

```text
basis({0,0},OO(D))
```

はいずれも同じ7本を返した。

したがって、この候補に関して `divisorToModule` 本体が section を失うという診断は
撤回する。

### 6.3 `mapToProjectiveSpace` に残る具体的な multigrading bug

`mapToProjectiveSpace` は `OO(D)` を graded ideal に埋め込み、次数シフト `d1` を得る。
その後、零因子 `D=0` のときに定数 `1` だけから非斉次 kernel ができるのを防ぐため、
特別処理を行う。

現在の `WeilDivisors` は、`d1` がリストの場合にも

```m2
if d1#0 == 0 then ...
```

と最初の成分しか確認しない。

今回の threshold divisor のシフトは

```text
d1 = {0,1}
```

である。これは零ベクトルではないが、最初の成分が0なので零次数と誤認され、全切断に
最初の環変数 `u0` が掛けられる。

期待される切断:

```text
x,
u0*y0, u0*y1, u0*y2,
u1*y0, u1*y1, u1*y2
```

実際に返る代表:

```text
u0*x,
u0^2*y0, u0^2*y1, u0^2*y2,
u0*u1*y0, u0*u1*y1, u0*u1*y2
```

section 数と斉次関係の kernel は通常変わらないが、人工的な共通因子 `u0` が入る。
これにより次の危険が生じる。

- literal な base locus に偽の成分 `u0=0` が現れる。
- rational map の見かけ上の定義域が小さくなる。
- section representatives を直接使う後段処理が誤る可能性がある。
- 不要な次数上昇により Gröbner 計算が重くなる。

最低限の修正は

```m2
if all(d1,e -> e == 0) then ...
```

であり、零ベクトルの場合にだけ defense を発動させることである。

### 6.4 `Spec R` と `MultiProj_B R` の差

より一般には、`divisorToModule` が作るのは `Spec R` 上の反射的加群であり、MMP が
扱いたいのは

```text
X = MultiProj_B(R)
```

上の層である。

現在の実装は、module の次数0部分を先に取り、その evaluation base locus を後から
`B` で saturate する。後段の saturation は irrelevant locus 上の偽の base point を
除けるが、module の次数0部分に最初から入っていない global section を追加することは
できない。

ただし、次の条件下では現在の方法を正当化できる。

- `R` が正規整域である。
- `OO(D)` が階数1反射的加群である。
- `V(B)` の各成分の余次元が2以上である。
- grading と irrelevant ideal が実際の Cox/multiProj presentation に対応する。

反射的加群は余次元2以上の集合を除いた開集合から一意に延長されるため、この条件下
では `OO(D)` の multidegree-zero part を quotient 上の切断として使える。

条件を満たさない入力では、次のいずれかが必要になる。

- embedded rank-one module を `B` で saturate してから切断を取る。
- localizations/Čech data から section module を構成する。
- Cox provenance がある場合、証明付き class degree の strand を直接使う。
- 条件を証明できない場合は誤った Boolean を返さず `inconclusive` とする。

## 7. 推奨する実装方針

### Phase A: multigraded section data の統一

`WeilDivisors` の `divisorToModule` 全体を変更するのではなく、MMP 側に内部関数

```text
multigradedDivisorSectionData(D,B)
```

を追加する。

返り値は少なくとも次を持つ。

```text
divisor
divisorModule
embeddedIdeal
embeddingShift
zeroDegree
sectionMatrix
sectionImages
baseIdeal
irrelevantIdeal
assumptionChecks
```

この関数は次を行う。

1. ring、grading rank、`B` の整合性を確認する。
2. 正規整域の証明データ、または caller state の provenance を確認する。
3. `OO(D)` が階数1反射的であることを確認する。
4. `V(B)` の余次元条件を確認する。
5. 必要なら embedded ideal/module を `B`-saturate する。
6. 完全な零次数ベクトルで section basis を計算する。
7. 零ベクトル判定を全成分で行い、人工的な共通因子を避ける。

BPF 判定、`mapToProjectiveSpace` 相当の map、contraction graph は、別々に section を
再構成せず、同じ `sectionData` を共有する。

これにより、BPF 判定で使った線形系と graph を作る線形系が一致する。

### Phase B: Cox provenance を持つ場合の section oracle

state が divisor class と multidegree の対応を証明付きで保持している場合、

```text
H^0(X,O(D)) = R_[D]
```

として対応する strand を直接取る経路を追加する。

これは既知の縮約先を与える fast path ではない。入力 grading から complete linear
system を計算する section oracle であり、縮約先、Stein factor、smallness、flip は従来
どおりアルゴリズムが計算する。

使用条件として次を記録・検証する。

- class group から grading lattice への同型または明示写像。
- `D` と class degree の対応。
- irrelevant ideal。
- factorially graded/Cox presentation であることの provenance。

### Phase C: threshold search の cost-aware 化

値の中央値による二分探索を、区間を保った cost-aware candidate search に置き換える。

各 test の結果は cache し、同じ rational candidate を二度計算しない。返り値には

```text
candidate
denominator
estimatedCost
actualCpuTime
nefCertificate
```

を記録し、今後の cost model を改善できるようにする。

negative-curve witness を三次元の通常経路へ接続し、一つの曲線で候補区間全体を除外
できる場合には高分母 BPF test を省く。

### Phase D: grading-preserving contraction graph

現在の `H`-diagonal source を恒久的な作業状態として使わない。graph の target degree
を現在の grading tower の右に追加し、rank `r+1` の block-lower-triangular graph ring
を作る。

その後の Stein 境界については次の順で実装を検討する。

1. rank `r` source に対する global Hom/Stein の一般化。
2. 元の grading tower へ戻せる証明付き一時 regrading。

既知 target の注入による省略は行わない。

### Phase E: toric hypersurface 候補の検証

6変数・1方程式の候補について、次を順に証明・測定する。

1. hypersurface equation が素イデアルを生成する。
2. Cox ring が正規整域である。
3. chamber と irrelevant ideal が正しい。
4. hypersurface が Q-factorial terminal threefold を与える。
5. adjunction で `K_X=(-1,0)` となる。
6. `H=(1,1)` が ample Cartier である。
7. threshold wall の例外集合が期待どおり曲線である。
8. `K` の交点符号が flip であることを示す。
9. raw `threefoldMMPData` が threshold と縮約を自動発見する。
10. Stein、smallness、relative canonical model、次状態まで完了する。
11. 最終的に minimal model または Mori fibre space へ到達する。

## 8. 必要な回帰テスト

### 8.1 Section extraction

- 正規整域の6変数 hypersurface で `D=(0,1)` の切断が7本になる。
- `basis(classDegree,R)` と `OO(D)` の零次数部分が一致する。
- section representatives に人工的な共通因子 `u0` が付かない。
- `D=0` の既存 defense は引き続き斉次な point target を返す。
- 非整域入力は section/divisor 計算前に明示的に拒否される。

### 8.2 BPF と irrelevant ideal

- explicit `B` が module section、evaluation cokernel、base-locus saturation の全段階で
  同じ object として使われる。
- `codim V(B)>=2` の検査結果が証明データに残る。
- `B`-saturation 前後で section module が変わる人工例を追加し、未検証入力で
  silent false result を返さない。

### 8.3 Threshold

- cost-aware search と従来の sorted linear search が同じ threshold を返す。
- test 順序は分母の小さい候補を優先する。
- cache により同一候補を再計算しない。
- negative-curve certificate による区間除外が、候補ごとの BPF 判定と同じ結論を返す。

### 8.4 End-to-end

- 既知の縮約先を入力しない。
- certified prefix を入力しない。
- threshold divisor の complete linear system から graph を構成する。
- Stein factorization を実際に計算する。
- smallness を自動判定する。
- flip 後の状態を自動生成する。
- MMP が terminal branch まで到達する。

## 9. 現時点の結論

現行コードで最初から最後まで完走する新しい flip 例は、まだ見つかっていない。

ただし、toric ambient hypersurface は、巡回被覆とは異なる有望な族である。現在の候補は
6変数・1方程式で、正規整域上では divisor module が期待する7切断を正しく返し、graph
構成も小さい。

次に行うべきことは、既知 target を使う近道ではなく、次の三点である。

1. multigraded section data を一箇所へ統一し、`mapToProjectiveSpace` の零ベクトル判定を
   修正する。
2. threshold 候補を cost-aware に探索し、三次元でも negative-curve witness を利用する。
3. grading を積み重ねたまま graph/Stein へ渡す境界を実装する。

この基盤の上で、6変数 toric hypersurface 候補を raw driver に通すのが次の実験である。
