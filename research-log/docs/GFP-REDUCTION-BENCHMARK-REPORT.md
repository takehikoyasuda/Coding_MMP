# 有限体 (GF(p)) 還元によるBPF判定ベンチマーク

**Status**: Completed, positive but bounded result
**Date**: 2026-08-13
**Work location**: Scratchpad only (no repo changes, no commits)
**Branch**: `feature/multigraded-stage1` (unchanged)

---

## 背景・目的

`algorithmic_mmp_bpf_fastpath_notes.md` §3 は、Gröbner基底・saturation・syzygy等の計算が
QQ より F_p 上で大幅に速くなることが多い（coefficient swellと多倍長整数演算を避けられるため）
という一般論から、QQ→F_p 還元を有力な高速化レバーとして提案している。

`BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md` で、既存の `isBasePointFreeDivisorInternal`
（`weilDivisorToModule` 構成 + `ann`/`saturate` 査定）のコストが n（$D=nK$ の $n$）とともに
ほぼ全面的に構成側に集中することを確認済みである。本実験は、**既存パイプラインの形を一切変えず**、
係数体だけを QQ から `ZZ/p` に置き換えて同じ計測を行い、実際にどれだけ速くなるか、その効果が
n とともにどう推移するかを直接測定する。

---

## 環境・手法

- Macaulay2 1.26.06
- `STAGE2-MEASUREMENT-RESULTS.md` / `BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md` と
  全く同じ singular な多重次数環 `Z`（canonical index 2）の構成を、係数体だけ `kk = ZZ/p` に
  置き換えて再構築（コーン・Hilbert basis等の組合せ論的な部分は体に依存しないため不変）。
- `n*K` に対する構成（`weilDivisorToModule`）と査定（`basis`+`coker`+`ann`+`saturate`）を
  `cpuTime()` で分離計測。n=1..14（QQ版で計測済みの範囲と同一）、n ごとに独立したM2プロセス。

### 素数の選定とサニティチェック

`p = 32003` を最初に試し、以下の全チェックに合格（canonical indexが2であるため p=2 等の
小さい素数は避けた。フォールバックは不要だった）:

| チェック項目 | 結果 | 期待値 |
|---|---|---|
| `dim Xproj` | 4 | 4 |
| `isNormal Xproj` | true | true |
| `degreeLength Z` | 2 | 2 |
| `dim Z` | 5 | 5 |
| `bpf(1*K)` | false | false（QQ版と一致） |
| `bpf(2*K)` | false | false（QQ版と一致） |

---

## 結果

全14n完走、stallなし（QQ版で発生したn=15の停止を再現する必要はなく、比較範囲のn=1..14で
十分だった）。bpf結果は**全nでQQ版と完全一致**（両方とも全てfalse）。

| n | 構成(s) | 査定(s) | 合計(s) | 構成の割合 |
|---|---|---|---|---|
| 1 | 0.0204 | 0.0952 | 0.1156 | 17.7% |
| 2 | 0.0487 | 0.0971 | 0.1459 | 33.4% |
| 3 | 0.2005 | 0.0680 | 0.2686 | 74.7% |
| 4 | 0.3754 | 0.0707 | 0.4461 | 84.2% |
| 5 | 1.0262 | 0.0830 | 1.1092 | 92.5% |
| 6 | 1.4465 | 0.0890 | 1.5355 | 94.2% |
| 7 | 3.7334 | 0.1124 | 3.8458 | 97.1% |
| 8 | 5.3244 | 0.1232 | 5.4477 | 97.7% |
| 9 | 11.821 | 0.1866 | 12.008 | 98.4% |
| 10 | 15.754 | 0.2025 | 15.957 | 98.7% |
| 11 | 28.904 | 0.5300 | 29.434 | 98.2% |
| 12 | 35.469 | 0.6191 | 36.088 | 98.3% |
| 13 | 59.945 | 1.3141 | 61.259 | 97.9% |
| 14 | 70.738 | 1.0584 | 71.796 | 98.5% |

構成側の割合の推移はQQ版（n=1で41.6%→n=14で98.9%）とほぼ同じパターン（n=1で17.7%→n=14で
98.5%）を辿る。したがって `BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md` の結論
（ボトルネックの実質はほぼ全面的に構成側にある）は、GF(p) 上でも変わらない。

### QQ版との直接比較

| n | QQ合計(s) | GF(p)合計(s) | 高速化倍率 (QQ/GF(p)) |
|---|---|---|---|
| 1 | 0.103 | 0.116 | 0.89×（GF(p)の方が遅い） |
| 2 | 0.169 | 0.146 | 1.16× |
| 3 | 0.489 | 0.269 | 1.82× |
| 4 | 0.848 | 0.446 | 1.90× |
| 5 | 2.336 | 1.109 | 2.11× |
| 6 | 3.320 | 1.536 | 2.16× |
| 7 | 9.516 | 3.846 | 2.47× |
| 8 | 13.856 | 5.448 | **2.54×（ピーク）** |
| 9 | 28.484 | 12.008 | 2.37× |
| 10 | 37.480 | 15.957 | 2.35× |
| 11 | 69.177 | 29.434 | 2.35× |
| 12 | 82.873 | 36.088 | 2.30× |
| 13 | 140.213 | 61.259 | 2.29× |
| 14 | 166.956 | 71.796 | 2.33× |

---

## 効果の推移についての結論

**高速化倍率は n とともに広がり続けるわけではない。** n=1ではGF(p)の方がわずかに遅く
（0.89×）、n=2〜8で急速に改善し（1.16×→2.54×）、n=8でピーク（2.54×）に達したあと、
n=9〜14では**約2.3〜2.4倍という狭い帯で頭打ち**になる。n=8のピークを上回るnは以降
一つも現れない。

これは「QQ側のcoefficient swellがnとともに悪化し続け、GF(p)の相対的優位性が広がり続ける」
という素朴な予想には反する。実態は、**n=8前後で収束する、ほぼ一定の定数倍改善（約2.3倍）**
である。

---

## 位置づけ・留保

- **正しさは確認された**: 全14nでbpf結果がQQ版と完全一致。invertible-ideal実験のような
  「正しいが遅い」結果ではなく、「正しく、かつ速い」という肯定的な結果である。
- **ただし、これは定数倍の改善であり、成長曲線の形そのものを変えるものではない**。
  `BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md` で確認された、構成側（`weilDivisorToModule`）
  が支配する急増パターンはGF(p)上でも同様に残る。約2.3倍の一定倍率は、n方向の成長を
  1ステップ弱ほど後ろにずらす程度の効果に相当する。
- **まだ rigorous な証明にはなっていない**: ここで確認したのは「mod pでの計算が速く、
  boolean の答えがQQ版と一致する」という経験的事実のみである。
  `algorithmic_mmp_bpf_fastpath_notes.md` §3 が要求する
  「$H^1(X_p,L_p)=0$ の確認によるcharacteristic 0への厳密な持ち上げ」は本実験では
  一切実装・検証していない。したがって現時点でのGF(p)還元は、production的に「証明された
  BPF判定」として使えるものではなく、強いヒューリスティックな傍証にとどまる。
- 構成/査定の比率がQQ版と同じ推移を辿ることから、GF(p)還元は
  `BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md` の結論（§17の「4本のsection」案の
  効果上限が小さいこと、構成側の回避が本命であること）と矛盾せず、**直交する独立の改善**
  として、将来 character/jet ベースの section oracle 設計と組み合わせられる可能性がある。

---

## ファイル

- サニティチェックスクリプト・ログ: `gfp-sanity.m2`, `log_sanity_p32003.txt`
- 内訳計測スクリプト: `gfp-breakdown-single.m2`
- 各nの生ログ: `gflog_n1.txt` 〜 `gflog_n14.txt`
- 比較対象（既存・不変）: `bpf-breakdown-single.m2`, `log_n1.txt` 〜 `log_n14.txt`
- 関連する既存文書:
  - `BPF-CONSTRUCTION-VS-ASSESSMENT-BREAKDOWN.md`
  - `algorithmic_mmp_bpf_fastpath_notes.md`（§3）
  - `INVERTIBLE-IDEAL-CACHING-EXPERIMENT-REPORT.md`
