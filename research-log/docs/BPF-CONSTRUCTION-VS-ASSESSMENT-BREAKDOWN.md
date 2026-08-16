# BPF判定の内訳計測: `weilDivisorToModule`構成 vs `ann`/`saturate`査定 (n=1..14)

**Status**: Completed, informative (confirms and sharpens a prior partial observation)
**Date**: 2026-08-13
**Work location**: Scratchpad only (no repo changes, no commits)
**Branch**: `feature/multigraded-stage1` (unchanged)

---

## 背景・目的

`INVERTIBLE-IDEAL-CACHING-EXPERIMENT-REPORT.md` は、n=4 (4K) の一点に限り、既存の
`isBasePointFreeDivisorInternal`（`MMPComputation.m2:228-233`）の内訳が

- `weilDivisorToModule D` の構成（reflexive hull構成）: 0.79–0.81秒（90–97%）
- その後の `basis`+`coker`+`ann`+`saturate`（査定）: 0.06–0.10秒（残り）

であることを報告した。しかしこれは n=4 でしか測られておらず、n が大きくなるにつれてこの比率
（構成側が圧倒的多数）が保たれるのか、それとも査定側の割合も増えていくのかは未確認だった。

本実験はこの内訳を n=1..14（可能な限り高いところまで）で再計測し、比率の推移を明らかにする
ことを目的とする。`algorithmic_mmp_bpf_fastpath_notes.md` §17（「4本のsectionだけを
ann/saturateに使えばよい」というLas Vegas的判定）の効果の上限を見積もる直接の材料でもある。

---

## 環境・対象

- Macaulay2 1.26.06 (`/opt/homebrew/bin/M2`)
- `STAGE2-MEASUREMENT-RESULTS.md` / `tests/multigraded-skew-cartier.m2` と全く同じ singular
  な多重次数環 `Z`（`computeFlip` による toric flip の結果、canonical index 2、`Btrue` は
  `P#irrelevantIdeal` 由来の真の irrelevant ideal）を毎回新しいM2プロセスで再構築。
- 計測対象: `D = n*K`（`K = canonicalDivisor(Z, IsGraded=>true)`）に対する
  `isBasePointFreeDivisorInternal`相当の処理を、**既存コードを変更せず**、
  1. `M = weilDivisorToModule D`（構成）
  2. `evaluationCokernel = coker basis(zeroDegree, M)` および
     `trim saturate(ann evaluationCokernel, Btrue) == ideal 1_R`（査定）

  の2区間に分けて `cpuTime()` で計測。n ごとに独立したM2プロセスで実行（1つのnの暴走が他のnの
  結果に影響しないようにするため）。

---

## 結果

全て `bpf = false`（Stage 2データと一致）。

| n | 構成 (s) | 査定 (s) | 合計 (s) | 構成の割合 | 査定の割合 | 直前比 |
|---|---|---|---|---|---|---|
| 1 | 0.0429 | 0.0603 | 0.1032 | 41.6% | 58.4% | — |
| 2 | 0.1046 | 0.0646 | 0.1693 | 61.8% | 38.2% | 1.64× |
| 3 | 0.4137 | 0.0754 | 0.4891 | 84.6% | 15.4% | 2.89× |
| 4 | 0.7732 | 0.0752 | 0.8484 | 91.1% | 8.9% | 1.74× |
| 5 | 2.1859 | 0.1502 | 2.3361 | 93.6% | 6.4% | 2.75× |
| 6 | 3.2181 | 0.1021 | 3.3202 | 96.9% | 3.1% | 1.42× |
| 7 | 9.2790 | 0.2369 | 9.5159 | 97.5% | 2.5% | 2.87× |
| 8 | 13.5854 | 0.2702 | 13.8556 | 98.1% | 1.9% | 1.46× |
| 9 | 28.0454 | 0.4384 | 28.4838 | 98.5% | 1.5% | 2.06× |
| 10 | 36.9746 | 0.5052 | 37.4798 | 98.6% | 1.4% | 1.32× |
| 11 | 68.0059 | 1.1712 | 69.1771 | 98.3% | 1.7% | 1.85× |
| 12 | 81.5570 | 1.3157 | 82.8727 | 98.4% | 1.6% | 1.20× |
| 13 | 138.0540 | 2.1592 | 140.2130 | 98.5% | 1.5% | 1.69× |
| 14 | 165.1500 | 1.8059 | 166.9560 | 98.9% | 1.1% | 1.19× |
| 15 | — | — | stall（後述） | — | — | — |

Stage 2データ（K:0.11, 2K:0.21, 3K:0.49, 4K:0.84, 5K:2.36, 6K:3.44）との照合: 良好に一致
（2Kが約20%低め、6Kが約3.5%低め、いずれも `INVERTIBLE-IDEAL-CACHING-EXPERIMENT-REPORT.md` が
既に指摘しているセッション間の通常のばらつきの範囲内）。マシン負荷やM2バージョン差による有意な
乖離の兆候はない。

---

## 査定側の割合は n が増えても増加しない

**n=4での「構成90%超・査定10%未満」という1点だけの観測は、実際にはさらに極端になっていく
過程の途中に過ぎなかった。** n=1では査定側（0.060s）の方が構成側（0.043s）より大きく、
n=2〜3の間で構成側が逆転する。以降、査定側の割合は n=4の8.9%から単調に縮小し続け、
n=10〜14ではおよそ1〜2%で下げ止まっている。構成側の割合は n=14時点で98.9%に達する。

つまり **査定(`ann`/`saturate`)側のコストが `n` とともに構成側より速く増大していく、という
仮説は否定される**。査定側は絶対値としては増加している（n=4で0.075s→n=14で1.806s、
約24倍）ものの、構成側の増加（n=4で0.773s→n=14で165.15s、約214倍）の方がはるかに速く、
相対的な重みは一貫して構成側に吸収されていく。

### `algorithmic_mmp_bpf_fastpath_notes.md` §17への含意

「全H^0生成元の代わりに genuine section 4本だけを `ann`/`saturate` に使う」という改善案
（Las Vegas的判定）の効果の理論的上限は、この査定側の割合そのものである。n=4時点での
見積もり（最大10%程度の改善）は、n が大きい領域ではさらに小さく——n=10〜14では
**最大でも1〜2%程度の改善にしかならない**。このため、この改善案単独の優先度は低いという
先行の判断がこの計測によって定量的に裏付けられた。

ボトルネックの実質的な削減は、構成側（`weilDivisorToModule`、すなわちreflexive hull構成）
自体を回避する設計（`algorithmic_mmp_bpf_fastpath_notes.md` §7–16 の character/jet局所補正）
以外にはあり得ないことが、この計測によってより強く裏付けられた。

---

## n=15 のstall: 制御されたタイムアウトではなく、質的に異なる劣化の可能性

n=15の計測では、シェルレベルのタイムアウト機構（`timeout`/`gtimeout` が本環境に存在しない
ため、`perl -e 'alarm shift; exec @ARGV' <secs> M2 ...` で代用）が機能しなかった。M2が
`SIGALRM` を自身の内部処理（alarm/interrupt機構）のために横取りしているとみられ、
ラッパーのシグナルがプロセスを終了させなかった。結果、n=15のプロセスは約29分間
（wall-clock約1750秒）走り続け、手動で `kill -9` した。

`ps` で確認したCPU時間はこの間わずか約200秒程度であり、wall-clockの大部分（約1550秒）で
CPUをほとんど使っていなかったことになる。これは単純な計算量の増大（構成コストの
n依存の急増）とは性質が異なり、**メモリ圧迫やGCのスラッシングなど、別種の劣化が
高次の n で始まっている可能性**を示唆する。標準入出力のバッファリングのため、
n=15については途中経過も含め一切のタイミングデータが回収できなかった。

n=14（合計166.96秒）が、完全な内訳が得られた最後の点である。

---

## 結論・次のアクションへの含意

- 査定(`ann`/`saturate`)側の割合は n の増大とともに増加せず、むしろ縮小し続ける。§17の
  「4本のsection」改善案単独の効果上限は、高次では1〜2%程度に過ぎない。
- ボトルネックの実質はほぼ全面的に `weilDivisorToModule`（reflexive hull構成）にあり、
  これは n が増えるほど支配的になる（n=14で98.9%）。
- n=15付近から、単純な計算量増大とは異なる可能性のある劣化（低CPU利用率での長時間stall）
  が観測された。これはメモリ・GC関連の別問題である可能性があり、今後の実験（特に
  character/jet局所補正によるreflexive hull回避を試みる際）でも、CPU時間だけでなく
  メモリ使用量・wall-clockとCPU時間の乖離を併せて監視する価値がある。
- 総合的な結論として、`algorithmic_mmp_bpf_fastpath_notes.md` §7–16
  （canonical cover / character decomposition / $Q_a$ のテーブル化によって
  `weilDivisorToModule` 自体を回避する設計）への投資根拠が、この計測によってさらに
  強化された。次の試金石は、同ドキュメントのロードマップ Phase 2
  （$\frac1r(1,-1,c)$ 型cyclic quotient singularityでの $Q_a$ の直接比較・table化可能性の
  検証）である。

---

## ファイル

- 計測スクリプト（scratchpad、リポジトリ非変更）:
  `bpf-breakdown-single.m2`
- 各 n の生ログ（scratchpad）:
  `log_n1.txt` 〜 `log_n14.txt`（各段階の`cpuTime`を含む完全な結果）、
  `log_n15.txt`（stallの経緯を記録、タイミングデータなし）
- 関連する既存文書:
  - `STAGE2-MEASUREMENT-RESULTS.md`
  - `INVERTIBLE-IDEAL-CACHING-EXPERIMENT-REPORT.md`
  - `algorithmic_mmp_bpf_fastpath_notes.md`
