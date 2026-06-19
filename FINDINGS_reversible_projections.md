# 可逆二村射影 — 知見まとめ (spec_av)

2026-06-18 時点。AV ベースの可逆部分評価器 `spec_av.rwhile` で第1〜第3二村射影を達成した過程で
得られた知見の統合記録（論文用）。旧 `FUTAMURA.md` は spec.rwhile 配列版・2026-06-14 時点で古い。

---

## 1. 達成したこと（fp1/fp2/fp3 すべて green）

`spec_av` の契約：入力 `In = (Prog . (BT . Src))`、`Prog` を静的入力 `Src` で特殊化（`BT='S`=Src 静的）。
基本方程式：`[spec_av]((p . ('S . s))) = comp,  [comp](d) = [p]((s . d))`。

- **fp1**：`[spec_av]((ri_min . ('S.op)))` = 残余 `comp`、`[comp](d)=[ri_min]((op.d))`。
  検証：`[[spec_av]((ri_min.('S.'swap)))](('a.'b)) = ('swap.('b.'a))`。`B` := この残余(436B)。
- **fp2（コンパイラ）**：`comp2 = [spec_av]((spec_av . ('S.ri_min)))`、`[comp2](('S.op)) == B`。
- **fp3（cogen）**：`comp3 = [spec_av]((spec_av . ('S.spec_av)))`、`[comp3](('S.ri_min)) == comp2`、
  ゆえに `[[comp3]('S.ri_min)]('S.'swap) == B`。

回帰テスト：`second-projection` 群（`test_fp2_second_projection`/`test_fp3_cogen`、`Slow、~28s）。

## 2. 鍵となった機構

- **MKAV（束縛時刻認識の部分入力）**：L1051 の無条件 `'S` タグ（束縛時刻の静的コミット）が fp2 の真因
  だった。`MKAV(BT,Src,Ic)` で `BT='S→('C.(('S.Src).('D.('var.Ic))))`、`BT='D→('D.('var.Ic))`。
  自己適用下では BT が動的化し条件が残余化される（必要だが不十分だった）。
- **PAT-READ-ITER（深さ一般の読みパターン残余化）＝fp2 を通した決め手**。`PAT-READ-AV` は深さ1で、
  ネスト cons を `PAT-READ-LEAF-AV2` の葉 else (`('S.(tl P))`) で**静的リテラル化**していた（マクロは再帰
  不可なので反復ワークリストで深さ一般化、AV-LIFT の begin/end マーカ流儀）。`ASSEMBLE-FP1` がネスト出力
  パターンを持つため fp2 で露呈した。
- **ストアサイズ N＝fp3 の決め手**：comp3 は spec_av(223 変数)を特殊化するのに AV-INIT の N(=`FpN`)=50 固定
  → AUX が index~223 まで歩いて 50 スロット店を溢れ `cons U Vl<=Vl`(Vl=nil) で落ちる（症状 `cons 10 1 vs nil`）。
  **真因は残余化バグではなくストアサイズ不足**。`FpN 50→256`・swap-via-temp の `TmpT 100→250`(特殊化対象の
  変数 index より上)で解決。動的算定ツール `specsize`（下記）。

## 3. 検証基準の落とし穴（重要）

- **`run_via_ri`（ri.rwhile 経由実行）は残余の判定に使えない**。ri.rwhile 自身にバグがあるため。
  - **bug1（修正済）**：ri.rwhile の `'cond` が入口テスト値と出口表明値を**ビット一致**で比較していた
    （`Arg ^= V`）。R-WHILE は**真偽一致**のみ要求。involutive な `CANON` マクロで真偽正規化して修正。
  - **bug2（本質的）**：可逆自己クリア `X ^= X` は**非可逆**（v→nil、逆も nil→nil）。ri.rwhile は
    `X^=X` を逆解釈できない。spec_av の残余は自己クリアを含むため run_via_ri で落ちる。
- **正しい判定＝直接評価**：`data2program`（`Program2DataRwhile`）＋ツール `d2p` で残余を AST に復号して
  `EvalRwhile.evalProgram` する。`comp == B`（byte 一致）で射影成立を判定。

## 4. 可逆性の理論（spec_av を可逆にすると何が起きるか）

- **spec_av は非可逆**：`X ^= X`（self-clear, X∈e 違反）で中間情報を不可逆消去している。前方実行専用なら
  クリーンに `(prog,src) → residual` を出せるが、これは**非可逆だからこそ**可能。
- **非単射ゆえ入力は消せない**：`spec : (prog,src) → residual` は非単射（residual から prog/src を復元
  できない＝逆特殊化は不可能）。非単射関数の可逆実現は入力を区別する情報を必ず保持する（Landauer/Bennett）。
  ⇒ **可逆版は必ず入力（or 同等のゴミ）を抱える**。「可逆かつ入力を捨てた clean 出力」は原理的に不可能。
- **整合**：可逆自己解釈器 `ri.rwhile` は出力を `(P . result)` にしてプログラムを保持しているからこそ可逆。

## 5. dead-path ゴミ埋め込み（可逆版プロトタイプ `spec_av_rev.rwhile`）

アイデア（横山先生）：**捨てる情報を残余の「実行されない枝」に封入**し、出力をペアでなく単一プログラムに保つ。
- 実装：`CLEAR(X)` マクロ本体を `X^=X` → `GARB <= cons X GARB`（ゴミスタックへ push）に変更。main の
  `EMBED-GARB` が GARB を残余の **dead 定数真分岐 else**（`if (nil.nil) then body else 0^=GARB fi (nil.nil)`）
  に埋め込む。`CLEAR` をマクロ化してあったため 1 マクロ差し替え + embed で済んだ。
- 検証（`test_rev_spec_dead_garbage`, `reversible-spec` 群）：
  1. `[spec_av_rev]((ri_min.('S.'swap)))` が **store クリーンで実行**（不可逆消去なし＝可逆実行）；
  2. `[comp](('a.'b))=('swap.('b.'a))`（dead 枝無視、direct eval も ri.rwhile も）；
  3. **決定的：`[INV-spec_av_rev](comp) == 入力`**（自分の出力から入力を全復元＝真の全単射）。
- 位置づけ：Bennett のゴミを別出力にせず **dead code に再配置**したもの。情報量は減らない（非単射）。

## 6. ゴミ最小化

- 計測（fp1 ri_min）：comp = 1739 nodes（B=103）。dead ゴミ 1517 nodes のうち **1 値が 1055 nodes
  ＝末尾 `CLEAR(Vl)`（AV 店全体, N=256）**。
- **lever1（支配的）：N-sizing**＝`specsize spec_av_rev.rwhile <subject>` で `FpN` を被特殊化プログラムの
  変数数に。ri_min(FpN=13)で 1055 店が潰れ comp ~755 nodes。
- **lever2（easy 部分・実施）：静的 delocalization**＝CLEAR(X) を、X が**生存変数のコピー**のとき
  `X ^= <src>`（再計算で打ち消し）に。CBoth/CBothS/CVT/NewV に適用、round-trip 維持。小さい(-12)。
- **lever2 hard 部分（未・研究規模）**：boolean flag（`f ^= =? X c`）は**分岐内で operand 消費**のため
  打ち消せず（operand 保存/並べ替え要）。runtime skip-if-nil は**両枝 X=nil 収束で出口表明不能**＝不可逆。
  真の消去は AV 代数(AV-HD/TL/UNCONS/EQ)の uncompute 規律可逆書き換え＋Vl の store-reversal。
- **合算（deloc + N-sizing）：1739→755 nodes（-57%）、`[comp]` 正答維持**。

## 7. 成果物マップ

| ファイル | 役割 | タグ |
|---|---|---|
| `examples/spec_av.rwhile` | 正本（forward, fp1/2/3 green） | `spec_av-fp123-working` |
| `examples/spec_av_clean.rwhile` | 可読化（forward, spec_av と byte 等価, ゲート付き） | — |
| `examples/spec_av_rev.rwhile` | 可逆版（dead-path ゴミ埋め込み） | `spec_av_rev-prototype` |

- ツール：`src/d2p.ml`（`make d2p`：残余の復号/直接評価）、`src/specsize.ml`（`make specsize`：N を
  subject の変数数から動的算定）。
- テスト群：`second-projection`(fp2/fp3)、`reversible-spec`(可逆版 round-trip)、`refactor-gate`
  (spec_av_clean ≡ spec_av)。
- 関連 Agda（`proofs/agda/`）：`RWhileRevProj2BT`(束縛時刻の真因)、`RWhileRevProj2Self`(目標形)。

## 8. 未解決・今後

- ゴミ最小化の hard 集合（AV 代数の uncompute 規律可逆書換、Vl の store-reversal）。
- `N` の真の動的化（spec_av 内部で Prog の変数数から算定。現状は固定 or `specsize` で外部生成）。
- ri.rwhile bug2（自己クリア非可逆）の扱い＝spec_av_rev のように残余から self-clear を排すれば run_via_ri 可。
- 先行研究：古典 PE の cogen は Mix/Similix/C-mix で達成済（いずれも非可逆）。**可逆領域**の先行 PE
  （Mogensen Janus PE 2011、Glück–Normann 2024、可逆フローチャート PE 2024）は **fp1＋反転射影どまりで
  自己適用 fp2/fp3 は無い**＝本研究（自己適用可能な可逆 PE による fp2/fp3・可逆 cogen）が中核的新規性。
  詳細な位置づけ・出典・公表前の確認事項は **`RELATED_WORK.md`** を参照。
