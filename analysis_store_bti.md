# 案1 Phase 2b：ストア index の束縛時刻改善（BTI）— 設計と診断

2026-06-20。目標：`comp2 = [spec_av]((spec_av.('S.ri_min)))` を `≪ |spec_av|` に縮め、
「本物の fp2（生成コンパイラが解釈オーバヘッドを除去）」を実機実証する。

## 1. 確定した診断（Phase 2b-1）

`measure_proj full` の breakdown（commit 5003ae1）より：

```
comp2:  CSeq=1533 CAss=758 CRep=1120 CCond=219 CLoop=125   (812,515 nodes, 0.994×|spec_av|)
Simp 後: 同一ヒストグラム, 597,961 nodes (0.731×)  ← 削減は全て式の定数畳み込み、dead分岐0除去
```

- **bulk は 125 個の CLoop**。これは spec_av のストアアクセス `AUX(Vl,J,…)`（`from (=? Cnt nil) loop … until (=? Cnt J)` で index J まで店を歩く）が **comp2 に残余化**されたもの。`LOOKUP`/`UPDATE` は `AUX; (read|write); INV-AUX`。
- post-hoc 簡約（Simp）はループ本体に触れない＝**天井 0.73×**。comp2≪|spec_av| には**ループ＝ストア機構そのものの束縛時刻改善**が必須。

### Simp 天井が「構造的」である裏取り（2026-06-21）
`Simp.simpCom` は実は **CLoop 本体に再帰している**（`Simp.ml:64` の `simpDo`/`simpLoop`）。
それでも `nodes inside CLoop bodies` が Simp 前後で **完全に不変**（1,157,729 → 1,157,729）なのは、
ループ本体がほぼ全て **`CRep`（パターン置換 `cons U Vl <= Vl; …`＝ストア歩行 AUX 本体）** で、
`simpCom` は `CRep` を素通し（`Simp.ml:57`）、かつ `Vl` が動的なので畳み込める**閉じた式が存在しない**ため。
⇒ **0.73× は Simp の調整不足ではなく構造的天井**。唯一のレバーは BTA（index 静的化）であることが確定。
（漏れ点も特定：`SPEC-EXP-AV-STEP` の `'var => LOOKUP(Vl, EArg, SX)`（`spec_av.rwhile:333`）。
EArg は内側 work-stack `Cd` 由来で、自己適用下では outer から動的化＝AUX 残余化。）

## 2. 真因（束縛時刻の漏れ）

`comp2` の契約：`[comp2](d) = [spec_av]((ri_min . d))`。すなわち comp2 は **ri_min を処理する内側 spec_av を、プログラム入力 = ri_min（静的）で特殊化した残余**。

- ri_min の変数 index（`cons 'var EArg` の EArg、呼び出し側 L333 `LOOKUP(Vl, EArg, SX)` ほか L360/373/387/399/416/453/472）は **ri_min の構文から取れる＝本来静的**。
- spec_av は**静的制御のループを展開できる**（L800「Static control unrolls via 'lcheck; dynamic control residualizes」）。よって EArg が静的 AV（'S）なら `AUX` の `=? Cnt J` は静的となり**展開され、comp2 から消える**はず。
- ところが comp2 には 125 個の動的 AUX が残る＝**EArg（ひいては内側のプログラムポインタ Cd）が outer から動的に見えている**。これが漏れ。

### 決定的な裏取り（実測、`measure_proj looptest`）
`[spec_av]((ri_seq . ('S . ('swap.('id.('swap.nil))))))`（命令列インタプリタを静的3命令リストに特殊化）の残余：
```
residual = 1281 nodes,  CSeq=14 CAss=9 CRep=6 CCond=0 CLoop=0
```
**CLoop=0・CCond=0**＝静的命令リスト上のループは**完全に展開**され、静的ディスパッチも解決済。
⇒ **spec_av のループ展開・静的分岐解決の機構は正しく動作している**。したがって comp2 の 125 CLoop は
「ループ機構の不備」ではなく**純粋に index J（＝内側プログラムポインタ Cd 由来）が動的**であることが原因と**確定**。
**修正は「index/プログラムポインタを静的に保つ」（§3 (A)/(B)）に一点集中でよい**（ループ特殊化は触らない）。

### 漏れの正確な局在（2026-06-23 診断, `measure_proj comp2-loops` + 残余ダンプ）
`measure_proj comp2-loops`（comp2 生成＋全 CLoop の入口/出口テスト式を集計＋残余を `/tmp/comp2_resid.rwhile` にダンプ）で**漏れ箇所を1点に特定**：
- **125 CLoop は全て AUX/INV-AUX のストア歩行**。出口テストは `=? Cnt J`（Cnt 共有, index J は**実行時変数**）で、index は約9個の相異なる動的変数（v114×18, v66×9, v212×7, v151×4 …）＝ri_min の変数数規模。
- **根本＝内側プログラム ri_min が「動的な残余定数」として吐かれている**：
  - 残余 `215 <= ('seq . …)` ＝ ri_min 本文が**残余変数 215 への代入**として出る（spec 時に静的消費されず動的扱い）。
  - `133 <= cons 215 nil; from =? 216 nil loop cons (cons 214 213) 133 <= 133 … until =? 133 nil` ＝
    **内側 spec_av のメインコマンドループが丸ごと残余化**（静的な ri_min を動的に歩く）。
  - 続いて**コマンドタグ分岐 `if =? 214 'ass/'rep/'cond/'loop/'seq` が全部残余化**（214＝コマンドタグが動的）→
    式ディスパッチ `if =? (hd 97) 'var`（97＝式ノード動的, `cons 113 114 <= 97` で EArg=114）→ 125 動的 AUX。
- ⇒ trivial 化の正体は「**ri_min は外側の静的 Src なのに、内側 spec_av がそれを静的値として保持できず、残余定数 215 として吐き、インタプリタ全体を残余化**」。
- **修正点は spec_av の入力分解／BT 伝播**（`spec_av.rwhile:922` `cons Prog FpBTS <= In` 以降, L1051 の `'S` 固定タグ）で**内側 Prog を静的 AV のまま保つ**こと。ループ・AV 代数・ストア機構は触らない。
- 道具：`measure_proj comp2-loops [specfile]`（dev ツール、加算的）。残余は `/tmp/comp2_resid.rwhile` にダンプされ offline 解析可。

### 犯人の確定＝`DYNAMICIZE-ALL`（2026-06-23 プローブで実証）
残余ダンプを追跡し、漏れの**正確な機序**を特定・実証した：
- **機序**：fp2（OUTER が INNER spec_av を特殊化）で、INNER の `MKAV(FpBT,…)`（`spec_av.rwhile:939`）は
  FpBT が動的なので内部 `if MkS`（L896）が OUTER の **'cond 動的テスト経路**（L782-797）に入る。その経路は
  **`DYNAMICIZE-ALL(Vl, RCode)`**（L288/L792, L827）を呼び、「分岐は任意変数を書きうる」として**OUTER ストア
  全体を materialize**（各静的スロットを `('var.k) <= lift(slot)` で吐き、全部 'D 化）。これで**静的だった
  内側プログラム FpBody が残余定数として吐かれ動的化**→内側インタプリタ全体が残余化→125 動的 AUX。
  残余の `215 <= ri_min定数` はまさに DYNAMICIZE-ALL が静的プログラムスロットを materialize した跡。
- **実証（プローブ, gate 保護下）**：`spec_av_bti` で DYNAMICIZE-ALL を **no-op** 化 →
  `measure_proj comp2-loops ../examples/spec_av_bti.rwhile` で **comp2 の CLoop = 125 → 0**（残余 1535→10 行、
  `215 <=` 消滅）。**fp1 ゲートは緑のまま**（fp1 は op 静的で DYNAMICIZE-ALL を呼ばない）。
  ⇒ DYNAMICIZE-ALL が trivial 化の唯一の原因と確定。
- **ただし naive 除去は unsound**：no-op 版の comp2 は出力が**定数**（MKAV 残余を破棄し動的入力 d に依存しない）。
  DYNAMICIZE-ALL は「動的分岐が実際に書くスロット」の materialize には必要。
- **正しい修正＝選択的 dynamicize（§3 (A) の具体形）**：'cond/'loop の動的テスト経路で、DYNAMICIZE-ALL の代わりに
  **分岐（C/D もしくは L/D）が実際に代入するスロットだけ**を materialize/動的化する。これには
  (1) コマンドの代入スロット集合を走査する macro（'ass の `cons 'var K`、'rep の書き側パターンの 'var を収集）、
  (2) その集合に限定した `SELECTIVE-DYNAMICIZE(Vl, Set, RCode)`、(3) 可逆性の保持、が要る。集合が過小だと unsound・
  過大だと最適化が弱まる（過大でも sound）。これで内側プログラム（FpBody）は静的に残り、インタプリタが展開され、
  かつ残余は d に依存＝**本物の最適化 fp2**。

### なぜ漏れるか（既知の本質）
HANDOFF_fp2.md / FINDINGS §2 の通り、spec_av は **online で「静的値」を運ぶ AV 設計**。自己適用下では内側のプログラムポインタ Cd が outer から見て動的化し、そこから読む EArg も 'D 化 → AUX が残余化。`MKAV`（束縛時刻認識の部分入力）は必要だが不十分で、根本は **online 値運搬 AV と offline 二段階 BT 分離の不整合**（FINDINGS §2 末尾）。

## 3. 修正の方向（候補）

いずれも「静的に既知の index アクセスを静的（展開済み）に落とす」のが目的。

- **(A) 環境の partially-static 化（本命）**：ストア `Vl` を *静的骨格*（index↔スロットの対応は静的に確定）と *動的内容*（各スロットの 'D 部分）に分割。`LOOKUP/UPDATE` を二相化：
  - index が静的 AV → **静的選択**（`AUX` の歩行を特殊化時にアンロール、ループ消滅）。
  - index が動的 → 現状の残余ループ。
  - 可逆性：静的選択も `SWAP-VIA-TEMP` 系の可逆代入で（既存の naive-swap 衝突対処と同系統）。
- **(B) プログラムポインタの静的維持**：内側 Cd を outer から静的に保つよう BT を通す（MKAV の延長）。漏れ箇所を `EArg` の AV タグで追跡して特定 → 'S を維持。(A) の前提でもある。
- **(C) index 表現の変更**：unary nat を、静的アクセスが O(1) 静的射影になる形（タグ付き直接スロット）へ。大改造。

## 4. 検証プロトコル（必須・各段で緑維持）

開発は**コピー `examples/spec_av_bti.rwhile`**（作成済み・初期は exact copy）で行い、動作中の
`spec_av.rwhile` は触らない。各変更後：

1. **fp1 ゲート**（高速・自動）：`./measure_proj gate ../examples/spec_av_bti.rwhile`。
   op∈{swap,id}・複数入力 d で **意味**（`[B_op](d) == [ri_min]((op.d))`）と**可逆性**
   （`[inv B_op]([B_op](d)) == d`）を検査し、**`GATE PASS` / rc=0** を要求（壊れたら `GATE FAIL` / rc=1、
   malformed 残余も例外捕捉して FAIL）。fp1 サイズ swap=103/id=63 はドリフト情報として表示（最適化で
   変わりうるのでハード判定はしない）。崩れたら即 revert。
2. **comp2 計測**：`./measure_proj full` で comp2/|spec_av| と breakdown（CLoop 数）が**減る**ことを確認。目標 CLoop≪125、ratio<0.5×。
3. **fp2/fp3 緑**：`second-projection` 群（d2p 直接評価で残余 byte 一致）。
4. **可逆性**：可逆版があれば `INV` round-trip。
5. 最終的に `spec_av_bti` が安定したら、`spec_av` へ昇格＋`spec_av_clean` 等価ゲート更新。

## 5. リスクと刻み

- **最難所**。過去の fp2/fp3 の詰まり（'10 過剰静的退化、var=Elem 可逆性違反、cons-vs-nil 束縛時刻、PAT-WRITE-ITER 退行）は**全て index/store 由来**。blind 編集は fp1/2/3 を高確率で壊す。
- **刻み**：まず (B) で漏れ箇所を 1 つ特定（EArg の AV タグを観測する最小実験）→ (A) を ri_min 規模の固定小ストアで実証→一般化。各刻みで fp1 ゲート。
- 詰まったら「どこまで静的化できたか」の境界を明示して止める（HANDOFF 方式の引継ぎ）。

## 6. 関連
- 診断ツール：`src/measure_proj.ml`（`make measure_proj`, breakdown 付き）、`src/Simp.ml`（簡約, 健全性 `proofs/agda/RWhileSimpSound.agda`）。
- 既存知見：FINDINGS §2（MKAV/PAT-READ-ITER/store N）・§9（Phase 1/2a/2b-1）、HANDOFF_fp2.md、`RWhileRevProj2BT.agda`（束縛時刻の真因の形式化）。
