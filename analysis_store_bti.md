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

### 実装試行1（2026-06-23, revert 済）＝設計は妥当・残課題は COLLECT-REFS の可逆性
選択的 dynamicize を `spec_av_bti` に実装して試行：`MEM-COUNT`＋自動逆で `MEMBER`、マーカ式ワークリスト
`COLLECT-REFS`（('var.K) 部分木を収集, 'val 直下は走査せず, 一般 cons は再帰）、`SELECTIVE-DYNAMICIZE`、
'cond/'loop の `DYNAMICIZE-ALL` を `COLLECT-REFS(C);COLLECT-REFS(D);SELECTIVE-DYNAMICIZE;INV-COLLECT-REFS(D);INV-COLLECT-REFS(C)` に差替。
- **fp1 ゲート PASS（103/63 不変）**＝パース・マクロ展開・静的経路は健全。forward の COLLECT-REFS/SELECTIVE は動作し
  comp2 生成は `INV-COLLECT-REFS` まで到達（＝設計の方向は妥当）。
- **赤＝可逆性バグ**：`Assertion pair? CrN is not false`（`INV-COLLECT-REFS` の逆実行で失敗）。原因は
  `COLLECT-REFS-STEP` の**フラグ自己クリア `Cr* ^= Cr*` が逆方向で壊れる**（`X^=X` 非可逆＝既知 bug2 と同型。
  逆 if のエントリ test に使うフラグ値が自己クリアで消える）。compute–uncompute（`INV-COLLECT-REFS` で CdRefs を
  クリア）に依存するため、`COLLECT-REFS` は厳密に可逆でなければならない。
- **次の一手（fix-the-fix）**：`COLLECT-REFS-STEP` を可逆に作り直す。候補：
  (a) フラグを自己クリアせず、**消費前の値で `fi`** または値を再構築してから assertion（`case` の output-discriminant 流儀）。
  (b) `Desugar` の `case` で書く（可逆性自動）——ただし命令木は任意 cons（'cons タグ無し）ゆえ PAT-READ-ITER の
      `case cons 'cons` 方式は直接使えず、汎用 cons への拡張が要る。
  (c) compute–uncompute を避け CdRefs を別経路で可逆に廃棄。
  各手 `measure_proj gate`（fp1 緑）＋`measure_proj comp2-loops ../examples/spec_av_bti.rwhile`（CLoop 125→激減かつ
  出力が d 依存で正しいか＝no-op プローブと違い定数化しないか）で確認。理論的目処は立ち、残るは可逆ワークリストのデバッグ（多ラウンド）。

### 実装試行3（2026-06-23, dedicated session）＝可逆 COLLECT-REFS 完成＋統合、残2課題を局所化
- **可逆 COLLECT-REFS 完成（commit 4d2c08f, ハーネス緑）**：文法指向で書き直し（worklist 項目を頭アトムタグ付き
  ノードに限定、無タグ arg-tuple は arm 内で固定形分解、PAT-READ-ITER 流の case＋begin/end マーカ）。`./ri` で
  式・命令ツリーとも forward→INV 往復 OK、forward は全 ('var.K) を正しく収集。試行1/2 の可逆性赤を解消。
- **spec_av_bti へ移植＋配線**：MEM-COUNT/MEMBER/COLLECT-REFS/SELECTIVE-DYNAMICIZE を追加、'cond/'loop の
  DYNAMICIZE-ALL を COLLECT-REFS(C);COLLECT-REFS(D);SELECTIVE-DYNAMICIZE;INV-COLLECT-REFS(D);INV-COLLECT-REFS(C)
  に差替。fp1 ゲート PASS（103/63 不変）。
- **comp2 で2つの後続課題を順に局所化**（各 fix で次が見える＝unroll が実際に進行している証拠）：
  1. **store サイズ不足**（`cons U Vl <= nil`）：新マクロ追加で spec_av_bti の変数数 219→**298**、FpN=256 を超過。
     `specsize ../examples/spec_av_bti.rwhile ../examples/spec_av_bti.rwhile 12` で FpN=310/TmpT=300 にリサイズ→解消。
  2. **'lcheck 動的 exit（`'error <= '41`）**：store 修正後、内側インタプリタが unroll を開始（selective 動作！）。
     だが内側のループが「静的 entry・動的 exit」になり 'lcheck が処理不能。**有力仮説＝over-approx**：COLLECT-REFS が
     **読み出しも収集**するため、MKAV 分岐の `cons 'var Ic`（Ic を読むだけ）で Ic スロットを動的化→それを index に
     使う AUX が動的 exit 化→'41。**修正＝書き込み位置のみ収集**（'ass target・'rep 書きパターンのみ、test/read 式は除外）
     ＝精密な assigned-set。context-aware（命令/書きパターン）worklist が要る。
- **状態**: spec_av_bti は gate 緑の WIP（comp2 は '41 で未達）。次＝COLLECT-REFS を writes-only 化しハーネスで検証→comp2。

### 実装試行4（2026-06-23, 続）＝writes-only 化、'41 の真因は「ループ束縛時刻」と判明（重要）
- **COLLECT-REFS を writes-only に精密化（ハーネス緑）**：書き込み位置のみ収集（'ass target・'rep 書きパターン）、
  read 子（'ass の E、'rep の P2、'cond/'loop の test 式）は begin マーカに退避して未走査・保存。**簡略化の発見**：
  書き込みだけなら式構成子（'hd/'tl/'eq/'pairp）は常に read で skip ゆえ scan 不要＝命令＋書きパターンのみ。
  往復 OK、命令木で 9→3 refs（精密）。spec_av_bti へ移植（変数数 298→282、FpN=310 で OK）、fp1 ゲート PASS。
- **comp2 は依然 '41**（'lcheck 動的 exit）。⇒ **over-approx は '41 の主因ではなかった**。
- **真因の確定**：`ri_min` はループ 0。よって '41 は**内側 spec_av 自身のループ**（AV-INIT/SPEC-CMD-AV/AUX 等）が
  unroll 時に「**静的 entry・動的 exit**」化したもの。spec_av の loop-unroll 機構（'lcheck）は静的 exit のみ対応で、
  動的 exit を `'error <= '41` にする。selective dynamicize で内側が unroll 開始した結果、ある内側ループの exit が
  部分的に動的なストアスロットを読み動的化＝**spec_av の unroller が entry だけ見て exit の束縛時刻を見ていない**。
- **⇒ comp2 非自明化は 2 段必要**：(1) **selective dynamicize**（DYNAMICIZE-ALL の過剰 materialize を解消＝**完了**、
  プログラムは静的に残る）＋(2) **ループ束縛時刻解析**（'loop ハンドラが entry∧exit を見て、どちらか動的なら
  residualize。現在 entry のみ）＝**未着手の深い課題**。(2) は 'loop/'lcheck の改造＋可逆性で、selective とは独立の大物。
- **到達点**: 可逆 COLLECT-REFS（最難所）＋selective dynamicize は完成・統合・fp1 緑。残＝loop-BTA。spec_av 本番は無改造。

### 実装試行5（2026-06-24/25, Agda 先行で loop-BTA 実装）＝comp2 が 0.005× に激減も**正しさバグ**
Agda 青写真（`RWhileLoopBTA`＝決定規則／`RWhileLoopBTARev`＝residual loop 可逆＋`constEntry-no-iter`＝entry 定数化禁止、
全51 --safe）に従い spec_av_bti の `'loop` を実装：entry に加え **exit `LpF` も特殊化**、`(LpTE=='S)∧(LpTF=='S)` で
判定、両方静的→unroll、片方でも動的→residualize（raw 源テスト＋body を emit、定数化しない）。measure_proj の
comp2-loops に**正しさチェック**（`[comp2]('S.op)==B`）＋サイズ表示を追加。
- **'41 解消・劇的 unroll**：comp2 **125→4 CLoop**、**812515→10691 nodes（0.994×→0.005×）**＝内側インタプリタが
  大量 unroll（selective＋loop-BTA が機能）。残る 4 loop は genuinely-dynamic（正しく residualize）。
- **だが `[comp2]('S.swap)==B : false`（id も false）＝comp2 が不正**。writes-only/reads+writes どちらでも false
  （under-materialize 仮説は外れ）。残余を見ると内側 spec_av の AV-LIFT ループ・ストア構築・AUX 歩行が runtime に
  残余化されており、何かを計算するが B を produce しない。
- **疑い**：selective が残す **partial-static ストア**（一部静的・一部動的）と、DYNAMICIZE-ALL が全動的を保証していた
  前提で書かれた内側 spec_av の後続処理との相互作用で残余が壊れる。または loop-BTA residualize の意味が微妙に違う。
- **次の切り分け**：fp1 規模で selective 'cond 単体の健全性を確認（`examples/fp_dyncond_bug.rwhile` を spec_av_bti で
  特殊化し `[comp](d)` が正答か）。'cond-selective が壊れていれば fundamental、健全なら loop-BTA 側。
- **状態**: spec_av_bti は fp1 ゲート緑だが **comp2 不正**の WIP。Agda 青写真は完成・正。spec_av 本番は無改造・repo 緑。
- **切り分け（`measure_proj dyncond`, fp1 規模・秒）**：`fp_dyncond_bug`（動的 cond の正当な可逆プログラム）を
  spec_av／spec_av_bti 両方で特殊化 → **両方正答**（comp=125, `[comp]('x)='one`, `[comp](nil)='two`）。
  ⇒ **selective dynamicize＋loop-BTA は単純な動的 cond では健全**。comp2 が不正なのは**自己適用特有**＝spec_av 自身の
  複雑な機構（AV ストア構築 AV-INIT／MKAV の動的 cond／入れ子ループ・AV-LIFT）を特殊化するときのみ顕在化。
  残余を見ると内側 spec_av の AV-LIFT/ストア/AUX が runtime 残余化されており、selective が残す partial-static ストアと
  これらの相互作用が疑わしい。**次**：comp2 規模で、selective が内側 spec_av のどの機構を壊すか特定（dump 差分／
  内側 AV-LIFT・AUX の入力 AV を追跡）。深いデバッグ（数分/回）。道具：`measure_proj dyncond`/`comp2-loops`(正しさ込み)。

### 実装試行2（2026-06-23, /loop-next B round 1）＝可逆性の真因を特定（重要）
高速ハーネス `examples/test_collect_refs.rwhile`（`./ri` で `COLLECT-REFS`→`INV-COLLECT-REFS` 往復を秒で検査。
comp2 数分が不要）を作成し、`COLLECT-REFS` の可逆性バグを**秒単位で局所化**：
- **真因＝`flag ^= flag` 自己クリア慣用句は FORWARD 専用**。`AV-HD`/`AV-UNCONS` もこれ（`CT ^= CT` 等）を使うが、
  それらは spec_av 内で**逆実行されない**から動く。`COLLECT-REFS` は `INV-COLLECT-REFS` で**逆実行する**ため、
  逆 if の**エントリ条件に使うフラグが nil クリアされ常に誤枝**を取り → `Assertion pair? CrN is not false`。
- ＝**逆実行されるマクロでは自己クリアフラグは使えない**（既知 bug2「X^=X 非可逆」の一般化）。可逆な条件分岐には、
  逆エントリ時に**再構成可能な判別**が要る：(i) `Desugar` の `case`（input/output discriminant。PAT-READ-ITER が
  これで可逆＝fp2/fp3 緑）、または (ii) `AUX` の `=? Cnt J` のような**永続状態テスト**。
- **`case` 版の障害**：命令木は `'seq.(C1.C2)` 等の**無タグ tuple-cons**を含み、end-marker の再結合が任意 head の
  cons を出力するため**出力 discriminant が非素**（`case` 健全性違反）。PAT-READ-ITER が成立するのは pattern が
  `'cons`/`'var`/`'val` で固定タグだから。
- **次ラウンドの設計候補**：(a) ワークリスト項目を**一律タグ付け**して `case` を適用可能に（無タグ cons を
  `('node . (H.T))` 等で包む）、(b) 可逆条件を**永続判別状態**で手書き（フラグを自己クリアせず、逆で再計算可能な
  値で `fi`）、(c) `COLLECT-REFS` を**逆実行しない**設計に（CdRefs を INV-COLLECT-REFS 以外で可逆に廃棄＝
  例えば SELECTIVE-DYNAMICIZE が消費しながら使う）。ハーネスで秒イテレーション可能。

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
