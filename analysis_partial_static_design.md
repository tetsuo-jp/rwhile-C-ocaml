# Partially-static values for spec.rwhile — design (Stage 1 toward fp1/fp2)

作成日: 2026-06-14
目的: spec.rwhile の束縛時（binding-time）表現を拡張し、**部分的に静的な構造値**を扱えるようにする。
これにより第1射影 `[spec]((rint . src))` が解釈系をきちんと特殊化でき（残余が縮約され）、
ひいては第2射影に進める。

## 1. なぜ必要か（根本原因）

現行 SPEC-EXP（`spec.rwhile` 49–216 行）の注釈付き結果は `(A . V)`：
- `A = (nil.nil)`（非nil・真） → **静的**、`V` = 静的値
- `A = nil`（偽） → **動的**、`V` = 残余式コード

`cons` の合成（`consE`, 100–117 行）では：
- 両方静的 → 静的 `((nil.nil) . (V1.V2))`
- **混在・両方動的 → 完全に動的**（静的側は `(cons 'val Vi)` でリテラル埋め込みして捨てる）

つまり **`cons(静的, 動的)` が完全動的化**し、car が静的だったという情報が失われる。
その後 `hd` してももう静的に取り出せず、ディスパッチ（`=? Tag 'ass` 等）が動的化 →
解釈系全体が残余化（ri_fp3 で残余 714KB, cond 343 個）。

部分的静的値があれば `cons(静的, 動的)` を「car 静的・cdr 動的」と覚え、`hd` が静的、`tl` が動的を返せる。
fp1 の入力 `V0 = (prog . data)`（prog 静的・data 動的）を最初の `cons Prog Data <= V0` で
分解した瞬間に Prog が**完全静的**になり、デコード/ディスパッチが静的解決される。
→ peel ハックも ri_fp3 の prelude ハックも不要になる（本筋）。

## 2. 新しい注釈付き値（AV: annotated value）— 再帰的・自己タグ付け

現行の `(A . V)` 2値エンコードを、再帰的に自己記述する単一木 AV に置き換える：

```
AV ::= ('S . v)            -- 完全静的。v は素の値（さらに AV を含まない）
     | ('D . code)         -- 動的。code は残余式コード（'var/'val/'cons/'hd/'tl/'eq ...）
     | ('C . (av1 . av2))  -- cons。av1, av2 は AV（部分的静的を表現）
```

タグに atom `'S` / `'D` / `'C` を使い、現行の nil/(nil.nil) の 2 値判定と衝突しないようにする
（現行 `if A then` 方式は廃止し、`=? Tag 'S` 等の 3 分岐に統一）。

### 正規化規則
- `cons(av1, av2)`:
  - 両方 `'S` → `('S . (v1.v2))`（完全静的に畳む）
  - それ以外 → `('C . (av1 . av2))`
- `hd(av)`:
  - `('S . (h.t))` → `('S . h)`／`('S . leaf)` は静的エラー（実行時 hd エラーに対応）
  - `('C . (a1.a2))` → `a1`
  - `('D . code)` → `('D . ('hd . code))`
- `tl(av)`: 対称（`'C` → a2、`'S.(h.t)` → `('S.t)`、`'D` → `('D.('tl.code))`）
- `eq(av1, av2)`:
  - 両方が完全静的（`av_to_static` が成功＝'D を含まない）→ 比較して `('S . bool)`
  - それ以外 → `('D . ('eq . (lift av1 . lift av2)))`
- `var k`: ストア slot（AV）をそのまま読む
- `val v`: `('S . v)`

### LIFT（AV → 残余式コード）
動的文脈で AV をコードへ落とす関数 `lift`:
- `('S . v)` → `('val . v)`
- `('D . code)` → `code`
- `('C . (a1.a2))` → `('cons . (lift a1 . lift a2))`

## 3. 変更が必要な箇所（spec.rwhile）

| 箇所 | 変更 |
|---|---|
| ストア Vl の slot | `(nil.nil)`/`((nil.nil).v)` → AV（初期 dynamic = `('D . ('var.k))`? 要検討。むしろ slot は「その変数の現在 AV」） |
| `SPEC-EXP-STEP` 49–216 | `var`/`val`/`cons`/`hd`/`tl`/`eq` を §2 の AV 規則に全面書換 |
| `SPEC-STEP` の `'ass` 393–437 | `if AnnK/AnnE then` の 2 分岐 → AV による更新。静的×静的 update、動的なら residual + slot を `'D` 化 |
| `'rep` 442–460 + `CHECK-PAT-STATIC`/`PAT-READ`/`PAT-WRITE` | パターンを AV 上で読み書き。部分静的 slot からの cons パターン分解が肝 |
| `'cond`/`'loop` のテスト 477–… | テスト AV が完全静的なら分岐確定、そうでなければ residual |
| `LIFT`（既存） | §2 の `lift` に統一 |
| Vl 初期化（698 行）/ クリーンアップ（815 行 `Vl ^= Vl`） | 初期値 = 全 slot 動的 AV。クリーンアップは self-XOR のままで可 |
| 入力設定（normal/partial） | peel を撤去し、read 変数 slot に AV を直接設定。fp1 は `V0 = ('C . (('S . prog) . ('D . ('var . 0))))` 相当を与える（prog 静的・data 動的） |

## 4. 後方互換と移行戦略

現行の 2 値エンコードと新 AV は非互換のため、**spec.rwhile の SPEC-EXP/SPEC-STEP/PAT を一括で AV に移行**する必要がある。段階的テスト：

1. AV ユーティリティ（cons/hd/tl/eq/lift/正規化）を macro 化し、`spec-macros` 流の単体テストで検証。
2. `SPEC-EXP` を AV ベースに置換 → SPEC-EXP の単体テスト（静的/動的/部分静的）で検証。
3. `SPEC-STEP` の ass/rep/cond/loop を AV 対応に置換 → spec-partial（swap）が通ることを確認。
4. 入力設定を AV 直接指定に変更（peel 撤去）→ fp1(id/swap) を green に。
5. fp1(reverse)・ri_fp3 で残余が縮約されることを確認。
6. ri.rwhile（配列ストア）でも改善するか確認（動的インデックスは別問題として残る可能性）。

## 5. リスクと注意

- spec.rwhile は**可逆プログラム**。AV の各操作を可逆に書く必要があり、特に「正規化（両静的なら畳む）」
  の分岐は可逆性を壊しやすい。各 if は対応する exit assertion / クリーンアップが要る。
- 既存で通っている `spec-partial`（swap）を壊さないこと。各段階でテスト。
- これは複数セッション規模。1 ステップずつコミット可能な単位で進める。

## 6. 進捗

### ステップ1 完了（2026-06-14）: AV 代数の実装と検証 ✅
`examples/av.rwhile` に非再帰 AV 演算 `AV-CONS`/`AV-HD`/`AV-TL` を可逆 R-WHILE で実装し、
単体テスト（TestSuite の `av-algebra` 群6件）で検証済み。可逆性（store invariant）も維持。
実証された核心：
- `cons ('S.'a) ('D.x)` → `('C.(('S.'a).('D.x)))`（**静的 car を保持**。現行 spec はここで
  完全 dynamic 化していた）
- その `hd` → `('S.'a)`（静的部を復元）、`tl` → `('D.x)`（動的部）
これにより「静的×動的の cons → 後で静的部を取り出せる」ことが可能になり、過剰残余化を解く
土台ができた。

### ステップ1.5 完了（2026-06-14）: 再帰的 AV-LIFT も実装・検証 ✅
`examples/av.rwhile` に `AV-LIFT`（AV→残余コード）をスタックマシン（spec.rwhile の SPEC-EXP と
同型の work/done/marker 方式）で実装。再帰的 'C・ネストも正しく lower（`av-algebra` 群10件 green）。
これで SPEC-EXP に必要な AV 演算（cons/hd/tl/lift）が揃った。eq は lift＋全静的判定で構成予定。

注: 可逆 if の exit assertion は then 節で書き換えた**後**のタグを検査する慣習
（`if =? Tag 'C then (Tag→'CB) ... fi =? Tag 'CB`）。これを外すと assertion 失敗になる（実装時の落とし穴）。

### ステップ1.6 完了（2026-06-14）: AV-EQ も実装 → AV 代数完備 ✅
`AV-EQ` を実装（不変条件「完全静的 ⟺ タグ'S」により両 'S なら比較、それ以外は AV-LIFT で
両辺を lower して動的 eq）。`av-algebra` 群 **13件 green**（cons/hd/tl/lift/eq）。
マクロ・ハイジーンの教訓: R-WHILE のマクロ展開は内部局所変数を改名しないため、入れ子マクロ呼び出し
（AV-EQ→AV-LIFT）で局所名が衝突する。AV-LIFT-STEP の内部局所を一意名(LfX/LfY/LfP/LfQ)に改名して解消。
また AV-LIFT は入力を**保存**する（SPEC-EXP 流の `cons A nil <= A'`）ので呼び出し側でクリアが必要。

### ステップ2 完了（2026-06-14）: AV 版 SPEC-EXP 実装・検証 ✅
`examples/spec_av.rwhile`（spec.rwhile の並行版）に、ストア演算＋AV代数＋**SPEC-EXP-AV** を実装。
SPEC-EXP-AV は SPEC-EXP と同型のスタックマシンで、各結合を AV 演算（AV-CONS/HD/TL/EQ）に委譲する。
ストア slot は AV（動的 slot = `('D.('var.k))`）。`spec-av-exp` 群7件 green。実証された特殊化：

| 式 | 旧 SPEC-EXP | AV 版 SPEC-EXP-AV |
|---|---|---|
| `cons var0(静) var1(動)` | 完全 dynamic 化 | **`('C.(('S.'a).('D...)))` 部分静的** |
| `hd(cons var0 var1)` | 動的（hd コード） | **`('S.'a)` 静的復元** |
| `eq var0 ('val 'a)` | 動的 eq | **`('S.(nil.nil))` 静的真** |

最後の例が重要：`=? Tag 'ass` 系のディスパッチが静的に解決されることを意味し、ri_fp3 の過剰残余化が
解ける見込み。

### ステップ3 着手（2026-06-14）: AV 版 SPEC-STEP の 'seq / 'ass 完成 ✅
`spec_av.rwhile` に `SPEC-STEP-AV`（+ ループ駆動 `SPEC-CMD-AV`）を実装。'seq は構造、'ass は
spec.rwhile の束縛時ロジックを AV へ移植：静的式×静的変数→静的 rupdate（残余なし）、動的/部分静的式
→ `X ^= lift(RE)` を残余化し変数を動的化。`spec-av-step` 群4件 green（静的実行／残余化／動的式での変数
動的化／seq）。
ハイジーン教訓（再）: `AV-LIFT-STEP` の内部 `Tag/Pay/PayC` が SPEC-STEP-AV のコマンドタグ `Tag` と
衝突 → `LfTag/LfPay/LfPayC` に改名。また `parse_macro_harness` は厳密マーカー
`(* ===== Main program ===== *)` を要求。

### ステップ3 続き（2026-06-14）: 'rep 完成 → swap がエンドツーエンドで特殊化 ✅
spec.rwhile のパターン補助（CHECK-PAT-STATIC / PAT-READ-SIMPLE / PAT-WRITE-SIMPLE /
PAT-CLR-SIMPLE と各 LEAF 版）を AV へ移植（静的タグ判定 `=? (hd slot) 'S`、動的スロット
`('D.('var.k))`）。'rep を SPEC-STEP-AV に追加（全静的→PE時実行、さもなくば残余化＋全変数動的化）。
`spec-av-step` 群7件 green。**full swap がエンドツーエンドで特殊化**：
- 静的入力 `('a.'b)` → ストア X=`('S.('b.'a))`、RCode=nil（完全実行）
- 動的入力 → 両 rep を残余化（残余＝swap 本体）
＝ spec-partial 相当を AV 版で達成。

注（既知の限界、spec.rwhile と同じ）: 'rep/'ass の残余化経路は静的変数が動的化されるとき値の
materialize をしない（部分静的 rep の最適化は未）。faithful port のため許容。

### ステップ3 続き（2026-06-14）: 'cond 完成 ✅
SPEC-CMD-AV をシェル破棄方式に簡素化（出力 `(Vl . RCode)`。Cmd 再構成＝injectivity 用の符号埋め込みは
Stage C の課題として後回し。これにより condCleanS の難しいシェル再構成機構が不要に）。
'cond を追加：静的テスト（RE='S）→選択枝を work stack に積んで処理・他枝破棄＝**残余から cond が消える**、
動的テスト→test を AV-LIFT して whole-cond を残余化。`spec-av-step` 群10件 green（cond static-true/false/dynamic 含む）。
これが fp1 のディスパッチ解決（`=? Tag 'ass` 系の静的 cond が枝に解決）の核心。

### ステップ3 完了（2026-06-14）: 'loop 完成 → **Stage B 完了** ✅
'loop を継続（'lcheck）による静的展開で実装：静的 entry（true）→ D を積み 'lcheck で exit 判定、
exit 静的 false → L,D を積み再度 'lcheck（後退辺）、exit 静的 true → 終了。これを SPEC-CMD-AV の
ループ駆動が回して**静的にアンロール**。動的 entry → entry test を lift して whole-loop 残余化。
`spec-av-step` 群12件 green（loop static-unroll / dynamic 含む）。検証した静的カウントループは
I:nil→(nil.nil) に展開され残余なし。

**Stage B（spec コアの partially-static 化）完了**：AV版 SPEC-EXP ＋ SPEC-STEP（seq/ass/rep/cond/loop）が
全て動作。AV 特殊化器がコア R-WHILE で機能的に完備。

## Stage C（第1射影 fp1）

### 診断：partially-static 'rep が必要
fp1 の鍵は ri_fp3 の入力分割 `cons Prog Data <= V0`（V0 = `('C.(('S.prog).('D.dataref)))`）を
**残余化せず構造分割**すること。現行 'rep は「全 RHS 変数が静的」でないと残余化するため、'C（部分静的）の
読みを残余化してしまい prog の静的性を失う。→ partially-static な pattern 読み書きが要る。

### ステップ C1 着手（2026-06-14）: AV-UNCONS 実装・検証 ✅
`AV-UNCONS(A, A1, A2)`：cons 形 AV を2成分に分割（'C → av1,av2／'S-cons → ('S.h),('S.t)／
'D → 記号 hd/tl）。これが入力分割（`cons Prog Data <= V0`, V0='C → Prog=('S.prog), Data=('D...)）の
要。`av-algebra` 群に3件追加 green。spec_av.rwhile にもミラー済み（'rep 改修で使用予定）。

### ステップ C2 完了（2026-06-14）: 'rep の AV 化（symbolic）✅
'rep を AV-aware パターン読み書き（PAT-READ-AV / PAT-WRITE-AV、cons は AV-CONS/AV-UNCONS で
分割合成）で書き換え。**常に AV 領域で実行（残余化しない）**＝部分静的構造は分割、純動的値は
記号的に流れ（出力 lift 時に残余化）。spec-av-step 群13件 green（**入力分割テスト追加**）：
- 入力分割 `cons V1 V2 <= V0`（V0=`('C.(('S.'a).('D...)))`）→ V1=`('S.'a)`静的, V2 動的, 残余なし ✅
- swap 静的 → `('S.('b.'a))`; swap 動的 → X=`('C.(('D.tl X).('D.hd X)))`（記号 swap、残余なし）
注: 旧 concrete-value 版補助（CHECK-PAT-STATIC-AV 等）は未使用化（参照用に残置）。

### （旧）設計：'rep の AV 化
'rep `Q <= R`：
- R を AV-aware に読む（PAT-READ-AV：var→slot AV を消費、val→('S.v)、cons→AV-CONS）。得た AVr。
- Q が cons で AVr が cons 形（'C / 'S-cons）→ AV-UNCONS で分割して各 var slot に書く（**構造分割・残余なし**）。
- Q が cons で AVr が 'D 葉（純動的）→ 構造分割不能 → 従来どおり残余化（PAT-CLR で var 動的化）。
- Q が var → slot := AVr（代入）。
これで入力分割は構造分割、純動的データ移動は残余化、という structural PE になる（symbolic 全展開は採らない＝
論文 §6 のゴミ解析と整合）。

### ステップ C3 試行（2026-06-14）: fp1(id) 実機検証で設計問題が判明
spec_av に fp1 用 main（V0 slot を `('C.(('S.src).('D.('var.I'))))` に設定 → SPEC-CMD-AV →
出力 AV を AV-LIFT して残余 rep を組み立て）を注入し `[spec_av]((ri_fp3 . id))` を実行。
判明：

1. **seq 簡素化が必要だった**（修正済み）：shell を破棄する設計なのに seq が `seqB/seqE` で Cd' を
   pop しており、seq に cond/loop がネストすると `('cond.nil)` 等と衝突（`'cond` と `'seqB` の不一致
   エラー）。seq を「C,D を work stack に積むだけ」に簡素化して解消。spec-av-step 全 green 維持。

2. **symbolic 'rep の残余が分裂する（本質問題）**：fp1(id) 実行で store-not-cleared、非nil は **RCode**。
   つまり SPEC-CMD-AV は動的 'ass を RCode に残余化する一方、symbolic 'rep は効果を出力 AV に
   貯める。→ 残余が「RCode（残余化された ass）＋出力 AV（rep の効果）」に**分裂**し、きれいな
   1本の可逆残余プログラムにならない。combine するには順序・整合性の調整＋MAKE-SEQ が要り、複雑。

**結論（設計修正）**：fp1 のきれいな残余には **structural 'rep**（動的 rep も RCode に残余化）が本筋。
partially-static は (a) 入力分割（構造的に既知の cons を分割）と (b) 静的ディスパッチ解決（cond/eq、
SPEC-EXP-AV で既に動作）に使い、純動的データ移動は rep ごと残余化する（symbolic 全展開はしない）。
これは論文 §6 のゴミ解析（コマンド構造を保持）とも整合。symbolic 'rep（C2）は撤回し structural+
入力分割特例に作り直す。

### ステップ C3 追検証（2026-06-14）: symbolic+combine も不正と確定
symbolic を活かせるか、`MAKE-SEQ` を追加し残余を「MAKE-SEQ(RCode)＋出力 rep」に結合して
`comp=[spec_av]((ri_fp3.id))` を生成 → `[ri]((comp.'a))` を実行したところ **error in update**
（comp が不正：ri の DynVal にプログラム断片が乗る）。**symbolic 方式は fp1 のきれいな残余を
生成しないと実機で確定**（2度目の確認）。MAKE-SEQ 自体は有用なので残置。

確定した本筋（structural）：
- 'rep は **static→PE実行 / 動的→残余化** の構造的方式に戻す（commit 8553800 の版）。
- 入力分割 `cons Prog Data <= V0`（V0='C＝静的prog＋動的data）は **main で peel 特例**：
  Prog を静的設定、Data 半を残余 rep `Data <= ReadVar` で移動（spec.rwhile の peel を AV へ移植）。
- 静的ディスパッチ解決（cond/eq）は SPEC-EXP-AV で既に動作。
これで残余は RCode 1本（コマンド構造保持＝論文§6整合）になり、出力 AV 分裂を回避。

### ステップ C3（改訂）: structural 'rep ＋ 入力 peel ＋ spec_av main ＋ fp1
spec_av に main（入力 `(ri_fp3 . src)` → V0 slot = `('C.(('S.src).('D.('var.0))))` を設定 → SPEC-CMD-AV →
残余プログラム組み立て）を整え、`comp = [spec_av]((ri_fp3 . src))` を実行。`check_first_projection` を
ri_fp3＋spec_av に向け green に。injectivity 用の符号埋め込みは機能的正しさ確認後。まず `av.rwhile` の AV 演算を
spec.rwhile に取り込み、SPEC-EXP の var/val/cons/hd/tl/eq を AV 規則へ。LIFT と eq の全静的判定は
再帰が要るためスタックマシン化（既存 SPEC-EXP の B/E マーカー方式を踏襲）。spec-partial(swap) を
壊さないこと。
