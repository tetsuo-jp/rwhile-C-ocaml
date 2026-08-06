# 計画：第1可逆射影 fp1 を green にする（Stage C, ri_fp3 経由）

作成日: 2026-06-15
対象タスク: 「[DEFERRED] fp1 green on ri_fp3 (needs spec-core work)」
基盤: `plan_reversible_projections_impl.md`（Stage A–F の親計画）, `analysis_partial_static_design.md`（AV 設計と Stage A–C の実機診断）。

## 0. 現状（着手前の地固め）

- **Stage A 完了**: `-stats`（`count_nodes`、`[RWHILE-STATS]`）実装済み。
- **Stage B 完了**: `examples/spec_av.rwhile` に partially-static（AV）コアが完備。
  AV代数（cons/hd/tl/lift/eq/uncons）＋ `SPEC-EXP-AV` ＋ `SPEC-STEP-AV`（seq/ass/rep/cond/loop）。
  `spec-av-exp`(7) / `spec-av-step`(13) / `av-algebra`(16) すべて green。静的ディスパッチ解決
  （`=? Tag 'ass` 等の cond/eq が静的に枝へ）は **SPEC-EXP-AV で既に動作**。
- **Stage C 未達（要設計）**: fp1 のきれいな可逆残余生成が未完。
  - 現 `spec_av.rwhile` の `'rep` は **symbolic**（部分静的は分割、純動的は記号的に流して出力時 lift）。
  - 実機検証 3 回で symbolic 方式は **不正**と確定（残余が「RCode＋出力AV」に分裂／combine しても
    ri の DynVal にプログラム断片が乗る／all-symbolic では runnable だが結果が `(id.'a)` にならない）。
  - `src/TestSuite.ml:755` の `check_first_projection` は今も **ri.rwhile** を参照（ri_fp3 未切替）。

## 1. ゴール（＝完了の定義）

```
[[spec_av]((ri_fp3 . src))](in) = (src . [src](in))   for src ∈ {id, swap, reverse}
```
- `./test-suite test first-projection` が green（対象を ri_fp3 ＋ spec_av に切替後）。
- 残余サイズ ≪ `ri_fp3` の p2d サイズ（`-stats` で特殊化が効いている証拠を記録）。
- 既存 green（`spec-av-*` / `spec-partial` / `rint` / `av-algebra`）を全段で維持。

## 2. 方針（3 つの dead-end を回避する）

partially-static AV は **(a) 入力分割**（構造的に既知の cons を分割）と **(b) 静的ディスパッチ解決**
（cond/eq、既に動作）に使う。**純動的なデータ移動は rep ごと単一 RCode に残余化**する（structural）。
こうすると残余は**1本の可逆プログラム（RCode）**になり、出力AV分裂を回避。コマンド構造が保たれ
論文 §6 のゴミ解析とも整合する。

> 回避する dead-end（`analysis_partial_static_design.md` Stage C 参照）：
> ① symbolic 'rep（純動的を出力AVへ）→ 残余分裂。② symbolic＋MAKE-SEQ combine → comp 不正。
> ③ all-symbolic → runnable だが結果不正。**いずれも再実装しない。**

## 3. 手順（各ステップに「完了の定義＝テスト」）

### C0. ハーネスと計測足場（低リスク・先行可・~0.5 セッション）
- `spec_av.rwhile` に fp1 駆動の main を用意（`(* ===== Main program ===== *)` マーカー方式で
  `parse_macro_harness` か新ヘルパから `[spec_av]((ri_fp3 . src))` を回せるように）。
- `src/TestSuite.ml` に残余サイズ表明ヘルパ（`-stats`/`count_nodes` 利用）。
- **完了**: `comp_src = [spec_av]((ri_fp3 . id))` がエンド・ツー・エンドで走り（結果は未だ不正でよい）、
  サイズが測れる。

### C1. structural 'rep（コア修正・最重要）— ✅ 完了（2026-06-15）
実装: `PAT-WRITE-STRUCT(P, WA, RCode)` を追加（`PAT-WRITE-AV` 退役）、`'rep` を差し替え。
唯一の残余化ケース＝「cons-LHS に純'D値を分配」のみ `cons q1 q2 <= <code>` を RCode へ。
var↔var/部分静的 cons は残余なし（AV-UNCONS で構造分割）。残余は**ソース変数添字を再利用**（'D
マーカーが運ぶ＝'ass と同名前空間、アロケータ不要）。macro 非再帰のため cons-LHS は1段
（`PAT-WRITE-SIMPLE-AV` 同様、ri_fp3 のパターンは1段で十分）。
検証: `spec-av-step` 13件 green（test7 を symbolic→structural に更新：動的 swap が **rep_yzx 1本**に
残余化）、`av-algebra`/`spec-av-exp`/`spec-macros`/`spec-partial` 全 green、hygiene ON も green。

(旧記述:)
`SPEC-STEP-AV` の `'rep`（現 symbolic）を structural に置換：
- **完全静的 RHS** → PE 時に実行（slot 更新）、残余なし。
- **cons-LHS かつ cons 形 RHS AV（'C / 'S-cons）** → `AV-UNCONS` で分割し各成分を LHS 変数 slot へ
  （静的は静的のまま、動的は流れる）。**分割自体は残余を出さない**＝**入力分割**ケース。
- **純 'D 葉の RHS（または分割不能な cons-LHS）** → `Q <= lift(RHS)` を **RCode に残余化**し、
  LHS 変数 slot を動的 `('D.('var.k))` に。
- `'ass` も動的を**同じ RCode**へ残余化（現状の residualizing 'ass を踏襲）。
- 旧 structural 補助（`CHECK-PAT-STATIC-AV` / `PAT-READ-SIMPLE-AV` / `PAT-WRITE-SIMPLE-AV` /
  `PAT-CLR-*-AV`、現「未使用化・残置」）を再活用。symbolic 版 `PAT-READ-AV`/`PAT-WRITE-AV` は退役。
- **可逆性注意**: 正規化（両静的なら畳む）・分割の各 `if` に対応する exit assertion／クリーンアップ。
  「then 節で書換えた**後**のタグを exit で検査」する慣習（`if =? Tag 'C ... fi =? Tag 'CB`）を守る。
- **完了**: `spec-av-step` を structural 仕様で green に更新（動的 swap は **RCode 1本**に残余化、
  入力分割テスト V0='C は分割・残余なしを維持）。期待値の更新を伴う。

### C2. 残余アセンブリ（真の難所＝前回未完）— 概念検証済み（2026-06-15）
**アセンブリ・レシピ（確定）**：`SPEC-CMD-AV` 出力 `(Vl . RCode)` から
`comp_src = (('var.I') . (Body . ('var.J')))`：
- `Body` = `reverse(RCode)` を 'seq で畳む（残余コマンド列）＋ **末尾に出力変数の materialize**
  `J' <= patternify(Vl[J'])`（出力 slot AV を `AV-LIFT` で 'var/'val/'cons コードに → rep の RHS パターン）。
- read 変数 = I'、write 変数 = J'（ri_fp3 では I'=J'=0=V0、出力 V0=(src.result)）。

**実機検証（C1+C2 を手組みで）**：動的 swap の C1 残余 `RCode=[cons V1 V2 <= V0]` ＋ 出力 V0 の AV
`('C.((D V2).(D V1)))` を materialize した `V0 <= cons V2 V1` を連結した
`read V0; cons V1 V2 <= V0; V0 <= cons V2 V1; write V0` を実行 → `('a.'b)→('b.'a)` **正しく可逆**。
＝structural 残余＋materialize が**1本の正しい可逆プログラム**になることを確認（symbolic の分裂を解消）。

**残り（複数セッションの核）**：(a) この materialize/reverse/seq-fold/p2d-wrap を **R-WHILE マクロ**
（`ASSEMBLE-FP1` 等）で spec_av に実装。(b) fp1 main：入力 `(ri_fp3 . src)` を decode、**~45 スロットの
AV ストア初期化**（各 slot 動的 `('D.('var.k))`、k は自スロット番号）、V0 slot に部分 AV
`('C.(('S.src).('D.('var.0))))` を設定、`SPEC-CMD-AV(ri_fp3-body)`、ASSEMBLE。(c) ri_fp3 全体の特殊化
が端から端まで正しく動くこと（真の未知数）。

### （旧）C2. 残余アセンブリ
`SPEC-CMD-AV` の出力 `(Vl . RCode)` から実プログラム `comp_src` を構築：
- read 変数 = 動的入力変数（data slot の動的参照）。
- body = `RCode`。
- write 式 = 出力変数の最終 slot AV を `AV-LIFT`。fp1 では部分静的：src 部（静的）→ `(val src)` リテラル、
  結果部（動的）→ そのコード。よって write = `cons (val src) <result-code>` ⇒ 出力 `(src . [src](in))`。
- `comp_src` を ri が解する program-data 形式で符号化（直接実行／`[ri]((comp_src.in))` 双方で検証）。
- **完了**: 最小の `id` で `[comp_src](in) = (src . [src](in))` が**実評価で一致**。
  （まず id で 1 本残余を確立するのが山。ここに最も時間を割く。）

### C3. green 化 id → swap → reverse
- id（最小）→ swap（cond/eq の静的ディスパッチ）→ reverse（**動的ループ**＝実行時リスト上の loop は
  残余化。`SPEC-STEP-AV` の 'loop 動的経路がきれいな残余ループを出すか確認）。
- `src/TestSuite.ml:752-767` の `check_first_projection` を **ri.rwhile → ri_fp3.rwhile** ＋
  **spec.rwhile → spec_av.rwhile** に切替。
- **完了**: `./test-suite test first-projection` green（id/swap/reverse）。残余サイズ ≪ ri_fp3 p2d を記録。

### C4. 仕上げ
- `spec_av` を正準 spec にするか判断（fp2/fp3 の自己適用に必要）。必要なら移行（テスト参照の切替、
  `spec.rwhile` は legacy 残置 or 置換）。
- `FUTAMURA.md` / `analysis_partial_static_design.md` / メモリ更新。各 green サブステップでコミット。

## 4. critical files
| 役割 | パス |
|---|---|
| AV 特殊化器（改修主対象） | `examples/spec_av.rwhile`（'rep を structural 化、main 追加） |
| 名前付き変数版インタプリタ（fp1 対象） | `examples/ri_fp3.rwhile` |
| テスト（fp1 切替＋サイズ表明） | `src/TestSuite.ml`（`check_first_projection` 752-767） |
| 評価エンジン | `src/EvalRwhile.ml` |
| p2d 符号化 | `src/Program2DataRwhile.ml` |
| 設計・診断（必読） | `analysis_partial_static_design.md`（Stage C 節）, `plan_reversible_projections_impl.md` |

## 5. リスクと規模
- **C2 が本質的研究の核**（可逆言語のオンライン部分評価における健全性＝単一のきれいな可逆残余生成）。
  前回 3 度の実機検証で未収束。**id で最小残余を確立**してから swap/reverse に広げる。
- reverse は**動的ループの残余化**を試す（実行時リストに対する loop は静的展開できず残余化）。
- 複数セッション規模。1 green サブステップ＝1 コミット。`spec-av-*`/`spec-partial`/`rint` を全段維持。
- コミット前 gitleaks（フック自動）。push はユーザ承認後。

## 5.5 着手メモ（2026-06-15）— structural 'rep の正確なルール（前回分析の精緻化）

ベースライン実測（倒すべき相手）: `ri_fp3` p2d = **43,981 ノード / 358 KB**、`spec_av` p2d = 106 KB。
fp1 は現状 red（4件、ri.rwhile 対象）。`spec_av` の現 'rep は **symbolic**（`PAT-READ-AV`/`PAT-WRITE-AV`
が `PAT-READ-LEAF-AV2`/`PAT-WRITE-LEAF-AV2` ＋ `AV-CONS`/`AV-UNCONS` を使用）。
休眠中の structural 補助 `CHECK-PAT-STATIC-AV` / `PAT-READ-SIMPLE-AV` / `PAT-WRITE-SIMPLE-AV` /
`PAT-CLR-SIMPLE-AV` が残置（再活用候補）。

**核心の知見（symbolic が誤りだった理由＝可逆性）**：`Q <= R` を「R を AVr に読む → Q に書く」と
し、Q と AVr を再帰マッチさせるとき、残余 rep を出すのは**ただ1ケースだけ**：

| ケース | 動作 | 残余 |
|---|---|---|
| `Q=var ← AVr`（任意） | `slot[Q] := AVr`（動的なら残余変数へのエイリアス、部分静的はそのまま保持） | **なし** |
| `Q=cons(q1,q2) ← AVr が cons形（'C / 'S-cons）` | `AV-UNCONS` で分割し再帰（＝**入力分割**、静的部保持） | **なし** |
| `Q=cons(q1,q2) ← AVr が純'D葉` | 動的値を cons に**分配**するには記号的 hd/tl だと**動的値を2回読む＝非可逆**。可逆には実行時分割が必須 → `cons q1' q2' <= <AVr の残余変数>` を **RCode へ残余化**し、q1,q2 を新規動的残余変数に | **あり（この1ケースのみ）** |

symbolic 版はこの最後のケースで記号 hd/tl を使い、可逆な単一残余にならなかった（残余分裂・不正の
真因）。structural 版はここだけ残余 rep を出す。`var↔var` の動的移動はエイリアス追跡のみ（残余なし。
後でその変数を使う命令が AVr を lift して残余変数を参照する）。

**必要な補助**：(i) 新規**残余変数の採番**（残余プログラムの変数名前空間。動的化された var に割当て）。
(ii) AVr→残余パターン化（'S.v→`('val.v)`、'D.(var.k)→`('var.k)`、'C→`('cons...)`。既存 `AV-LIFT` が
'var/'val/'cons を出すため流用可能）。残余 rep の RHS はパターン（var/val/cons のみ）で表現可能
（rep の R は元来 var/val/cons だけなので AVr も必ずパターン化可能。hd/tl/eq は式専用で rep には出ない）。

**次の具体コード手順**（C1 実装の入口、各々テスト可能・additive 優先）：
1. 残余変数アロケータ（カウンタ slot or ストア末尾）を spec_av に用意（単体テスト）。
2. structural `PAT-WRITE` を「動的 cons-split のみ残余 rep を出す」版に（休眠 SIMPLE 系を土台に）。
3. SPEC-STEP-AV の 'rep を symbolic → 上記 structural へ差し替え、`spec-av-step` を新仕様で green に更新。
4. （C2）SPEC-CMD-AV 出力＋出力変数 slot の `AV-LIFT` で comp_src を組立、id で `[comp_src](in)=(id.'a)`。

## 5.6 着手の到達点（2026-06-15, セッション2）

実装・テスト済み（全 commit, spec-av-* / assemble-fp1 全 green, OFF & hygiene）：
- **C1** structural 'rep（`PAT-WRITE-STRUCT`）— `b735ca3`
- **C2①** `ASSEMBLE-FP1`（materialize＋MAKE-SEQ＋p2d-wrap）— `3413c2c`
- **C2②a** `AV-INIT`（N スロット静的nilストア）— `6c76925`
- **C2②b** fp1 main（spec_av のデフォルト main＝エントリポイント）＋ swap E2E テスト — `6666aea`
  - `[spec_av]((swap . 'a))` → 残余、`[comp]('b)=('b.'a)` ✅
- N を 50 に拡張（ri_fp3 の 45 変数を収容）

**C2③ ri_fp3 初接触（重要な到達）**：`[spec_av]((ri_fp3 . id))` が **完走** し、
**358KB → 3.4KB（約100倍縮約）** の残余を生成。残余の内訳 = **ass×6, rep×1, cond×0, loop×0**
＝**解釈系のディスパッチ（cond/loop）が静的に完全消去**され、動的データ移動のみ残った。
＝AV特殊化（静的ディスパッチ解決＋ループ展開＋structural rep）が**スケールして機能**。前回
（symbolic で残余分裂・肥大）を大きく超えた。

**残課題（診断修正 2026-06-15）**：comp_src を `[ri]((comp.x))` で実行すると `error in update`。
**当初の「出力二重構築」仮説は誤り**。comp_src をデコードすると：
```
read V2 ; V35^=V2; V36^=V2; V37^=V35; V35^=V37; V0^=V37; V37^=V0;
          V2 <= cons(val(id), V0); write V2
```
真因＝**残余が非可逆**：(a) `V36^=V2` は対応する clear が無い**宙吊りコピー**、(b) 入力変数 V2 が
**一度も consume されない**ため最後の `V2 <= cons(id,V0)` が非nilの V2 に書いて衝突。
データは ri_fp3 の**非破壊 LOOKUP（X^=V[J] のコピー）**で V2 から運び出されるが V2 が clear されない。
swap が通るのは materialize が同一変数を read-then-write（`V0 <= cons (var0) 'a`）で可逆だから。
ri_fp3 ではデータが変数間を**移動**（V2→…→V0）し、LOOKUP コピーとその逆 INV-LOOKUP clear の
**残余化が非対称**（前向きコピーは残余化、逆向き clear が静的解決で消失）→ 宙吊り V36＋未consume V2。
＝可逆言語オンライン部分評価の健全性問題（前向き/逆向きの残余化バランス保持）。

**最小再現で根本原因を特定（2026-06-15, 候補B 実施）**：
プログラム `read V0; cons V1 V2 <= V0; V3^=V2; V2^=V2; V0 <= cons V1 V3; write V0`
（split→データを V2 から V3 へ move→V2 を self-clear→rejoin＝ペア恒等）を `fp1(.,'a)` すると
comp = `read V0; V3^=V0; V2^=V0; V0 <= cons (val 'a) V3; write V0` となり実行で `error in update`。
2つの欠陥（いずれも**変数間の動的値エイリアス**が原因）：
1. **エイリアス下の self-clear**：`V2^=V2`（V2クリア）が、V2のスロットが var0 を**エイリアス**していた
   ため `V2^=V0` に残余化 → 実行時 V2 は nil なので**クリアでなくセット**になる。
2. **入力変数が consume されない**：部分静的入力の structural split は実行時命令を出さないので
   V0（動的入力を保持）がコピーされるだけで clear されず、末尾の rejoin が非nilの V0 に書いて衝突。
根本＝部分入力の動的半分が変数を**エイリアス**（`('D.('var.dataidx))`）し、データ移動/クリア時に
**再ホーム化されない**。（swap・split-rejoin が通るのは I/O が同一変数でエイリアスが跨変数化しないため。）

**修正方針（確定）= no-alias 不変条件 / 入力 peel**：
- 動的スロット k は常に自分自身 `('D.('var.k))` を指す（他変数をエイリアスしない）。変数間の動的値
  移動は**実行時 move（残余 rep）を出して**所有権を移す。
- 部分静的入力の structural split は、動的半分を**残余 move でターゲット変数へ extract**する
  （spec.rwhile の peel `Data <= ReadVar` を AV へ移植）。これで入力変数が runtime で consume され、
  self-clear も自分自身を指すので正しくクリアになる。
- 該当箇所：fp1 main の入力 AV 設定／`PAT-WRITE-STRUCT` の var-write（動的エイリアス AV の書き込み時に
  再ホーム move を出す）。各々単体テストで検証（self-clear、跨変数 move、move-clear-rejoin 最小再現）。
（再現: 上記プログラムの p2d を `(P . 'a)` で `./src/ri examples/spec_av.rwhile`。）

**no-alias 修正 完了（2026-06-15, commit 3a0c42d）**：`PAT-WRITE-LEAF-REHOME` を実装。
動的-var 葉 `('D.('var.k))` を変数 Q(≠k) に書くとき、エイリアスせず**実行時 move `Q <= ('var.k)`
を残余化**し slot を自己参照 `('D.('var.Q))` に。`PAT-WRITE-STRUCT` の全 leaf write が使用。
検証（assemble-fp1 群）：cross-var move + 可逆クリア(`V2^=V3`) + rejoin の fp1 が **ri 経由で
[comp]('d)=('a.'d)** に成功。spec-av-step の input-split は re-home 挙動（move `V2<=V0`）に更新。
全 AV 群 green（OFF & hygiene）。

**新たに判明した次の壁**：ri_fp3 は**非可逆な self-clear `X^=X`**（`V1^=V1; V2^=V2`）を使う。
`X^=X` は情報を捨てる非可逆操作で、**可逆自己解釈系 ri.rwhile は self-interpret できない**
（最小確認: `cons A B<=X; A^=A; X<=cons A B` を非nil A で `[ri]((.))` 実行→`error in update`、
直接実行は正しい）。よって ri_fp3 残余を ri で走らせるには ri_fp3 を**可逆クリア**（`V2^=Data` 等、
値を保持する変数で消す）に書き換える必要がある（候補C）。no-alias 修正自体は正しいと検証済み。

**次の手の候補**：
- (A) 深掘りデバッグ：ri_fp3 の LOOKUP/UPDATE（名前付き添字コピー）特殊化を追跡し、非対称残余化
  （宙吊りコピー/未consume）の発生点を特定して修正。
- (B) 最小再現：ri_fp3 流の「添字付き非破壊コピー＋その逆」を使う 2 変数の極小プログラムで
  fp1 を回し、不均衡を高速に切り分ける（ri_fp3 全体より速い）。
- (C) ri_fp3 のデータ init/extract（`UPDATE-FP3(I',Data); LOOKUP-FP3(I',Data)` 等）を PE で
  round-trip しやすい形（コピーでなく move ベース）に書き換える。
- (D) チェックポイント：100倍の静的縮約は単体で強い結果。ここで記録し小休止。
（再現: `RIFP3=$(./src/ri -exp -p2d examples/ri_fp3.rwhile); IDP=$(./src/ri -exp -p2d examples/id.rwhile);
printf '(%s . %s)' "$RIFP3" "$IDP" > in.val; ./src/ri examples/spec_av.rwhile in.val`）

**候補C 完了（2026-06-15）= ri_fp3 を可逆クリアに書換**：`ri_fp3.rwhile` main の
`cons V1 V2 <= V0; Prog ^= V1; V1 ^= V1; Data ^= V2; V2 ^= V2;`（copy-then-self-clear、
非可逆 `X^=X` を含む）を**可逆 pattern-move** `cons V1 V2 <= V0; Prog <= V1; Data <= V2;`
に置換。V1/V2 は依然早期に出現するので p2d 添字 1,2 は不変。
- **回帰確認**：ri_fp3 の**直接**自己解釈は不変＝正しい。`[ri_fp3]((swap.('a.'b)))=(swap.('b.'a))`、
  `[ri_fp3]((id.'a))=(id.'a)`（新テスト `ri_fp3 reversible-clear self-interp: id/swap`、assemble-fp1 群）。
- **候補C の成果**：fp1 残余が **ri 経由で実行できるようになった**（以前は `X^=X` で `error in update`
  クラッシュ）。可逆 move は残余に可逆 `rep` move として落ちる。

**ただし fp1 はまだ green ではない（より深い特殊化バグを新たに局所化）**：
`comp=[spec_av]((ri_fp3 . src))` の残余を ri で実行すると**意味的に誤り**。
- src=id：`[comp]('a)` の動的部は `'a`（id なので恒等で偶然正しい）。だが echo（静的 src 部）が
  **壊れている**：`'val` リテラルに焼かれた id 本体が `('ass.(('var.nil).('val.nil)))` ではなく
  `(('var.K1).('var.K2))`（K1≈33, K2≈32 の深い unary 添字＝ストアスロット添字が `'val` に漏出）。
- src=swap：動的部すら誤り。`[comp](('a.'b))` が `('a.'b)`（**swap されない**＝被解釈プログラムの
  操作が残余に落ちていない）。echo も同様に壊れる。
- 切り分け：**ri_fp3 自体は正しい**（直接自己解釈は OK）ので、バグは **spec_av による ri_fp3 の
  特殊化**側にある。具体的には STEP ループ（命令の destructure→処理→`Cd' <= cons (cons Tag Arg) Cd'`
  再組立）の特殊化で、(1) 被解釈操作の残余化が脱落、(2) 静的 program 再構成（Tag/Arg）が
  ストアスロット添字の `('var.k)` を `'val` に焼き込んで破壊、の2症状。
- **次の手**：候補B（ri_fp3 流の「添字付き非破壊コピー＋逆」を使う極小2変数プログラムで fp1 を回し、
  Tag/Arg 再組立の特殊化が壊れる最小ケースを高速に特定）→ PAT-WRITE-STRUCT / AV-LIFT / LOOKUP-UPDATE
  特殊化の該当点を修正。

**候補B 実施（2026-06-15）= バグの精密局所化（単体テスト駆動）**：
spec_av の各マクロを harness で単体検証しながら、fp1-via-ri_fp3 残余を pp_cmd で
デコードして追跡した。

- **'ass コピー/クリア仮説は否定**：`X ^= V[J]` の copy/inverse-clear を SPEC-CMD-AV で
  単体テスト。現行コード（自己参照 ('D.('var.K))）は **clear を認識せず抽象ストアが古くなる**
  が、**残余そのものは正しい**（move_clear が通るのはこのため）。alias 化で clear 認識を
  入れる修正を試作したが、**alias は lift を壊す**（V3 が V2 を alias すると lift(V3)=('var.2)
  となり残余が `V2^=V2` に化ける＝error in update）。→ alias 不可。revert 済み。
- **真因の局所化**：fp1-via-ri_fp3 残余を decode すると、`swap` と `sx_splitjoin`
  （uncons→即 rejoin＝恒等）の**残余 body がバイト一致**。両者とも
  `read V2; V36<=V2; V35<=V36; V36^=V35; V35^=V36; V0^=V36; V36^=V0; V2<=cons({echo},V0); write V2`
  ＝**純粋なデータ・ルーティングのみで hd/tl/cons が消滅**。つまり spec_av は
  **ri_fp3 のスタックベース EVAL-PAT / INV-EVAL-PAT を畳み込んで消している**。
  動的値に対する構造操作（uncons/cons）が残余に落ちず、swap の並べ替えも失われる。
- **切り分け**：直接特殊化（test_fp1_main_swap = spec_av が swap を直接特殊化）は**正しい**。
  よってバグは spec_av のコア 'rep/'cons/'hd/'tl ではなく、**ri_fp3 のスタックマシン
  間接（EVAL-EXP-FP3/EVAL-PAT-FP3 とその INV-、St への push/pop）の特殊化**に固有。
- **回帰アンカー**：`test_fp1_ri_fp3_known_bug`（assemble-fp1 群）が「swap と splitjoin の
  残余 body 一致」をアサート（＝バグの存在）。修正されればこのテストが**落ちて気付ける**。
  最小ソース `examples/sx_splitjoin.rwhile` を fixture として追加。
- **次の手**：特殊化の**途中の抽象ストア**を覗いて、swap STEP 後に V0 が
  ('C.((D tl).(D hd)))（並べ替え済み記号値）を保持しているか、それとも d のままかを判定する。
  - 保持していれば → バグは**抽出/出力（lift）側**。
  - d のままなら → バグは **STEP（EVAL-PAT のスタック記号評価）側**。
  そのために spec_av に「STEP 後ストア dump」フックか、ri_fp3 を 1 ステップだけ回す
  極小ドライバが要る。

**STEP vs lift の確定（2026-06-15）**：fp1 main を ASSEMBLE 直前で打ち切り、抽象ストア
V[FpJ]（ri_fp3 の出力変数）を覗くハーネスを実装（`test_fp1_step_bug_opaque_result`,
`fp1_store_out_slot`）。結果：swap も sx_splitjoin も
V[FpJ] = `('C.(('S.<src>).('D.('var.nil))))`。**Result 半分(tl)=`('D.('var.0))` の素の
不透明動的値**で swap 構造 `('C.((D tl).(D hd)))` になっていない。
→ **バグは STEP 側で確定**（lift/ASSEMBLE は無実）。ri_fp3 のスタックマシン特殊化で
動的値が**不透明 `('D.('var.k))` のまま流れ**、hd/tl/cons が記号追跡されない。
回帰アンカー：swap の Result が不透明であることをアサート（修正で落ちる）。

**次の手**：STEP ループの**各反復後**に抽象ストアを dump し、ri_fp3 が
`cons V1e V2e <= V`（スタック頂上の動的値分解）を行う箇所で AV-UNCONS の 'D 分岐
（`A1<=cons 'D (cons 'hd V)`）が呼ばれ `('D.('hd.(var k)))` を生成しているか、
PAT-WRITE-STRUCT が pure-D 値の分割を残余化しているかを単体で確認する。

**根本原因 確定（2026-06-15）= PAT-WRITE-STRUCT がネスト cons パターンを扱えない**：
`test_pat_write_nested_split` で精密に再現。`cons (cons V1e V2e) St <= var0`
（var0 = ('C.((D var0).(S nil)))、深さ2パターン）を SPEC-CMD-AV で実行すると、
**V1e=V2e=('S.nil) のまま・residual=nil**＝**内側 cons の動的値が捨てられる**。
- 原因：`PAT-WRITE-STRUCT` の real-split 分岐（spec_av.rwhile L537-542）は 1 段だけ
  AV-UNCONS し、各サブパターンを **`PAT-WRITE-LEAF-REHOME` に委譲**する。だが
  PAT-WRITE-LEAF-REHOME は **var 葉しか扱わず**、サブパターンが cons だと else 分岐
  `WA ^= WA` で**値を破棄**（L587）。マクロは再帰不可なので深さ1までしか処理できない。
- これが fp1-via-ri_fp3 の真因：ri_fp3 のスタック分解 `cons (cons V1e V2e) St <= St`
  は深さ2 → 内側が消え、swap/全変換が恒等ルーティングに潰れる。直接 swap
  （`cons Y Z <= X`、深さ1）が通るのと整合。

**修正方針＝PAT-WRITE をイテレーティブ（worklist）化**：マクロ再帰不可のため、
ri_fp3 自身の EVAL-PAT と同じく**明示スタックでループ**する PAT-WRITE に書き換える。
(subPattern, subAV) ペアの作業スタックを持ち：
- subP が var 葉 → PAT-WRITE-LEAF-REHOME。
- subP が cons かつ subAV が pure-D → 分割を residualize（subP 配下の全葉を
  動的自己参照にし、`subP <= code` を1本出す）。深さ>1 の pure-D には全葉クリアが要る
  （PAT-CLR-SIMPLE-AV は深さ1のみ → これも要 worklist 化、または PAT-CLR-DEEP）。
- subP が cons かつ subAV が 'C/'S → AV-UNCONS して (p1,a1),(p2,a2) をスタックに push。
PAT-READ 側も同様にネスト対応が要るか確認（読み取りは AV-UNCONS が再帰的でないか）。

**worklist PAT-WRITE 実装（2026-06-15, 部分前進）**：
- `PAT-WRITE-ITER` / `PAT-WRITE-ITER-STEP` を spec_av に実装（明示スタックで任意深さの
  cons パターンを処理）。var葉→REHOME、cons+pure-D→分割を residualize（深さ1葉を
  PAT-CLR-SIMPLE-AV で自己参照化）、cons+'C/'S→AV-UNCONS して push。定数 cons パターン
  （両葉が 'val、ri_fp3 のマーカ `cons 'consB nil` 等）は assertion として discard するガード付き。
- **単体検証 OK**：`test_pat_write_iter_nested` で深さ2 `cons (cons V1e V2e) St <= var0`
  （var0=('C.((D var0).(S nil)))）を正しく分割（V1e,V2e 動的化＋残余 `cons V1e V2e <= var0`、
  St に残り）。PAT-WRITE-STRUCT が捨てていた内側を正しく扱える。
- **まだ 'rep 経路に配線していない**：full ri_fp3 に配線すると、ri_fp3 のマーカ機構
  （EVAL-PAT の 'consE 処理など）で**var を含む cons パターンが静的アトム 'cons と対**になり
  AV-UNCONS が `cons H Tl <= 'cons`（アトム分解）で落ちる。定数 cons ガードでは防げない
  （葉に var を含むため）。id（cons rep 無し）は通るが splitjoin/swap（cons rep 有り）が落ちる。
  → 当面 PAT-WRITE-STRUCT を配線したまま（suite green）、worklist は単体テスト済みで温存。
- **次の手**：落ちる正確なパターン/値ペアを特定する。AV-UNCONS を安全化（'S で非 cons 値を
  検出して leaf-discard へ）するか、ri_fp3 のマーカ機構の特殊化時に over-decompose しない
  ように EVAL-PAT のスタック表現を見直す。R-WHILE には安全な「is-cons」判定が無いため、
  AV 側のタグ（'S 値が cons か）を別表現で持つ等の工夫が要るかもしれない。

**配線時の壁を精密特定（2026-06-15）= 静的パターン照合の失敗検出（is-cons 不在）**：
PAT-WRITE-ITER を 'rep に配線し、静的分割ごとに `(WiP . WiA)` センチネルを残余へ吐く
デバッグ版で full ri_fp3/sx_splitjoin の静的分割ペアを採取（6件）。決定的な例：
- `P=cons(cons(V34,V33), V30)  A=('S.(nil.nil))`：深さ2の **var を含む** cons パターンが
  静的値 (nil.nil) と対。外側 uncons → 内側 cons(V34,V33) が **静的 nil/atom** と対になり、
  AV-UNCONS の `cons H Tl <= V`（V が atom 'cons や nil）で落ちる。
- atom（'cons 等）は **静的プログラム構造**（swap_data の 'cons/'rep タグ）が ri_fp3 の
  再構成を通って値位置に流れたもの。
- 本質：**var を含む cons パターンが静的アトム/nil と対になるのは静的パターン照合の「失敗」**
  （= その 'rep は実行されない dead path）。実 ri_fp3 は正しく自己解釈するので実データ上は
  起きないが、特殊化時に spec_av がこの（cond で枝刈りされない）経路を評価してしまう。
  旧 PAT-WRITE-STRUCT は深さ1で discard していたため露呈しなかった。
- **R-WHILE に安全な is-cons が無い**（hd/tl は atom で例外、=? のみ安全）ため、AV-UNCONS は
  「静的値が cons か」を判定できず crash する。

**配線に必要な設計判断（次セッション）**：
1. AV の静的値に **cons 性タグ**を持たせる（('Satom.v)/('Scons.v) 等）か、is-cons を
   安全に判定する仕組みを AV 代数に入れる。→ AV-UNCONS が静的 atom/nil を検出して
   「静的照合失敗＝dead」を扱える。
2. または spec_av の 'rep 特殊化で**静的パターン照合の失敗**を一級に扱い、dead な 'rep を
   枝刈り（残余を出さない）。
3. または ri_fp3 のスタック機構の特殊化が dead path を評価しないよう、EVAL-PAT 経路の
   静的ディスパッチ／表現を見直す。
worklist 自体（任意深さ分割）は単体検証済み（`test_pat_write_iter_nested`）。残るのは
この静的照合失敗の扱いのみ。

**pair? 追加＋ガードで atom crash 解決、ただし配線で新たに発散（2026-06-15）**：
- 言語に `pair?`（Scheme流 cons 判定、p2d タグ `'pairp`）を追加（commit d0b793f）。
- PAT-WRITE-ITER の real-split に **pair? ガード**を追加：'S 値が cons でなければ
  「静的パターン照合の失敗＝dead」として discard（AV-UNCONS で atom を割って落ちるのを防ぐ）。
- 効果：**atom crash は解消**。配線すると assemble-fp1 0–6 が通り（以前は配線で crash）、
  小さい fp1（swap/split-rejoin/move-clear = tests 2/3/4）は**配線下でも正しく通る**
  ＝PAT-WRITE-ITER+pair? は健全。
- **新たな壁**：full ri_fp3 の fp1（test 7）は配線すると**発散（ハング）**。ri_fp3 の
  スタックマシンの**静的ループが特殊化中に無限展開**するとみられる（PAT-WRITE-ITER が
  構造操作を正しく残余化するようになった結果、ストアの静的/動的分類が変わり、ある
  静的ループの終了テストが永遠に成立しなくなる、等）。crash ではなくループ。
- 当面 PAT-WRITE-STRUCT を配線したまま（suite 非ハング）。PAT-WRITE-ITER+pair? は
  単体テスト（test 10）＋小 fp1 で検証済み。
- **発散の切り分け 完了（2026-06-15, CLI で確認）**：PAT-WRITE-ITER を配線し、
  `(ri_fp3_p2d . src_p2d)` を `./ri spec_av.rwhile` で直接実行（timeout 45s）：
  - **fp1(id)（cons rep 無し）→ 完了（exit 0、正常終了）**。
  - **fp1(sx_splitjoin)（cons rep 有り）→ 発散（timeout、出力なし）**。
  → 発散は **cons の 'rep → ri_fp3 の EVAL-PAT スタックマシンのループ**を
  PAT-WRITE-ITER で特殊化したときに起きる。PAT-WRITE-ITER 単体や直接 fp1(swap 等)は
  正常なので、原因は **spec_av の loop 特殊化（静的アンロール）が無限展開**すること。
  （再現: `./src/ri -exp -p2d examples/ri_fp3.rwhile`,`id.rwhile`,`sx_splitjoin.rwhile`
  を p2d 化し `printf '(%s . %s)' RIFP3 SRC > in.val`、PAT-WRITE-ITER を配線して
  `timeout 45 ./src/ri examples/spec_av.rwhile in.val`。id は返り、split はハング。）
- **次の手**：spec_av の loop/lcheck 特殊化に「静的アンロール回数の上限→超えたら
  動的化（loop を residualize）にフォールバック」を入れて発散を止め、まず**停止性を確保**
  → その上で残余の正しさを確認。並行して、なぜ ITER だとループ制御が静的に終わらなく
  なるのか（PAT-WRITE-ITER が worklist 値の静的/動的分類を STRUCT と変えている点）を精査。

**発散は「真の無限」と確定＋構造的結論（2026-06-15）**：
- fp1(sx_splitjoin) を ITER 配線で 240s 実行 → **0 バイト出力のままハング**＝特殊化が
  残余を一切生成せず無限ループ（巨大有限ではない、真の無限静的アンロール）。
- 原因の核心：`'lcheck` の出口テスト F が**毎反復で静的 false に評価される**。spec_av は
  「ループ制御が静的だが永遠に出口に達しない」と判断し無限展開する。実 ri_fp3 は正しく
  停止するので、これは**特殊化時の分類が誤り**（データ依存で本来は動的化すべき制御を
  静的 false に固定してしまう）。
- さらに spec_av の `'lcheck` は出口テストが**動的**だと `'error <= '41` で**エラーになる**
  ＝「静的 entry の後に出口がデータ依存になったループ」を residualize する経路が無い。
  加えて動的 entry の residualize はループ本体を**そのまま（未特殊化で）**埋め込むだけ。

**結論（重要）**：ri_fp3 の**スタックマシン型 EVAL-PAT/EVAL-EXP は、ネストパターンを
正しく扱うと、データ依存ループの制御分類が破綻して clean な部分評価ができない**。
単純な「アンロール上限＋エラー」は**停止性は得るが fp1 green にはならない**。
「上限＋動的化フォールバック」も、現 spec_av のループ residualize が本体を未特殊化で
コピーするだけなので、きれいなコンパイル結果にならない。

**取り得る方向（次の判断）**：
1. **停止性のみ確保**：spec_av の loop unroll に上限を入れ、超過で clean error。
   ハングは消えるが fp1 は green にならない（失敗を明示するだけ）。
2. **spec_av のループ処理を本格改修**：`'lcheck` 動的出口の residualize 実装＋
   ループ本体の特殊化＋制御の動的伝播修正。大規模・高リスク。
3. **インタプリタ設計の変更**：スタックマシンをやめ、構造再帰的（プログラム構造を
   直接たどる）な PE フレンドリな mini self-interpreter を fp1 用に用意する。
   スタック越しの値追跡が無くなり、ループ制御分類の破綻を回避できる見込み。最も筋が良い。
4. **fp1 を別ターゲットで達成**：ループを含まない/単純な被解釈プログラム集合に限定して
   fp1 green を先に示し、ループ対応は段階的に。

PAT-WRITE-ITER + pair? は健全で単体検証済み（ネスト分割・小 fp1 で正しい）。残るのは
この**ループ特殊化の構造問題**で、方向 2/3 のどちらに投資するかは設計判断。

**インタプリタのバグ疑い → 核は健全と確認（2026-06-15）**：
発散が「PE の本質的限界」か「R-WHILE のバグ」かを切り分け。
- **-hygienic-macros でも発散**（default と同一）→ マクロローカル名衝突（衛生性）バグではない。
- `evalLoop`（可逆ループ、再入時の ¬e 表明あり）、`CCond`/`pair?`（ガードは正しい）、
  `evalPat`/`inv_evalPat`（ネストパターン対応済、非cons は明示エラー）、`rupdate`、
  `AUX`（範囲外添字は Vl 枯渇でエラー＝ハングしない）を精査 → **OCaml インタプリタ核は健全**。
- evalLoop に一時計装（ループ反復カウンタ）を入れて発散の所在を特定：
  内側 `AUX`（=? Cnt …）を除外して数えると、**外側ループ
  `=? Cd' nil / =? Cd nil`（SPEC-CMD-AV のコマンド送り）と
  `=? E' nil / =? E nil`（SPEC-EXP-AV の式送り）が交互に無限に回る**。
  → 発散は **spec_av の特殊化アルゴリズム自体**（ri_fp3 の内部ループの静的アンロールが
  止まらない＝ループ worklist が縮まない）。OCaml 核ではなく **R-WHILE プログラム spec_av のバグ**。
- 有力仮説：ITER で worklist 操作 `cons (cons RTag RArg) R <= R` を正しく分割した結果、
  R（パターン/コマンド worklist）が縮まなくなる、または余分に push される。
  **本質的限界ではなく fixable な spec_av バグの可能性**が高い（PAT-WRITE-ITER が
  worklist 用の 'rep を特殊化する際の R の扱いを精査すれば判明する見込み）。
- 次：発散している外側ループ 1 回分の入出力（Cd/E が反復でどう変化するか）を計装して、
  どの worklist 'rep が R を縮めないかを特定 → PAT-WRITE-ITER/PAT-READ-AV の該当点を修正。

**発散箇所を精密特定（2026-06-15）= worklist が循環して縮まない**：
`show` 計装で発散ループを特定：
- 発散ループの until テスト = `=? V7 nil`、毎反復 `('S.nil)`（静的 false）。
  → V7（ri_fp3 の EVAL-PAT/EVAL-EXP の worklist R）は**静的に非nilの定数値のまま縮まない**。
- V7 の値を反復ごとに dump → **4 状態を無限に循環**（nil に到達しない）：
  1. `((var19) . (cons (cons 'consB nil) (var7)))`
  2. `(cons (cons 'consB nil) (var7))`
  3. `((cons 'consB nil) . (var7))`
  4. `((val nil) . ((var19) . (cons (cons 'consB nil) (var7))))` → 1 へ
- **決定的証拠**：worklist 値に `('var.7)`（worklist 変数**自身**の添字）と `('var.19)` が
  含まれる。被解釈プログラム swap の変数は添字 0,1,2 のみ → これらは**混入**。
  worklist が**自己参照的・循環的構造**になり、`'consB`/`'consE` マーカ処理が同じ cons を
  再 push し続けて R が空にならない。
- → **PE の本質的限界ではなく spec_av の具体バグ**。PAT-WRITE-ITER が ri_fp3 の
  マーカ処理 'rep（深さ3の `cons E2 (cons E1 (cons (cons 'consB nil) R')) <= R'`、
  worklist R' が read かつ rewrite される）を特殊化する際、worklist を**自己参照を含む
  循環構造に壊す**。
- **修正対象**：worklist 変数が read かつ write 両方に現れる 'rep を PAT-WRITE-ITER が
  処理する際の R' の扱い（おそらく REHOME / 自己参照書き込みが worklist に ('var.self) を
  混入させる）。この 'rep を最小ケースで切り出して PAT-WRITE-ITER の単体テストにし、
  worklist が正しく縮む（自己参照を混入しない）よう修正する。

**最小再現で絞り込み（2026-06-15）= 静的ケースは正しい、動的相互作用が原因**：
疑った 'rep `cons E2 (cons E1 (cons (cons 'consB nil) R)) <= R`（worklist R が read+write、深さ4）を
**静的値で最小再現**（R=(e2.(e1.((consB.nil).rest)))）→ PAT-WRITE-ITER は**正しく動く**：
E2='e2, E1='e1, **R='rest（正しく縮む）**、残余なし、自己参照の混入なし。
→ **純静的の read+write worklist rep は健全**。よって発散時の worklist 破壊（自己参照 ('var.7)
混入・循環）は **full ri_fp3 の動的コンテキスト**（スタック St が動的値 ('D.('var.k)) を持ち、
残余コードの var 参照が worklist と絡む状況）でのみ起きる。静的最小ケースでは再現しない。
- 次：full 実行で **最初に ('var.7)（worklist 自身の添字）が worklist に混入する瞬間**を計装で
  捕捉する（PAT-WRITE-LEAF-REHOME / AV-LIFT が動的自己参照を worklist 値へ書く点を特定）。
  これは動的×worklist の相互作用の追跡で、静的最小化では不可。

**🟢 fp1 GREEN 達成（2026-06-15）= 極小自己解釈系 ri_min で第1射影成立**：
方針転換「まず単純プログラムで fp1 green」を実行。`examples/ri_min.rwhile` を新規作成：
- 被解釈言語は1命令（Op='swap なら (a.b)→(b.a)、それ以外='id）。
- **深さ1 cons パターンのみ・静的ディスパッチ1個・ループなし** → spec_av は実証済みの
  depth-1 PAT-WRITE-STRUCT だけで特殊化でき、**有限・正しく終了**（ri_fp3 のスタックマシン
  深ネスト由来の発散を完全回避）。
- 検証（`first-projection-min` 群、green）：
  - `[[spec_av]((ri_min . 'swap))](('a.'b)) = ('swap.('b.'a))` = `[ri_min](('swap.('a.'b)))` ✓
  - `[[spec_av]((ri_min . 'id))]('q) = ('id.'q)` ✓
- **これが本処理系で初の真の第1 Futamura 射影 green**（インタプリタを静的ソースで特殊化し、
  正しい残余を生成）。直接特殊化（test_fp1_main_swap 等）と違い、**インタプリタ経由**で成立。

**次の段階（fp1 を richer に）**：
- ri_min を**命令列（seq）**対応に拡張（静的ループで命令を辿る。静的ループ unroll は
  spec-av-step で実証済み）。深さ1パターンを維持。
- さらに hd/tl/eq/cond 等を depth-1 で足し、扱える被解釈言語を広げる。
- ri_fp3（スタックマシン深ネスト）の発散修正は別トラックとして保留（worklist 自己参照
  混入の動的トレースが必要）。ri_min 路線で fp1→fp2→fp3 を先に通すのが有望。

**fp1 を命令列(seq)に拡張（2026-06-15）= 静的ループ unroll も green**：
`examples/ri_seq.rwhile` 新規作成：被解釈プログラム = op のリスト [o1..on]、**静的ループ**で
各 op を Data に適用（深さ1パターン維持）。spec_av が静的ループを unroll し fp1 成立：
- `[[spec_av]((ri_seq.[]))](('a.'b)) = ([].('a.'b))` ✓
- `[[spec_av]((ri_seq.[id,swap]))](('a.'b)) = ([id,swap].('b.'a))` ✓（ループ2回＋swap1回）
- [], [id], [swap], [id,id], [id,swap], [swap,id] など **swap ≤1 個の列は全て green**。
- `first-projection-min` 群 = 4 テスト green（ri_min swap/id + ri_seq []/[id,swap]）。

**既知の限界（別バグ）**：`[swap,swap]`（値の置換＝恒等）は no-alias move ロジックが
残余に**素朴な変数交換 `V4 <= V3; V3 <= V4`** を出し、実行時に両方非nilで衝突（error in update）。
正しくは swap-via-temp 残余が必要。swap を2個以上含み**値の置換**が起きる列のみ該当。
→ no-alias REHOME の move 発行を「相互参照（置換）の場合は一時変数経由の3手交換」にする修正が次。

**🟢 swap-via-temp 修正 完了（2026-06-16）= 値の置換列も green**：
根因を残余デコードで確定：iter1 の `X <= cons B A` が slot[X]=('C.((D V3).(D V4)))（葉が
相互参照）を作り、iter2 の split `cons A B <= X` がこれを V4,V3 へ戻す＝**2変数の置換
（transposition）**。PAT-WRITE-STRUCT は REHOME を2回逐次呼び、各々が in-place move を
出す→ `V4<=V3; V3<=V4`（両ターゲット非nil）で衝突。
- 修正：`PAT-WRITE-STRUCT` の real-split 分岐に **transposition 検出**を追加（両葉が var で、
  各 sub-AV が相手葉の変数への動的参照＝WSa1=('D.('var.i2)), WSa2=('D.('var.i1)), i1≠i2）。
  検出時は `SWAP-VIA-TEMP(i1,i2,RCode)` で**一時変数経由の3手交換** `tmp <= V_i1; V_i1 <= V_i2;
  V_i2 <= tmp` を残余化し、両 slot を自己参照に戻す。非transposition は従来の逐次 REHOME。
- 一時変数：予約済み**ユニーク添字 100**（`TEMP-IDX` マクロ、unary）。被解釈プログラムの
  変数添字（<50）より上、かつ ri.rwhile のストア（~300 slot）内なので衝突しない。atom 添字
  ('tmp) は ri.rwhile の AUX 計数ループ（unary 前提）を壊す（store 末尾突破でクラッシュ）ため不可。
  複数 transposition でも各 swap が tmp を nil に戻すので 1 添字を再利用可。
- 検証：`[[spec_av]((ri_seq.[swap,swap]))](('a.'b)) = ([swap,swap].('a.'b))` ✓（ri 経由・手trace一致）。
  `first-projection-min` 群 = **5 テスト green**（[swap,swap] 追加）。assemble-fp1 / spec-av-step /
  av-algebra / spec-av-exp / spec-macros / spec-partial 全 green、hygiene ON も green、回帰なし。
  （first-projection 群の 3 red は spec/rint ベースの既存 deferred、本修正と無関係。）

## 5.7 fp2 前提：pair? の特殊化＋自己解釈（2026-06-16, commit 71c608c）

spec_av 自身が `pair?` を使う（PAT-WRITE-ITER の静的照合失敗ガード）ため、spec_av の p2d は
`'pairp` を含む → fp2（spec_av の自己適用）には `'pairp` の特殊化・自己解釈が必須だった。実装：
- **AV-PAIRP**（AV代数）：static→既知bool、partial-static cons→静的TRUE、dynamic→残余 `pair?`。
  SPEC-EXP-AV-STEP に `'pairp`/`'pairpE`（単項、'hd と同型）を追加。
- **ri.rwhile** EVAL-EXP-STEP に `'pairp`/`'pairpE`：オペランドを pop、`pair? V1` を計算、bool を
  push、入力 V1 を履歴スタック H に退避（'eq と同型で可逆）。
- 検証：spec-av-exp +4（11 green）、ri 自己解釈の pair? == 直接評価・可逆（eval-exp +1, 14 green）、
  全AV群・macro・inversion green、hygiene ON green、回帰なし。
- 残：`ri_fp3.rwhile`/`spec.rwhile` は未だ `'pairp` 非対応（それらの fp2/fp3 自己適用時のみ問題）。

## 5.8 fp2 初接触（2026-06-16）= 終了する（発散しない）／AV-UNCONS 安全化／次ブロッカ局所化

`[spec_av]((spec_av . ri_min))` を実機で初めて回した（外側 spec_av の store N を 50→250 に拡大：
spec_av は展開後 ~201 変数、p2d は 2.8MB）。重要な所見：
- **発散しない**（ri_fp3 と違い有限で停止）。120s 以内にエラーで返る。
- 第1ブロッカ＝**AV-UNCONS が静的 non-cons を分割しようとしてクラッシュ**
  （`cons H Tl <= nil`）。ri_fp3 で documented の is-cons 不在問題と同型で、spec_av 自身の本体が
  PE 中に静的 nil への cons-read を含むため発火。
- **修正（commit 予定）**：`av.rwhile` / `spec_av.rwhile` 双方の AV-UNCONS の 'S 分岐に **pair? ガード**。
  静的値が cons なら従来通り分割、非cons なら「静的照合失敗＝dead」として degenerate な
  ('S.nil) 分割（クラッシュ回避）。cons 入力時の挙動は不変＝既存 av-algebra 16 件 green 維持、
  新規 `uncons static non-cons -> degenerate`（av-algebra 17件目）green、hygiene ON green。
- **第2ブロッカ（次の深い課題）**：AV-UNCONS 安全化後、fp2 は SPEC-STEP-AV の **静的 `^=` 処理**で
  `'error <= '10`（spec_av.rwhile L813）に到達。＝抽象ストアが「var は静的に値 A を持つ」と分類して
  いるのに本体が別値 B を XOR-assign する（正しい実行ではあり得ない rupdate-different）状況。
  **抽象ストアの静的値追跡が spec_av の `^=` 列で実体とズレる**（plan 5.6 の「抽象ストアが古くなる」
  問題の自己適用版）。これが fp2 の次の本丸。**注意**：degenerate uncons はライブ経路では誤りを
  隠しうる（dead 経路前提）。fp2 を詰めるとき要再検討。

## 5.9 fp2 次ブロッカの精密特定（2026-06-16）= 動的分岐内の変数が動的化されない

診断（/tmp の diag コピーで AV-UNCONS 非cons枝に distinct marker '77 → fp2 が '77 に到達）で確定：
- **非cons AV-UNCONS はライブ経路で発火**（dead ではない）。`show V` で **V=nil**＝静的 nil の
  cons-split が live で起きている。
- 層の解釈：外側 spec_av は **内側 spec_av の本体**を SPEC-CMD-AV（ri_min は静的データとして流れる
  だけ）。内側 spec_av の本体は**動的条件/ループ**（制御が内側の動的 Src に依存）を含む。外側が
  その動的分岐を residualize する際、分岐内の演算も処理するが、その abstract path で ('S.nil) の
  変数に対し `cons A B <= X` を**静的（degenerate）分割**してしまう（本来は動的に residualize すべき）。
- **＝可逆言語オンライン PE の自己適用核心問題**：spec_av は**動的条件/ループ分岐内の変数を
  動的化しない**ため、静的 nil 値が動的であるべき分岐へ漏れ、degenerate split → 抽象ストア drift
  → `'error <= '10`。memory の「spec が self-applicable でない」詰まりの実体。
- **次の本丸**：spec_av の 'cond/'loop 動的経路で、分岐が触る変数を動的化（dynamicize）する処理。
  大規模・高リスク（fp1 green を壊さないこと）。多セッション規模。
- 注：degenerate uncons はこの dead-ish 経路を非crashで通すが、ライブ動的分岐では正しくない
  （動的 residualize が正解）。fp2 を詰める際にここを設計し直す。

## 6. fp1 完遂後（保留の fp2/fp3 へ）
- **Stage D（fp2）**: `comp = [spec_av]((spec_av . ri_fp3))`、`[comp](src)=comp_src` を検証。
  spec_av の**自己適用**が要点（Stage B で AV/名前付きストア化したのはこのため）。`second-projection` 群新設。
- **Stage E（fp3）**: `cogen = [spec_av]((spec_av . spec_av))`、`[[cogen](ri_fp3)](src)=comp_src`。`third-projection` 群新設。

## 6.1 fp2 (ii) 着手：動的分岐の店内動的化（2026-06-16）
- **DYNAMICIZE-ALL(Vl, RCode)** 実装＋単体テスト（assemble-fp1 #11）：全 slot を動的自己参照に、
  静的非nil/部分静的は materialize（`var k <= lift` を RCode 先頭へ＝残余の動的領域より前に実行）。
  commit `ad51193`。
- **動的 'cond/'loop に配線**（commit `090e9ae`）：従来は分岐/本体を verbatim 残余化しつつ
  抽象ストアを据え置く**不健全**だった（分岐が書く変数の静的値が陳腐化）。配線で健全化。
  spec-av-step の cond/loop dynamic テストを動的化後ストアに更新。全 spec_av 群 green、
  fp1(ri_min/ri_seq) は静的ディスパッチで動的経路に来ないため不変。
- **fp2 はまだ通らない（次ブロッカを精密特定）**：自己適用は依然 `'error <= '10`
  （SPEC-STEP-AV 静的 `^=`、L813近辺）に到達。これは動的分岐とは**別系統の drift**＝
  **'ass コピー/クリアの陳腐化**：LOOKUP/AUX の `X ^= V[J]` コピーが抽象ストアに clear として
  反映されず、ある変数が実行時 nil なのに抽象上は値を保持→静的 `^=` が別値書込みと判定。
  → 次の手：'ass（特に X^=V[J] コピーと逆クリア）の抽象ストア更新を対称化する（コピー時に
  ソース slot を保持しつつ、対応する逆クリアを抽象上も clear と認識）。plan 5.7「alias は lift を
  壊す」の知見と両立させる必要あり（alias 不可）。

## 6.2 fp2 '10 ブロッカの精密診断（2026-06-16, (1)着手）
- 計装で確定：**'10 到達前に DYNBRANCH（動的 cond/loop の residualize）は 0 回**。
  ＝この '10 は 6.1 の動的分岐修正とは**直交**（より手前、純静的寄りの処理で起きる）。
- '10 の値（show で採取）：**K=13（unary）、slot[13]=VAVx=(('var.15).('var.15))（プログラム断片）、
  代入値 VRE=('C . …)（AV データ）**。slot[13]≠nil かつ ≠VRE かつ VRE≠nil → 静的 `^=` が
  rupdate-different と判定。
- 解釈：外側 spec_av が内側 spec_av の AV 操作コードを処理する中で、変数13の slot が
  **陳腐化**（実行時 nil なのに抽象上はプログラム断片を保持）。動的 'ass/'rep の no-alias
  残余化（slot を ('D.('var.k)) 自己参照に）と、その後のクリア追跡の非対称が疑わしい
  （plan 5.7「clear を認識せず古くなる／alias は lift を壊す」の系統）。
- **次の手**：p2d index 13 を spec_av の変数名へ対応づけ（varProgram 順）、その変数の
  生成/消費（コピー/クリア）ライフサイクルを追って陳腐化点を特定する。alias 不可の制約下で
  クリアを追跡する設計（例：消費時に slot を ('S.nil) でなく「動的だが nil 既知」マークにする等）
  が要る可能性。多セッション規模・高リスク。
- 現状の健全な成果（commit 済・green）：DYNAMICIZE-ALL＋動的cond/loop配線（6.1）。
  fp2 green には至らず（独立ブロッカ複数）。

## 6.3 fp2 '10 の接地（2026-06-16, ground-truth 再採取）
- **再現確認**：`./src/ri /tmp/spec_av_bigN.rwhile /tmp/fp2_in.val` → 依然 `'10`（150s 内停止）。
  `fp2_in.val` の内側 p2d = 現 spec_av（先頭200B一致）。
- **変数同定ツール** `src/dump_vars.ml`（expMacProgram→varProgram 順を印字＝p2d 採番）を作成。
  examples 版と bigN 版で var 順は完全一致。**index 13=`Rest`、15=`A'`、11=`U`**。
- **L849 で実測**（`show` 計装）：失敗コマンドは Tag=`'ass`、`K=13`(unary 確定)。
  - `VAVx`（slot[13] の static 値）= **`(('var.15).('var.15))` = 断片 `(A' . A')`**（'S タグ付き）。
  - `VRE`（代入される AV）= **`('C . …)`**＝部分静的 cons、中に `('val.'S)/('val.'D)/('val.'var)`
    リテラルを含む＝**残余コード構築中**の値。
- **判明した矛盾と再フレーム**：展開ソースに `Rest ^= …`（'ass）は**存在しない**（Rest は
  `cons Elem Rest <= Vl`／逆の 'rep でのみ 58+58 回出現）。p2d 中の `('ass.((var13).(var11)))`
  substring は spec_av が 'ass/'var 木を**リテラル値**として扱うコード片の偽陽性。
  → よって `'10` は「Rest への直接代入の rupdate-different」ではなく、**抽象スロット13 が
  プログラム断片 `(A'.A')` を static 値として保持したまま陳腐化**し、その状態で（残余コード構築の）
  `^=` が走って toggle 不整合になっている。**陳腐化値が "store データ" ではなく "プログラム断片"**
  である点が新発見＝plan 6.2 の「'ass コピー/クリア」より、**A'（AV-LIFT のループ変数, L140-143）
  絡みで slot13 に焼き付いた断片がクリアされない**系統を示唆。
- **次の手（多セッション）**：slot[13] が `(A'.A')` になった時点を全実行トレースで特定する
  （`show` をフックして slot[13] 遷移を記録）。A'＝AV-LIFT のループ局所が、自己適用下で
  Rest(13) と**非衛生な名前衝突**を起こしている疑い（CLAUDE.md「hygiene-clean」化の盲点）。
  `RWHILE_HYGIENIC=1`/`-hygienic-macros` 下で fp2 を回して挙動が変わるか確認するのが安価な次手。

### 6.3.1 衛生仮説の検証と**否定**（2026-06-16, 同セッション）
- 衛生展開で spec_av の変数は 213→**932**（`dump_vars_hy`）。内側 p2d は 3.1MB→19.3MB。
- **-hygienic-macros + N=250** → `'10` ではなく `cons U-472 Vl <= Vl against nil`（AUX 店尾踏み抜き）。
  当初これを「`'10` 消滅」と誤読したが、実体は **N 不足で `'10` 到達前にクラッシュしていただけ**。
- **-hygienic-macros + N=1000**（FpN リテラルを 1000 nil に置換, `/tmp/spec_av_N1000.rwhile`）
  → **`'10` 再出現**。
- **結論（仮説の訂正）**：`'10` は hygiene ON/OFF の**両方で**（十分な店サイズで）再現する。
  ⇒ **マクロローカルの名前衝突ではない**。spec_av の **AV 特殊化ロジック自体の抽象ストア陳腐化**
  （ある slot が部分静的プログラム断片 `(A'.A')` を 'S 保持したまま、残余構築の `^=` が走る）。
- **修正の方向（訂正後）**：hygiene は無関係。直すべきは **'rep/'ass の抽象ストア更新**——
  具体的には「slot がプログラム断片を static 保持→次の reversible `^=`（toggle）前に clear されない」
  経路。A'（AV-LIFT ループ, L140-143）が slot に断片を残す箇所、または PAT-WRITE 系が
  消費後に ('S.nil) でなく断片を残す箇所を、全実行 slot トレースで特定する（多セッション）。
- **衛生版での計装確認**（-hygienic-macros + N=1000, `/tmp/spec_av_N1000_diag.rwhile`）：
  失敗は依然 **K=13**（unary 14 nils）、**VAVx=`(('var.21).('var.21))`**＝**同型の `(VarX.VarX)` 断片**
  （X だけ採番違い 15→21）。⇒ hygiene 非依存・**同一構造のバグ**を確証。
  距離的特徴：**陳腐化値は常に `(VarX . VarX)`**（同一変数参照の二重 cons）＝残余コード／部分入力
  setup 由来の断片が static slot に焼き付く。修正は「この `(VarX.VarX)` を生む経路の特定」に帰着。

### 6.3.2 **根本原因の確定（2026-06-16, off-by-one 訂正後）**
- **重要な訂正**：6.2/6.3 の index は **off-by-one で誤り**だった。`conss` は `[v]→v`（L8）なので
  index n の encoding は **n 個の nil**（n+1 ではない）。よって dump_position = index = nil 個数。
  正しい復号：
  - 失敗コマンド target **K=14 = `AsAV`**（×`Rest`13）、RHS **E=12 = `Elem`**。
    ＝ **`AsAV ^= Elem`**（`LOOKUP(Vl,J,X)` 展開の `X ^= Elem`、非破壊読みのコピー）。
  - 陳腐化値 **VAVx=(('var.16).('var.17)) = `(LfTag . LfPay)`**＝**AV-LIFT-STEP の内部局所**
    （L146-174）の参照断片（×`(A'.A')`）。
- **根本原因（特定）**：失敗箇所は inner `ASSEMBLE-FP1`（L259-262）の **lift-then-clear イディオム**：
  ```
  LOOKUP(Vl, J', AsAV);   (* 1回目: AsAV ^= Elem → AsAV = slot[J'] *)
  AV-LIFT(AsAV, AsCode);  (* AsAV を lift（本来 AsAV 保存）*)
  LOOKUP(Vl, J', AsAV);   (* 2回目: AsAV ^= Elem → クリアのはず *)
  ```
  計装（slot トレース + 'ass RHS dump）で `AsAV ^= Elem` が **ちょうど2回**処理され（2発の LOOKUP）、
  **2発目の clear で '10**。AsAV の抽象 AV が、間の **`AV-LIFT(AsAV)` の抽象特殊化で drift**し、
  slot[J'] に復元されず **AV-LIFT-STEP の内部変数 `(LfTag.LfPay)` を保持**したまま →
  2発目の `AsAV ^= Elem` で「AsAV の AV ≠ Elem の AV」となり rupdate-different。
  ＝plan 6.2 の「X^=V[J] コピー」仮説は**当たり**だが、犯人は **AV-LIFT が入力変数 AsAV の抽象 slot を
  保存しない**点。「抽象 store が古くなる」の実体＝AV-LIFT の非保存性。
- **修正方向（次セッション・要 core 変更）**：(a) AV-LIFT の抽象処理を入力変数保存にする
  （lift 中の AsAV slot を最後に元 AV へ復元）、または (b) ASSEMBLE-FP1 の clear を Elem 再読みに
  依存させず AsAV を直接クリア（lift 後に `AsAV` を slot 由来でなく自前で消す）。
  まず単体テスト：`AV-LIFT(X,_)` 後に X の抽象 slot が不変か（spec-av-step 群に lift-preserve テスト追加）。

### 6.3.3 修正の試行と教訓（2026-06-17）
- **C 層で必要十分条件を証明**（`proofs/agda/RWhileRevProj2Lift.agda`, --safe）：spec_av の可逆 XOR
  代入の `'10` 判定と ASSEMBLE-FP1 の lift-then-clear をモデル化し、**idiom が round-trip するのは
  lift が演算対象を保存するとき、かつそのときに限る**（`idiom-ok`/`idiom-drift`）。実観測の drift
  `(LfTag.LfPay)` で `'10` を再現（`bug-reproduces-'10`）。
- **単体テスト追加**（av-algebra 4件, suite 162 OK）：AV-LIFT が入力 AV を保存することを pin。
- **試行①（自己クリア, REVERTED）**：ASSEMBLE-FP1 の2発目 clear `LOOKUP(Vl,J',AsAV)` を
  `AsAV ^= AsAV`（自己 XOR）に置換。結果：**fp1 は 162 OK 維持、fp2 は `'10` 消滅・完走**したが、
  **生成 compiler が壊れていた**（1110B と退化、`[ri.rwhile]((compiler.'swap))` で
  `error in update: var=Vl`）。＝自己クリアは drift チェックを**迂回**するだけで、AV-LIFT が壊した
  AsCode/抽象ストアは不正なまま → **偽の修正**。`'10`（ラウドな失敗）の方が安全なので revert。
  この教訓を Agda に定理化：`selfClear-masks`（自己クリアは任意の le で成功＝drift に鈍感）。
- **確定した次手**：真の修正は **AV-LIFT の抽象特殊化が AsAV の slot を実際に保存する**こと
  （`fix-roundtrips` = lift 保存で全出力 round-trip）。チェック迂回ではなく保存性の回復。
  具体的には spec_av の AV-LIFT 展開コマンド列を OUTER が特殊化する際、worklist round-trip
  （`A <= cons A nil` … `cons A nil <= A'`）が部分静的 AsAV で抽象保存されるよう直す。高リスク・要集中。

### 6.3.4 高速再現の試みと判明した制約（2026-06-17）
- 反復用に**最小再現**を試作：AV-LIFT+AV-LIFT-STEP だけの小プログラム `/tmp/tiny_lift.rwhile`
  を OUTER spec_av で特殊化（`(tiny_lift_p2d . 'a)`）。**具体実行は In 保存で正常**だが、
  OUTER 特殊化で **`'41`**（≠'10）＝AV-LIFT のループ**出口テストが動的化**（L994, 'lcheck の
  LpF 動的）に到達。
- **判明**：drift は **AsAV の形に敏感**。実 fp2 では AsAV（ri_min-fp1 出力 AV）の形が AV-LIFT の
  ループを**静的**に保ち '10 になるが、generic な部分静的入力ではループが**動的化**して '41 になる。
  ＝最小再現では実 '10 を忠実再現できず、**忠実な反復ループは 120s の実 fp2 のみ**。
- **副産物の知見**：AV-LIFT のループ制御は部分静的オペランド一般に脆い（静的/動的の境界次第で
  '10 か '41）。真の修正は AV-LIFT を**部分静的入力に対してロバストな静的処理＋抽象保存**に
  作り直す必要があり、AsAV 限定の小手先では不十分。
- **現実的評価**：本修正は SPEC-STEP-AV の静的ループ unroll＋worklist 抽象追跡の作り直しで、
  忠実な fast test が無い以上 120s ループでの集中作業が要る。green 状態（162 OK）を壊すリスクが
  高く、専用セッション推奨。今セッションの確定成果＝C層で必要十分条件＋偽修正排除＋再現制約の特定。

### 6.3.5 clear 側修正の**全面的排除**（2026-06-17, 決定的）
2種類の clear 側修正を実機 fp2 で検証（どちらも fp1 は 162 OK 維持）：
- **試行②: 自己クリア** `AsAV ^= AsAV` → fp2 完走だが compiler 壊れ（`error in update: var=Vl`）。
- **試行③: 分解クリア（DYNAMICIZE-ALL 型）** `cons AsOt AsOv <= AsAV; AsOt^=AsOt; AsOv^=AsOv`
  → fp2 完走だが **同じ** `error in update: var=Vl`。compiler は 1158B と退化。
- **決定的結論**：clear 方法（re-read / 自己 / 分解）に**関係なく**、fp2 完走時の compiler は壊れる。
  ＝`'10` は症状であり、**真因は AV-LIFT が特殊化で誤った AsCode を生む（＋全体が過剰静的に退化、
  cf. 5.9 の「動的分岐内変数を動的化しない」）**。**clear 側のいかなる修正も不可**と確定。
  両試行とも revert（spec_av は無変更を維持）。
- **fp2 に必要な真の作業（確定）**：
  1. AV-LIFT の抽象特殊化が部分静的入力で**正しい AsCode を生成**し AsAV を保存する（worklist
     unroll の値追跡の作り直し）。
  2. 5.9 の過剰静的問題（動的依存の変数/分岐を確実に動的化）の解消。
  これらは SPEC-STEP-AV / AV-LIFT の中核改修で、忠実 fast test 不在のため 120s ループでの
  専用セッションが必須。clear 側の小手先は全滅と判明したので、次は (1)(2) に直接取り組む。

### 6.3.6 **真の根本＝束縛時刻（binding-time）の静的コミット**（2026-06-17, 決定的）
clear 側全滅を受け上流を精査して根本に到達：spec_av の main（L1051）が partial-input を
```
FpPart <= cons 'C (cons (cons 'S Src) (cons 'D (cons 'var FpIc)));
```
で組み、**`Src` を `'S`（静的）で固定タグ**する。＝「Src は静的」という**束縛時刻の前提を静的に
コミット**している。
- **fp1**：Src は実際に静的（'swap 等）→ 正しい。
- **fp2 = [spec_av]((spec_av . ri_min))**：OUTER から見て inner の `Src`(=d) は**動的**。なのに inner
  コードは `cons 'S Src` で**動的値を 'S 固定タグ**。OUTER は `cons 'S(静的) Src(動的)` を部分静的 'C に
  展開するが、inner の後続は「FpPart=('C.(('S.Src)...))」のクリーン 'S を前提に pattern-match/処理 →
  束縛時刻の不整合が連鎖 → **過剰静的退化（compiler 1158B）＋ AV-LIFT '10 等は全て下流症状**。
- **結論（最重要）**：fp2 が通らない真因は AV-LIFT でも clear でもなく、**spec_av 自身が「自分の
  静的入力 Src は本当に静的」と仮定して書かれている**こと。自己適用では Src が動的になり仮定が崩れる。
  ＝Futamura/Jones の「spec が self-applicable であるための束縛時刻分離（BTA / 二段階化）」が
  未達。**局所修正では直らない**（AV-LIFT/clear はいずれも下流）。
- **正しい道（研究方針と整合）**：spec_av を BTA 済み・自己適用可能な形に書き直す。規模が大きいので
  メモリの研究方針通り、**小さな自己適用可能 specializer コアを R-CORE で設計→意味保存翻訳で橋渡し**
  が現実的（[[research-direction-core-language]]）。本番 spec_av の直接改修は高リスク・大規模。
- 今セッションの確定成果：fp2 不通の真因を **AV-LIFT の '10（症状）→ AV-LIFT 特殊化（中間）→
  束縛時刻の静的コミット（根本）** まで掘り下げ、clear 側修正を全面排除。次は小コアでの
  self-applicable specializer 設計が本筋。

### 6.3.7 本番 spec_av 移植のブループリント（2026-06-17, 証明裏打ち）
C層の証明が揃った（`RWhileRevProj2BT`=真因+修正仕様、`RWhileRevProj2Self`=BT-aware で fp2 が
本物の残余で通る構成的実現）。これを本番へ移す際の**精密な見立て**：

**(A) なぜ一行修正では済まないか**
- L1051 `cons 'S Src` は「自分の静的入力 Src は静的」と仮定。fp1 は Src=生の静的値で正しい。
- fp2 では内側 spec_av の Src=動的値 d。**spec_av は値だけから Src の束縛時刻を判別できない**
  （'swap も d も「ただの値」）。＝Jones の「naive specializer は self-applicable でない」。
- 修正には spec_av が**束縛時刻情報（BT division / 注釈付き入力）を受け取る**必要＝**インターフェイス
  含む再設計**。`RWhileRevProj2Self` の op-list 設計は本番（AV ストア＋汎用プログラム）と別物で
  そのまま移植不可。

**(B) 移植の選択肢**
1. **二段階化（推奨, 研究方針と整合）**：spec_av を「BT-注釈付き入力を取る」版に。入力を
   `(Prog . (BT . Src))` 等にし、L1051 を `mkAV BT Src`（BT=static→('S.Src), dynamic→('D.var)）に。
   fp1 呼び出しは BT=static を渡す（既存テスト互換のラッパ）。fp2 では外側が内側へ渡す BT が
   dynamic になり、'S 固定の嘘が消える。`RWhileRevProj2BT.mkAV` がこの関数の仕様。
2. **意味保存翻訳で橋渡し**：`RWhileRevProj2Self` の小コア specializer を R-WHILE へ翻訳し、
   翻訳の意味保存（[[RWhileElabCom]]/[[RWhileCoreExp]] 系）で本番相当の性質を移送。本番 spec_av は
   直接いじらず、小コア版を「正」とする住み分け。

**(C) 検証計画（移植時）**
- 不変条件：全 spec_av 群＋fp1(ri_min/ri_seq) が green を維持（162 OK）。BT=static 経路が
  既存 fp1 と一致することをまず確認（`fp1-ok` の実機版）。
- fp2 進捗：`[spec_av]((spec_av . ri_min))` で '10 が消え、生成 compiler が **runtime 入力を使う**
  （`compiler-residual-uses-input` の実機版：`[[compiler]('swap)](('a.'b)) = ('swap.('b.'a))`）。
  ＝今回 clear 側修正で出た「壊れた compiler」ではなく正しい compiler。
- 反復：忠実 fast test 不在のため 120s ループ。BT=static ラッパで fp1 を高速回帰しつつ、fp2 は
  バックグラウンドで。

**(D) リスク・規模**：spec_av の入力契約変更＋partial-input 構築＋（場合により）AV 処理の二段階化。
複数セッション規模・高リスク（green 厳守）。ただし**設計仕様（B層が満たすべき定理）と構成的実現
（小コアで fp2 が通る）は Agda で確定済み**なので、迷いなく着手できる。今セッションはここまでで
安全に区切るのが妥当（本番改修は専用セッション）。
