# Changelog

## [Unreleased] - 2026-08-09

### 可逆版 Jones 最適性の測定（ロードマップ④「最適性」）

- **`Simp.program_preserving`**：プログラム保存版 p⁺（`[p⁺](d) = (p2d p . [p](d))`）を作る変換。
  可逆射影はプログラム保存インタプリタを要求するので、Jones 最適性の比較対象は p ではなく
  **同じ義務を果たす p の最小の拡張** p⁺ である、という基準の可逆版を実装したもの。
- **`./measure_proj jones-self`**：自己インタプリタ `ri_fp3.rwhile` に対する fp1 残余を
  直接実行・p⁺・自己解釈と、`-steps`／`-work` の両指標で比べる表。
- **結果**：work では 7 被験すべてで `残余 ≤ p⁺`（可逆版 Jones 最適性が成立）、
  steps では `id` を除き 1.4〜5.0× で不成立。解釈のオーバヘッド自体は自己解釈の 1/10〜1/30。
  コピー伝播（`Simp.copyprop_program`）が効かせている。
- **テスト群 `jones-self`（5 件）**：下敷きの妥当性（3 者一致＋p⁺ の可逆性）、work 側の最適性、
  steps 側の非最適性（改善したら落ちる pin）、解釈層の除去、コピー伝播の必要性。
  テスト総数 263 → 268 件。
- ドキュメント：`RWHILE_S.md`「判明したこと 3」、`FINDINGS_reversible_projections.md`、
  `RESEARCH_ROADMAP.md` ④。

### 被験をループ込みへ拡大し、壁の正体を特定（同日）

- **申し送り「ループ被験は fp1-via-ri_fp3 が未対応」は誤りだった。壁は動的制御。**
  ループ被験 `loop_static2/3` は通り、`ri_fp3` は `reverse` を正しく自己解釈する。
  **ループを含まない** `dyncond3.rwhile`（動的分岐のみ）が同じ `'error <= '41` で落ちることが決め手。
  破綻箇所は `examples/spec_av.rwhile` の `'lcheck` ハンドラ 1 か所、破れる不変条件は
  「展開を始めたループは脱出条件が静的なままであり続ける」。選択的動的化では解けない。
- **結果**：ループ被験は **steps・work の両指標で `残余 ≤ p⁺` が成立する唯一の例**
  （0.1×／0.91×・0.86×）。反復を増やしても `st_res` は 1 のままなので、直線被験の steps 側の
  不成立は**固定の段取りコスト**であって一般的な劣位ではない。
- `./measure_proj` に `lp_p`／`lp_r` 列（`CLoop` ノード数）と `JONES_EXTRA=a,b,c`（被験の追試）。
  既存被験名は二重に足さない。特殊化に失敗した被験は表を殺さず 1 行で報告する。
- テスト群 `jones-self` +2、**`jones-self-open`（3 件）**が壁を期待される失敗として pin
  （通るようになったら落ちて気づく）。テスト総数 268 → 273 件。
- 新規 `examples/loop_static2.rwhile`・`loop_static3.rwhile`・`dyncond3.rwhile`。
  詳細は `FINDINGS_reversible_projections.md` §10。

### p⁺ の定義側を Agda で機械検証（同日）

- 新規 5 モジュール（すべて `{-# OPTIONS --safe #-}`・**postulate ゼロ**）：
  `RWhileJonesRev`（抽象層の基準）、`RWhileProgPres`（構成と意味論）、
  `RWhileProgPresRev`（可逆性）、`RWhileProgPresMin`（拡張の中での最小性）、
  `RWhileJonesRevCE`（反証）。`./check.sh` は 108 モジュール PASS。
- **証明できたこと**：p⁺ の可逆性（逆も同じコスト `k+8` で往復）、意味論が仕様どおり、
  fp1 残余がプログラム保存の義務を継承すること、古典版 Jones 最適性 ⇒ 可逆版。
- **反証したこと**：「p⁺ は義務を果たす最小のプログラム」は**一般には偽**。
  義務は外延的に関数を固定するが、コストは関数から決まらないため。代わりに
  「**p の拡張の中での**最小性」を証明（下界 `+3`、p⁺ は `+8`、差は常に加法定数）。
  → 和文では「最小の義務」ではなく「**義務を満たす最小の拡張**」と書き分けること。
- **既知の差**：抽象層と具象層は未接続、モデルの定数 8 は実機 `-steps` の 4 と異なる
  （定理が主張しているのは**定数性**であって 8 ではない）、`-work` 指標のコストモデルは未整備。
  対応表は `AGDA_CORRESPONDENCE.md`。

### 投機的展開＋巻き戻しで動的制御の壁を越えた（同日）

- **`'error <= '41` を廃止。** 展開を始めたループの脱出条件が後から動的化する場合に、
  **ループ入口の状態へ巻き戻して**残余化に切り替える。`'loop` ハンドラの「入口が静的に真」の枝で
  投機を始め、`'lcheck` のフレームに `(Vl, RCode, TmpCtr)` を退避する。
  `Cd` は本体の特殊化がスタック平衡なので退避不要。
  **退避が安いのは可逆言語だから**：`^=` は右辺を式として読むので `SpcVl ^= Vl` は消費せずに複製でき、
  フレーム構築（`<=`、右辺はパターン）がその複製を消費する。`spec_av.rwhile` に約 40 行
  （§10.4 の見積もり 50〜100 行に対して）。`spec_av_clean.rwhile` も同期。
- **巻き戻し先が入口である理由**：可逆ループは入口テストを初回に真、以降の戻り辺で偽と表明するので、
  「k 反復目から続ける」を意味する残余ループが書けない（`exit-dynamic-forces-residual`）。
  巻き戻した後は **`DYNAMICIZE-ALL` を先に**やってから**入口テストを再特殊化**する。
  静的に真の入口テストを定数で出すと戻り辺を取れないループ＝非可逆になるため
  （`constEntry-no-iter`。`[inv comp]([comp](d)) = d` の検査で守る）。
- **成果**：データ依存のループが**初めて** work 指標で可逆版 Jones 基準を満たした。

  | 被験 | \|resid\| | wk p⁺ | wk res | Jr(work) |
  |---|---:|---:|---:|---:|
  | `reverse` | 125 | 107 | 18 | **0.17×** |
  | `length` | 2273 | 259 | 37 | **0.14×** |
  | `length2` | 2329 | 318 | 40 | **0.13×** |

  静的制御の被験（0.91×／0.86×）より良い。残余はループを保ち、3 入力で原プログラムと一致し、
  構文的反転で往復する。**同一のベンチを変更前の `spec_av` で回すと 3 被験とも `'41` で落ちる**
  （反証テスト実施済み）。
- **正直な限界**：`ri_fp3` 経由の残余は正しいが巨大（`reverse` 46003 ノード、Jr(work) 17.17×）。
  被験の動的制御がインタプリタの主ループを動的化するため、残余化するとインタプリタの動的核が残る。
  **「越えた」は停止して正しいという意味であって、Jones 最適という意味ではない。**
- **棄却した設計（`FINDINGS_reversible_projections.md` §10.6）**：`INV-SPEC-STEP-AV` による
  `Cd'` 上の逆向き実行は**不可能**で、§10.4 の前提が誤っていた。**`spec_av` は単射ではない**
  （`X ^= X` でゴミを捨てる。`'lcheck` ハンドラ自身が `LpE ^= LpE` 等をしている）。
  厳密な逆向き実行はゴミを埋め込む `spec_av_rev.rwhile` でしか成立しない。
  今回の退避はまさにその埋め込みを**必要な箇所だけ**行うもの（Bennett 流の入力保存）。
  「仕事を捨てる＝逆に走る」という筋書きは `spec_av_rev` を土台にしないと書けない（別プロジェクト）。
- テスト群 `dyn-control`（テストファースト。実装前に 4 件 red でコミット）。
  `jones-self-open` は削除せず、`'41` 状態が**到達不能**であることを pin する形に書き換えた
  （大声の失敗が静かな誤答に化けていないことの検査）。新しい pin
  `OPEN (ri_fp3, not spec_av)`：`ri_fp3` には `ri.rwhile` の `CANON` 修正が入っていないため
  非正準な真値（`'q`）では自己解釈できず、**残余も同じ入力で同じように失敗する**
  （残余が忠実であることの証拠）。テスト総数 273 → **278 件**。
- ゲート：`make run-tests` 278 件緑、`measure_proj full` で
  `[comp2](('S.swap)) == B : true`（fp2 維持）。比 0.963 → 0.967 は
  `|spec_av|` 自身が 415733 → 470385（+13.2%）に増えたため。fp1 残余は不変（swap 59、0.36×）。

### `ri_fp3` に CANON を移植（同日）

- `ri.rwhile` の BUG 1（条件文の脱出表明を**真偽値の一致**ではなく**ビット一致**で消していた）は
  そちらでは `CANON` マクロで直っていたが、`ri_fp3.rwhile` は生の `W ^= Ve` / `Arg ^= Ve` のままだった。
  同じ修正を **`CANON-FP3`** として移植。R-WHILE の条件文は真偽の一致しか要求しないので、
  テストが `'q`、脱出表明が `=? Z 'one` = `(nil.nil)` でも一致しなければならない。
- **効果**：非正準な真値（`'q`）を持つ被験が自己解釈できるようになった。
  `dyncond3` を `ri_fp3` 経由で fp1 した残余も同じ入力で正しく走る。
- **テストの扱い**：バグを pin していた `OPEN (ri_fp3, not spec_av)` は削除せず、
  **「インタプリタと残余が同じ入力で一致する」ことを検査する形に書き換えた**
  （修正前は両方が `error in update` を投げることを検査していた。どちらの状態でも、
  残余がインタプリタと食い違えば落ちる）。`dyncond3` の被験入力にも `'q` を追加。
- **測定への影響はゼロ**：`measure_proj jones-self` の 9 行、`dyncontrol` の 3 行、
  `[comp2](('S.swap)) == B : true` のいずれも変化なし
  （どの被験も条件文を含まないか、comp2 は `ri_min` 経由のため）。テストは 278 件のまま。
- **残る同型の穴**：ループの脱出条件は `ri.rwhile`・`ri_fp3.rwhile` とも生の値で比較している。

### 文献・CI（同日）

- `RELATED_WORK.md` §1.5：Jones 最適性の定義を**原典で確認**（JGS 1993 の 6 章 6.4 節
  Definition 6.4、時間 t で測る）。**JGS 自身が定義は "cheated" されうると明記している**点を
  引き、p⁺ への置き換えが「基準を緩めた」のではなく「同じ義務を負う者どうしを比べる」もので
  あることを表で明示。書誌 6 件を Semantic Scholar／DBLP で裏取り。
- `.github/workflows/ci.yml`：`ri` のビルド → 273 件のテスト → examples の煙試験 →
  測定ツールのビルドと実行 → 逆変換の往復の E2E。

## [Unreleased] - 2026-03-06

### リファクタリング

#### `Subst.ml` の新規作成（置換処理の共通化）
- `MacroRwhile.ml` と `Program2DataRwhile.ml` に完全に重複していた置換関数群を
  共通モジュール `Subst.ml` に抽出
- 対象関数: `substRIdent`, `substVariable`, `substExp`, `substPat`, `substCom`,
  `substThenBranch`, `substElseBranch`, `substDoBranch`, `substLoopBranch`,
  `substMacro`, `substProgram`
- 約70行の重複コードを削除

#### `MacroRwhile.ml`
- 置換関数群を削除し `Subst` モジュールへの呼び出しに置き換え
- Warning 52 修正: `Invalid_argument "List.combine"` → `Invalid_argument _`
  （fragile literal pattern の解消）
- 95行 → 46行

#### `Program2DataRwhile.ml`
- 置換関数群を削除し `Subst` モジュールへの呼び出しに置き換え
- Warning 52 修正: `Failure("int_of_string")` → `int_of_string_opt` + `match`
  （fragile literal pattern の解消）
- 未使用の `transMacro` 関数を削除
- 未使用の変数警告を修正（`CMac (rident, ridents)` → `CMac (_, _)`, `CShow e` → `CShow _`）
- 不要な `rec` を `transRIdent`, `transVariable` から除去
- 135行 → 72行

#### `Makefile`
- ビルド対象に `Subst.ml` を追加
- `test-suite` ターゲットを追加（Alcotest によるユニットテスト）
- `run-tests` ターゲットを追加
- `clean` ターゲットに `test-suite` を追加

### テストスイートの追加と拡張

`TestSuite.ml` は現在 708 行、Alcotest による 75 テスト。

| カテゴリ | テスト数 | テスト内容 |
|---------|---------|-----------|
| store | 10 | insert, rupdate, update, all_cleared |
| eval-exp | 9 | cons, hd, tl, =?, リテラル, 変数, エラーケース |
| var-collect | 2 | プログラム中の変数名収集 |
| inversion | 8 | コマンド反転, マクロ名反転, 二重反転不変性 (inv∘inv = id) |
| substitution | 5 | 識別子・式・コマンド・プログラムの置換 |
| macro | 4 | マクロ展開, 逆マクロ展開, エラーケース (not found, arity mismatch) |
| p2d | 4 | program-to-data 変換, conss ユーティリティ |
| eval-integration | 13 | swap, reverse, if, loop, macro minus, 可逆性検証, エラーケース |
| inv-eval | 2 | 逆プログラムの実行 (swap, reverse) |
| roundtrip | 2 | parse → print → parse の往復一致 |
| spec | 4 | `spec.rwhile` の実行、出力形式、残余プログラムの基本意味保存 |
| file-integration | 12 | examples/ のファイルを使った統合テスト |

### ビルド結果
- コンパイル警告: 0件（リファクタリング前は Warning 52 が2件）
- テスト: 75件全件 OK
