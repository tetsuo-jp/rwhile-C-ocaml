# Changelog

## [Unreleased] - 2026-08-09

### 可逆版 Jones 最適性の測定（ロードマップ④「最適性」）

- **`Simp.program_preserving`**：プログラム保存版 p⁺（`[p⁺](d) = (p2d p . [p](d))`）を作る変換。
  可逆射影はプログラム保存インタプリタを要求するので、Jones 最適性の比較対象は p ではなく
  **同じ義務を持つ最小のプログラム** p⁺ である、という基準の可逆版を実装したもの。
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
