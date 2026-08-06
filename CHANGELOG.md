# Changelog

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
