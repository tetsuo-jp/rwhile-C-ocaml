# spec.rwhile reverse テスト修正の検討メモ

作成日: 2026-03-19

## 問題

`test_spec_first_projection_ri_reverse` テストが失敗している。

このテストは「第1フタムラ射影」を検証する：
- `spec(reverse_program, ('a.'b.'c.nil))` を実行
- 残留プログラム P_res を取り出す
- P_res を nil に適用すると `('c.('b.('a.nil)))` が得られるはず

## 問題1: テストが間違ったファイルを使っている

**TestSuite.ml の行 639:**
```ocaml
let spec_input = parse_file_val (examples_dir ^ "/ri_ri_reverse_list123.p_val") in
```

- `ri_ri_reverse_list123.p_val` (957KB) → P=ri.rwhile自身、S=(reverse_data, '1.'2.'3.nil)
  - これは第2フタムラ射影用（より深い特殊化）
  - 期待値の 'a,'b,'c とリスト要素の '1,'2,'3 が不一致

- 正しいファイル: `reverse_and_list123.p_val` (427バイト) → P=reverseプログラム、S=('a.'b.'c.nil)

**修正1**: TestSuite.ml 行639を `reverse_and_list123.p_val` に変更

## 問題2: spec.rwhile が reverse ループを静的に展開できない

`reverse_and_list123.p_val` の内容（解読済み）:
```
P = ('var.nil) ... ('var.(nil.nil.nil))
    read変数 = var[0] (= Y)
    write変数 = var[2] (= X)
S = ('a.('b.('c.nil)))
```

reverseプログラムのループ: `from (=? X nil) loop ... until (=? Y nil)`

- ループ入り条件 e = `=? X nil` … X は write変数 = var[2]
- spec.rwhile の Vl 初期化:
  - Vl[var[0]] (Y) = static(S) = `((nil.nil).S)` ← read変数のみ静的設定
  - Vl[他] = `(nil.nil)` = dynamic ← X, Z は全部動的

- SPEC-EXP で `=? X nil` を評価 → X が dynamic → 結果 = dynamic
- → ループが残留化（residualize）されてしまう

**結果**: 残留プログラムが元のreverseプログラムそのままになる。
これを ri.rwhile で nil に適用すると、nil を (cons Z Y) パターンに当てようとして
`impossible happened in inv_evalPat.PCons, pattern: cons V1 V2, term: nil` エラー。

## 問題2の根本原因

R-WHILE の可逆性条件（store invariant）：
> 全変数は実行開始時も終了時も nil でなければならない（read変数とwrite変数を除く）

つまり X (write変数) も実行開始時は nil であることが保証されている。
しかし spec.rwhile は read変数のみ static に初期化し、write変数を含む他の全変数を dynamic に初期化している。これは情報の無駄。

**修正2**: write変数 Vl[J'] も static(nil) として初期化する

## 修正2の詳細

### Vl の初期化（lines 615-621 付近）

現行:
```rwhile
(* Set read variable to static *)
LOOKUP(Vl, I', SV);
UPDATE(Vl, I', SV);
SV ^= SV;
SV ^= cons (nil.nil) S;
UPDATE(Vl, I', SV);
LOOKUP(Vl, I', SV);
```

追加すべきコード（write変数を static(nil) に設定）:
```rwhile
(* Set write variable to static(nil) *)
LOOKUP(Vl, J', SV);
UPDATE(Vl, J', SV);
SV ^= SV;
SV ^= cons (nil.nil) nil;   (* static(nil) = ((nil.nil).nil) *)
UPDATE(Vl, J', SV);
LOOKUP(Vl, J', SV);
```

### Vl のクリーンアップ（lines 651-659 付近）

現行: Vl[I'] のみ (nil.nil) に戻してから大きな XOR でクリア

追加すべき: Vl[J'] も明示的にクリアしてから (nil.nil) に戻す

現行のクリーンアップパターン:
```rwhile
LOOKUP(Vl, I', SV);
UPDATE(Vl, I', SV);   (* Vl[I'] → nil *)
SV ^= SV;
SV ^= (nil.nil);
UPDATE(Vl, I', SV);   (* Vl[I'] = (nil.nil) *)
SV ^= (nil.nil);
Vl ^= ((nil.nil)...100エントリ...);  (* 全部 XOR で nil に *)
```

追加:
```rwhile
(* J' も (nil.nil) に戻す *)
LOOKUP(Vl, J', SV);
UPDATE(Vl, J', SV);   (* Vl[J'] → nil; 現在 static(result) かもしれない *)
SV ^= SV;
SV ^= (nil.nil);
UPDATE(Vl, J', SV);   (* Vl[J'] = (nil.nil) *)
SV ^= (nil.nil);
```

## 問題3: PAT-WRITE-LEAF が static(nil) を受け付けない

現行の PAT-WRITE-LEAF（lines 309-322）:
```rwhile
macro PAT-WRITE-LEAF(PP, PV)
  if =? (hd PP) 'var then
    cons PWLtg PWLag <= PP;
    PWLsv ^= (nil.nil);           (* PWLsv = (nil.nil) *)
    UPDATE(Vl, PWLag, PWLsv);    (* Vl[k] ^= (nil.nil): Vl[k]=(nil.nil)→nil *)
    PWLsv ^= (nil.nil);           (* PWLsv = nil *)
    PWLsv ^= (nil.nil);           (* PWLsv = (nil.nil) [冗長だが可逆性のため] *)
    PWLsv <= cons PWLsv PV;      (* PWLsv = ((nil.nil).PV) *)
    UPDATE(Vl, PWLag, PWLsv);   (* Vl[k] = ((nil.nil).PV) *)
    PWLsv ^= PWLsv;              (* clear *)
    PP <= cons PWLtg PWLag
  ...
```

**前提条件**: Vl[k] = (nil.nil) でなければ動かない
- Vl[k] = (nil.nil): UPDATE で nil に → OK
- Vl[k] = static(nil) = ((nil.nil).nil): `((nil.nil).nil) ^= (nil.nil)` → ERROR（異なる非nil値）

**修正3**: LOOKUP+UPDATE パターンで Vl[k] を任意の値からクリアする:
```rwhile
macro PAT-WRITE-LEAF(PP, PV)
  if =? (hd PP) 'var then
    cons PWLtg PWLag <= PP;
    LOOKUP(Vl, PWLag, PWLsv);    (* PWLsv = Vl[k] (現在値) *)
    UPDATE(Vl, PWLag, PWLsv);   (* Vl[k] ^= PWLsv → Vl[k] = nil *)
    PWLsv ^= PWLsv;              (* PWLsv = nil *)
    PWLsv ^= (nil.nil);          (* PWLsv = (nil.nil) *)
    PWLsv <= cons PWLsv PV;     (* PWLsv = ((nil.nil).PV) *)
    UPDATE(Vl, PWLag, PWLsv);   (* Vl[k] = ((nil.nil).PV) *)
    PWLsv ^= PWLsv;              (* clear *)
    PP <= cons PWLtg PWLag
  ...
```

## 問題4: ループ再入時の entry test チェック

spec.rwhile の 'l1E ハンドラは entry test が false の場合エラーを出す:
```rwhile
if ValE2 then
  (* True: enter do-branch *) ...
else
  (* False entry: error *)
  'error <= '20
fi ValE2
```

しかし 'l4E から戻ってきた2回目以降の 'l1E では、
R-WHILE のループ意味論では entry test は false（`assert e = false`）でなければならない。

現行実装では 'l1E が2回以上呼ばれる場合を考慮していない可能性がある。

**要調査**: 'l4E → 'l1B → 'l1E の流れで、2回目の entry test が false になるとエラーになるか？

`reverse_and_list123.p_val` を使った場合、X は:
- 初回 'l1E: X = static(nil) → `=? nil nil` = true → OK (ループに入る)
- do-branch: doNothing (BDoNone → doNothing = `'ass ('var.nil) ('val.nil)`)
- 1回目のループ本体実行後: X = static(('a.nil))
- 2回目 'l1E: X = static(('a.nil)) → `=? ('a.nil) nil` = false → `'error <= '20`

→ **'l1E でエラーになる可能性がある**。要確認・修正。

## 検討中の追加修正

spec.rwhile のループ処理において、'l4E からの再入を「アサーション」として扱い、
entry test が false のときはエラーにせず通過する修正が必要かもしれない。

例えば 'l1E に「再入フラグ」を渡す方法:
- 初回: W = nil (エラーチェック有効)
- 再入: W = (nil.nil) (アサーションモード: false で OK、true でエラー)

ただしこれは 'l4E を修正して W に非nil値をセットする必要がある。

## まとめ: 必要な修正リスト

| # | ファイル | 変更内容 |
|---|---------|---------|
| 1 | TestSuite.ml (行639) | `ri_ri_reverse_list123.p_val` → `reverse_and_list123.p_val` |
| 2 | spec.rwhile (行615-621後) | write変数 J' も static(nil) に初期化するコードを追加 |
| 3 | spec.rwhile (行651-659) | Vl[J'] のクリーンアップを追加 |
| 4 | spec.rwhile PAT-WRITE-LEAF | LOOKUP+UPDATE パターンで Vl[k] を任意値からクリア |
| 5 | spec.rwhile 'l1E ハンドラ | 2回目以降（'l4E から再入）の entry test = false をエラーにしない |

修正5については詳細な設計が必要。現行の 'l4E が `(cons 'l1E (cons nil Arg))` を push しているので、W=nil を W=(nil.nil) に変更することで区別できる。

## 未解決の疑問

1. `doNothing = ('ass . (('var.nil) . ('val.nil)))` という形のコマンドが spec.rwhile で 'ass タグとして処理されるとき、どう評価されるか？
   - K = nil (var 0 = Y = read変数)、E = ('val.nil)
   - Y が static(S) の状態でこれを評価すると、Y の値が更新される？
   - SPEC-EXP('val.nil) = static(nil)
   - LOOKUP(Vl, nil, SV): SV = Vl[Y]... Y は var 0 = ('var.nil) で index = nil
   - つまり doNothing の `('var.nil)` は var[0] を指す = Y の変数を指す！？
   - これは問題かもしれない

2. reverseプログラムの変数番号付け: Program2DataRwhile.ml が `varProgram` の順で番号を振る
   - Y (read) = var[0]、Z (中間) = var[1]、X (write) = var[2] の順序確認が必要

3. 'l4E から 'l1E への再入フローの正確なトレース

## 次のステップ

1. まず修正1（テストファイル変更）だけ適用してビルド＆テスト → どんなエラーが出るか確認
2. 修正4（PAT-WRITE-LEAF）は比較的安全な変更なので先に適用
3. 修正2＋3（write変数初期化＆クリーンアップ）を適用
4. 修正5（'l1E 再入処理）を設計＆適用
5. 全テストが通ることを確認（既存の75テストが壊れないこと）
