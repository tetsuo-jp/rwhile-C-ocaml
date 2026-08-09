# NIGHTLOG

## 2026-08-10 — 課題 f393cb66bfc1: ri.rwhile BUG 2（自己クリア `X ^= X`）を保存値方式で修正 ＋ `ri-selfclear` 群

### ⚠️ 最重要：この晩は 1 つもコマンドを実行できていない（未検証）

`postulate` は追加していない（Agda には一切触れていない）。だが**それ以上に重い注意**がある：

**この worktree では Bash がシェル組込み（`echo` / `true` / 代入）以外すべて拒否された。**
`make`, `./test-suite`, `./measure_proj`, `git`, `grep`, `rg`, `ls`, `sh -c`, `find`, `runcap` は
いずれも "This command requires approval" で実行できず、非対話セッションのため承認も取れない。
（`rtk` フックが `ls` → `rtk ls` 等に書き換え、その `rtk ...` が許可されていない。`echo` だけは通る。）
したがって以下は**すべて未実行・未検証**：

- `cd src && make run-tests`（コンパイルすら試せていない）
- `./test-suite test ri-selfclear`（今夜の accept_cmd）
- `./measure_proj full`
- `cd proofs/agda && ./check.sh`
- 変異注入プローブ

**掟「沈黙を成功と読まない」に従い、緑だとは書かない。**下の変更は
「読解と手計算だけで組み立てた、コンパイルも実行もしていないパッチ」である。
翌晩の人はまず `cd src && make run-tests` を回すところから始めてほしい。
（ファイル読み書き＝Read/Edit/Write は使えたので、変更自体は入っている。）

### 何を直したか

**症状**：`comp`（spec_av の残余）が直接評価では正しいのに `run_via_ri` 経由だと
`error in update` で落ちる。`run_via_ri` は HANDOFF_fp2.md が fp2 の成功判定に使う経路なので、
正しい残余を「壊れている」と誤報していた。

**真因**（既にソースに特定済だったもの）：`examples/ri.rwhile` の `'ass`

```
EVAL-EXP(E,V,H); DUPDATE(Vl,K,V); INV-EVAL-EXP(E,V,H)
```

`INV-EVAL-EXP` は temp（V と H）を **store を読み直して**消す。ところが直前の `DUPDATE` が
その store を書き換えている。`E` が K 番スロットを読む場合（`X ^= X` など）読み直し値が変わり、
temp が相殺できずに `error in update`。

この方言では `X ^= E` に「X ∉ Vars(E)」の制限がない（`EvalRwhile.evalCom` の `CAss` は
E を**書き込み前の** store で評価するので、`X ^= X` は自己クリアとして意味を持ち、
spec_av はこれを残余に吐く）。だから解釈器側が対応する必要がある。

**修正（保存値方式、`examples/ri.rwhile` `'ass`）**：

```
EVAL-EXP(E,V,H);     (* V := E の値、ゴミは H *)
AssV ^= V;           (* store が変わる前に保存 *)
INV-EVAL-EXP(E,V,H); (* 未変更の store に対して逆算 → 必ず消える *)
DUPDATE(Vl,K,AssV);  (* 更新はここで初めて行う *)
AssV ^= AssV         (* 保存値を捨てる *)
```

`'cond` / `'l1E` / `'l2E` が既に採っている「EVAL-EXP → 保存 → INV-EVAL-EXP」と同じ形にしただけ。
`X ∉ Vars(E)` の通常ケースでは store 効果は従来と完全に同一（値も更新も同じ、順序だけ変わる）。

### 判断の分岐点：ri.rwhile の可逆性を犠牲にした（＝過去に「不採用」とされた道）

HANDOFF_fp2.md §0f には 2026-06-17(7) の結論として
「(b) ri を前方のみ忠実化（可逆性犠牲・ハック、**不採用**）」と書かれていた。今回の修正は
その (b) にあたる。**承知のうえで採った**。理由：

- `X ^= X` は**非単射**（`v → nil`、どの v でも nil）。
- 自己解釈器の計算する関数は被解釈プログラムの関数そのもの。被解釈側が非単射なら、
  それを忠実に解釈する解釈器も非単射でしかありえない。
- ⇒「忠実さ」と「可逆性」はここで両立しない。(b) はハックではなく**強制**である。
  当時の「局所パッチ不可」という結論は、正しくは「可逆なままの局所パッチは不可」。

犠牲の範囲は `AssV ^= AssV` **1 箇所**に局在させた。ri.rwhile は構文的には従来どおり
R-WHILE プログラムのままで、`InvRwhile.invProgram` の対象・`test_file_inverse` の involution も不変。
失われるのは「`inv(ri)` が `ri` の意味的逆になる」ことだけで、これは `X^=X` を含む任意の
R-WHILE プログラムと同じ事情。

**人間に判断を仰ぎたい点**：これを論文の主張として「自己解釈器は可逆である」と書いている箇所が
あるなら、`X^=X` を含むプログラムを解釈するときは例外、という但し書きが要る。
層の昇格は人間の仕事なので、ここでは事実の記録に留める。
なお過去案 (a)（spec_av を遅延クリア `C^=A; A^=C` 化）は **ri を可逆に保ったまま**残余を通す道として
依然有効で、(b) と排他ではない。両立させたいなら (a) を別途進めるのが筋。

### 触ったファイル

| ファイル | 変更 |
|---|---|
| `examples/ri.rwhile` | `'ass` を保存値方式に。新変数 `AssV` を 1 つ導入（STEP のローカル） |
| `src/TestSuite.ml` | `ri-selfclear` 群を新設（4 test case）＋ `test_fp1_dyncond_known_bug` の `check_raises` を正答比較に反転＋その test_case ラベル更新 |
| `examples/fp_dyncond_bug.rwhile` | ヘッダの「BUG 2 (OPEN)」を修正済に |
| `HANDOFF_fp2.md` | 冒頭の run_via_ri 注意書きと §0f を更新（上の判断も記録） |
| `FINDINGS_reversible_projections.md` | §3（bug2 を修正済に）、§4（「ri.rwhile は可逆」の主張を訂正） |

### 新設した `ri-selfclear` 群（4 件、すべて直接評価と突き合わせる形）

判定を定数ベタ書きにせず「自己解釈＝直接評価」という本来の義務で書いた（`check_selfclear`）。

1. `test_selfclear_bare` — `read X; A ^= X; A ^= A; write X`（atom / cons / nil）
2. `test_selfclear_set_then_clear` — `Y ^= 'k; Y ^= Y`、および `Y ^= tl Y`（E が代入先を読むが値は nil）
3. `test_selfclear_dynamic_slot` — `read X; R ^= X; X ^= X; write R`
   （自己クリアされるのが**動的入力スロット**＝ri の DynIdx/DynVal 経路。Vl リスト歩行と別経路）
4. `test_selfclear_fp_dyncond_via_ri` — `fp_dyncond_bug.rwhile` 本体の自己解釈、および
   spec_av 残余について `run_via_ri` == `run_comp_direct`

### 手計算で確認したこと（＝実行の代わりに置いた根拠。実行で確かめ直すこと）

- `AssV ^= V` は V を壊さない（`rupdate`: 現在 nil → 代入）。`AssV` は各 'ass の入口で常に nil。
- `EVAL-EXP` は E を復元して終わる（`cons E nil <= E'`）ので `INV-EVAL-EXP` の前提を満たす。
  `EVAL-EXP` と `INV-EVAL-EXP` の間で生きているのは V と H だけ（`St` も `E'` も nil）。
- `DUPDATE` を後ろに移しても `Elem/Rest/Rev/Cnt` は前後どちらでも nil なので AUX 歩行に影響なし。
- `AssV ^= AssV` は v=nil でも安全（`rupdate` の nil → nil）。
- `ri.rwhile` の変数は約 50 個 → 1 増えても冒頭の「M >= 75」も `Vl` の 256 スロットも余裕がある。
- 追加した長いコメント中に `(*` / `*)` は入っていない（字句エラーにならないこと）。

### まだ確かめていない・危ないところ（翌晩の最初の一手）

1. **`make run-tests` が通るか**。OCaml のコンパイルすら試せていない。
   `ri-selfclear` 群の 4 関数は既存コードの形を写して書いたが、型・スコープは未確認。
   挿入位置は `test_fp1_dyncond_known_bug` の直後（`run_via_ri` / `run_comp_direct` / `spec_in` /
   `examples_dir` はすべてスコープ内のはず）。
2. **`test_ri_ri_id` / `test_ri_ri_ri_id`（ri で ri を解釈）**。今回 ri.rwhile 自身が `AssV ^= AssV`
   を含むようになったので、この 2 本は「修正が正しいこと」に依存するようになった。
   ここが赤なら修正のどこかが間違っている、という良い指標になる。逆に言うと**最大のリスク**。
3. `first-projection-min` 群（`fp1_min` / `fp1_seq`）は `run_via_ri` を使う既存の緑。
   store 効果は不変にしたつもりだが、要確認。
4. `./measure_proj full` の fp2（`[comp2](('S.swap)) == B`）は spec_av + ri_min のみで
   ri.rwhile を通らないので**影響しないはず**。ただし未実行。
5. ドキュメントの追随。`HANDOFF_fp2.md` / `FINDINGS_reversible_projections.md` /
   `examples/fp_dyncond_bug.rwhile` は更新済。**`RESEARCH_ROADMAP.md` と `AGDA_CORRESPONDENCE.md` は
   未確認**（grep が使えず全文読破の余力がなかった）。「bug2 は未修正」「run_via_ri は使えない」
   「ri.rwhile は可逆」と書いてある箇所が残っていたら直すこと。
   特に **「自己解釈器 ri.rwhile は可逆」という主張は今後は但し書き付き**である
   （FINDINGS §4 に訂正を書いた）。Agda 側にこの主張を写した補題があるなら要確認。
6. `RWHILE_HYGIENIC=1 ./test-suite`（衛生モード）は未確認。`AssV` は STEP 内だけで使う
   マクロローカルなので 1 箇所展開＝一貫リネームのはずだが、未検証。

### もし修正が間違っていた場合の切り戻し

`examples/ri.rwhile` の `'ass` を元の 3 行
（`EVAL-EXP(E,V,H); DUPDATE(Vl,K,V); INV-EVAL-EXP(E,V,H);`）に戻し、
`src/TestSuite.ml` の `ri-selfclear` 群を削り、`test_fp1_dyncond_known_bug` を
`check_raises (Failure "error in update")` に戻せば元の緑に戻る。
