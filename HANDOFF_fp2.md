# 引継ぎ: 第2可逆射影 (fp2) を本番 spec_av で通す（専用セッション向け）

最終更新 2026-06-17。前セッションで **症状→真因→修正仕様→構成的実現→移植計画** を全て Agda で
確定。本番 spec_av は**無変更**（全グリーン 162 OK）。このセッションの目的は **本番 spec_av の
二段階化（BTA）** を実装し fp2 を正しく通すこと。

---

## 0b. 2026-06-17(2) セッション結果 ＝ BTA を実装し「必要だが不十分」を実証（最新・先に読む）

**やったこと（コミット 2 本、fp1 全 spec_av 群 green 維持）**
- `2c8d23f` MKAV マクロ追加（`examples/spec_av.rwhile`）。`MKAV(BT,Src,Ic,AVout)`：
  `BT='S → ('C.(('S.Src).('D.('var.Ic))))`（従来 fp1）／`BT='D → ('D.('var.Ic))`（全動的・Src 破棄）。
  単体テスト 3 本を av-algebra 群に追加（mkav static / static-idx1 / dynamic）。
- `f798880` main を BTA 契約へ：`read In; cons Prog FpBTS <= In; cons FpBT Src <= FpBTS;`、
  旧 L1051 を `MKAV(FpBT,Src,FpIc,FpPart)` に。TestSuite の fp1 呼出 7 箇所を
  新ヘルパ `spec_in p src = (p.('S.src))` でラップ。**fp1 不変（spec_av 群全 green）**。

**fp2 の結果（前進したが未達）**
- 入力は新契約：`fp2.val = (p2d(spec_av) . ('S . p2d(ri_min)))`（再現 §4 を更新のこと）。
- **`'10` を脱出**：旧 baseline は生成中に `'10`。BTA 後は**生成成功＝comp 3.19MB**
  （偽修正の 1158B 過剰静的退化では**ない**）。
- **だが compiler はまだ壊れ**：`[comp](('S.'swap))` を ri 経由実行で
  **`error in update: var=Elem cur=(nil.(nil.nil)) new=(nil.nil)`**。
  基準 B=`[spec_av]((ri_min.('S.'swap)))`=436B は正答（[B](('a.'b))=('swap.('b.'a))）。

**新しい真因（局在）・次の壁**
- fp2 では BT が OUTER から動的 → MKAV の `if MkS` が **comp に残余化**され、その残余条件
  （then=構造化 AVout／else=Src クリア＋'D、両枝で store 効果発散）の**可逆化が壊れ var=Elem**。
  fp1 は BT 静的→条件静的消去で無傷（静的 BT='D の fp1 は 694B でクリーン＝動的枝自体は健全）。
- **BT を静的側 `((Prog.BT).Src)` に移す案は不可**：条件は静的化できるが fp2 で `('S.<動的Src>)`
  の過剰静的ミスタグに逆戻り。根本は **AV が静的“値”を運ぶ設計**で、自己適用下では 'S-AV が
  動的(記号)値を運ぶ必要があり下流(AV-LIFT/AV-EQ/AV-HD)が具体値前提で破綻＝online 値運搬 AV と
  offline 二段階 BT の本質的不整合。真の修正は AV 代数の offline 化（「静的・存在保証だが記号的」
  区分の導入）＝大規模研究。⇒ 現実解は研究方針どおり R-CORE で小 self-applicable specializer を
  作り意味保存翻訳で橋渡し（option 2）。memory: `second-futamura-projection-status` 更新済。

## 0d. 2026-06-17(4) 高速最小再現を確立（最新・最重要・ここから直せる）

- **`examples/fp_dyncond_bug.rwhile`**（コミット f61fdab）＝正当な可逆プログラム
  (`[prog]((nil.d))='one`)。`comp=[spec_av]((prog.('S.nil)))` 生成成功・`[comp](d)` が
  `error in update` で落ちる＝**fp2 var=Elem を fp1 規模・1秒未満で再現**。テスト
  `test_fp1_dyncond_known_bug`(assemble-fp1 群、緑 characterization。修正後は `[comp](d)='one` に反転)。
- **真因の一般化**：条件なし／**静的テスト**条件は正しく特殊化される。**動的入力をテストする条件**だけが
  発症（SPEC-STEP-AV 'cond, L922- の **DYNAMICIZE-ALL + 残余 cond が可逆性を壊す**）。ri_min/ri_seq の
  fp1 が通るのは条件が静的 op を分岐するから。fp2 の var=Elem はその一般形（自己適用で spec_av 自身の
  条件 MKAV 等が動的化）。
- **次の作業**：MKAV/index 固有ではなく **spec_av の動的テスト条件残余化** を可逆に直す。手順：
  `./ri -p2d examples/fp_dyncond_bug.rwhile >/tmp/p.val; printf '('; cat /tmp/p.val; printf " . ('S . nil))"`
  を spec_av に渡して comp 生成→ ri.rwhile で `[comp]('q)` 実行が `'one` になるまで DYNAMICIZE-ALL／
  'cond 残余化を修正。緑判定＝`test_fp1_dyncond_known_bug` を正答主張に反転して通す。

---

## 0c. 2026-06-17(3) var=Elem 局所診断 ＝ '10 と同一真因

- **op 非依存**：`[comp](('S.'id))` も `'swap` と**同一エラー・同一 index(cur=2,new=1)**。基準
  `B_id=[spec_av]((ri_min.('S.'id)))`=268B は健全。⇒ var=Elem は comp の**共有プロローグ**
  （入力デコード＋MKAV 残余条件）に局在し、op 本体とは無関係。
- **DYNAMICIZE-ALL が必須**：MKAV を分岐なし版
  `AVout <= cons 'C (cons (cons BT Src) (cons 'D (cons 'var Ic)))` にすると fp2 生成が
  **'10 に逆戻り**（78B）。分岐版（=現コミット）は DYNAMICIZE-ALL で '10 を脱出し 3MB 生成まで
  到達＝**現コミットの分岐版が最良**。動的化は必要だがその後が壊れる。
- **var=Elem の正体**：`UPDATE(Vl,J,X)`=`AUX; Elem ^= X; INV-AUX`、AUX は動的 index J の
  `from..until(=? Cnt J)` ループ。fp2 全動的化で残余化された **`Elem ^= X`(可逆 XOR 代入)** が
  実行時 Elem=index2・X=index1（nil でも等しくもない）で可逆性違反。
- **結論**：`'10`(L849 static-assign) と `var=Elem`(L869-883/UPDATE dynamic-assign) は**同一根**＝
  自己適用の全動的化下で spec_av が **reversible-update(`^=`)/index 歩行(AUX/LOOKUP/UPDATE) を
  可逆に残余化できない**（動的化レベルが違うだけ）。一行修正不可。次手は SWAP-VIA-TEMP 系の
  「可逆代入を保存する残余化」を 'ass 残余化＋index コードへ拡張＝実質 self-app 本体／または R-CORE
  option 2。memory: `second-futamura-projection-status` に全詳細。

---

## 0. 結論サマリ（これだけ読めば文脈が分かる）

- **fp1 は green**：`[spec_av]((ri_min . op))` / `[spec_av]((ri_seq . oplist))` は正しく動作（テスト・Agda 証明済）。
- **fp2 = `[spec_av]((spec_av . ri_min))` は未通**。真因は **`examples/spec_av.rwhile:1051`**
  ```
  FpPart <= cons 'C (cons (cons 'S Src) (cons 'D (cons 'var FpIc)));
  ```
  が **静的入力 Src を `'S`（静的）で無条件タグ**すること＝**束縛時刻(BT)の静的コミット**。
  fp1 では Src は本当に静的で正しいが、自己適用(fp2)では内側の Src は**動的値**になり 'S が嘘 →
  過剰静的退化（compiler が壊れる）。
- **値だけから BT は判別不能**（Jones の「naive specializer は self-applicable でない」）。
  ⇒ 修正は **spec_av が BT 情報（注釈付き入力）を受け取る再設計**。一行修正では不可。

## 1. やってはいけない（前セッションで排除済・再試行禁止）

- **clear 側の小細工は全滅**。ASSEMBLE-FP1 (L259-262) の2発目 clear を
  - 自己クリア `AsAV ^= AsAV`、または
  - 分解クリア `cons AsOt AsOv <= AsAV; AsOt^=AsOt; AsOv^=AsOv`（DYNAMICIZE-ALL 型）
  に変えると、fp1 は 162 OK のままだが **fp2 の compiler が壊れる**（`error in update: var=Vl`、1158B 退化）。
  ＝`'10` は症状で、AV-LIFT/clear はいずれも**下流**。Agda `selfClear-masks` で「clear バイパスは
  drift に鈍感＝偽の修正」を証明済。**clear 側・AV-LIFT 単体をいじっても直らない。**

## 2. 修正方針（証明裏打ち、plan 6.3.7 参照）

**選択肢1: 二段階化（推奨）**
- spec_av の入力を BT 注釈付きに（例 `(Prog . (BT . Src))`）。L1051 を
  `mkAV BT Src`（BT=static→`('S.Src)`, dynamic→`('D.('var.I'))`）に。
- fp1 互換：BT=static を渡す薄いラッパ（既存テストは BT=static で不変）。
- fp2：外側が内側へ渡す BT が dynamic になり、'S 固定の嘘が消える。
- **関数仕様 = `proofs/agda/RWhileRevProj2BT.agda` の `mkAV`**（`fp1-ok`/`fp2-buggy-mistags`/
  `overstatic-wrong` が満たすべき性質）。

**選択肢2: 翻訳で橋渡し（研究方針の住み分け）**
- 小コア版 `proofs/agda/RWhileRevProj2Self.agda`（BT-aware op-list specializer、fp1/fp2/fp3 が
  本物の残余で `refl`）を「正」とし、意味保存翻訳で本番相当へ移送。本番 spec_av を直接いじらない。

## 3. 参照すべき Agda（すべて --safe、`proofs/agda/`）

- `RWhileRevProj2Lift.agda` — clear/lift の必要十分条件・偽修正の排除（`idiom-ok`/`idiom-drift`/
  `selfClear-masks`/`bug-reproduces-'10`）。
- `RWhileRevProj2BT.agda` — **真因＋修正仕様**（`mkAV`/`fp1-ok`/`fp2-buggy-mistags`/
  `buggy-ignores-input`/`correct-uses-input`/`overstatic-wrong`）。←**移植の関数仕様**
- `RWhileRevProj2Self.agda` — **構成的実現**（BT-aware self-applicable specializer、`fp1`/`fp2`/`fp3`/
  `compiler-residual-uses-input`/`fp2-correct`）。←**目指す姿**
- 既存：`RWhileFutamura2`(階層論理 H1+H2)、`RWhileFutamura2Inst`(papp で H2 充足だが lift 自明化)。
- 全チェック：`proofs/agda/README.md` の `## Checking` の for ループ。

## 4. 再現手順（fast test 不在 → 実 fp2 は ~120s）

```bash
cd src && export CAML_LD_LIBRARY_PATH="/home/tetsuo/.local/share/opam/default/lib/stublibs:$CAML_LD_LIBRARY_PATH"
make ri test-suite
# fp1 高速回帰（必ず緑を維持。基準: 162 OK / 0 FAIL）
./test-suite | grep -cE '\[OK\]'        # => 162
./test-suite | grep -cE '\[FAIL\]'      # => 0

# fp2 入力の生成（/tmp は消えている前提で毎回再生成）
./ri -p2d ../examples/spec_av.rwhile > /tmp/inner.val
./ri -p2d ../examples/ri_min.rwhile  > /tmp/rimin.val
python3 - <<'PY'   # outer = spec_av だが FpN(店サイズ)を N=300 に拡大（内側 213+ 変数）
import re
s=open("../examples/spec_av.rwhile").read()
lit=lambda n:("nil" if n==0 else "(nil."+lit(n-1)+")")
open("/tmp/outer.rwhile","w").write(re.sub(r"FpN \^= \([^;]*\);","FpN ^= "+lit(300)+";",s))
PY
# 新契約（BTA, 2026-06-17(2) 以降）: outer 入力 = (inner . ('S . rimin))
printf '(' > /tmp/fp2.val; tr -d '\n' </tmp/inner.val >>/tmp/fp2.val
printf " . ('S . " >>/tmp/fp2.val; tr -d '\n' </tmp/rimin.val >>/tmp/fp2.val; printf '))\n' >>/tmp/fp2.val

# 旧 baseline はここで '10。BTA 後は生成成功＝comp 3MB（>/tmp/fp2_fixed.out）。
timeout 280 ./ri /tmp/outer.rwhile /tmp/fp2.val > /tmp/fp2_fixed.out 2>&1; wc -c /tmp/fp2_fixed.out
# comp の正しさ判定: comp_swap=[comp](('S.'swap)) を ri 経由で。現状は var=Elem で落ちる（未達）。
#   B=[spec_av]((ri_min.('S.'swap))) を基準に比較（B は 436B で正答）。
#   printf '('; cat fp2_fixed.out; printf " . ('S . 'swap))"  を ri.rwhile に渡し cdr を取る。
```

## 5. 成功判定（修正が正しいことの確認）

1. **fp1 不変**：`./test-suite` が 162 OK / 0 FAIL（BT=static 経路が既存と一致）。
2. **fp2 が '10 を出さず completes**（必要条件、十分でない！ clear 側修正もここまでは到達した）。
3. **compiler が正しい（本命）**：compiler = fp2 の出力（p2d データ）。ri.rwhile 経由で
   `[[compiler]('swap)](('a.'b)) == ('swap.('b.'a))` を確認。
   - 比較基準 B = `[spec_av]((ri_min . 'swap))`（fp1 残余）。`[compiler]('swap) == B` なら第2射影成立。
   - run 方法：`run_via_ri`（`src/TestSuite.ml:712`）＝ ri.rwhile に `(prog_data . d)` を渡し cdr を取る。
   - 偽修正版はここで `error in update: var=Vl` で落ちた（compiler 壊れ）。**落ちずに正答が判定基準**。
4. 緑になったら `src/TestSuite.ml` に `second-projection` 群（fp2_min 等）を新設して回帰固定。

## 6. 道具・落とし穴

- **変数 index ⇄ unary の対応**：`conss [v]→v`(`Program2DataRwhile.ml:8`) なので
  **index n = nil n 個**（n+1 ではない！ 前セッションは off-by-one で Rest13/A'15 と誤読、正は
  AsAV14/Elem12/LfTag16/LfPay17）。変数順ダンプ: `src/dump_vars.ml`(untracked、
  `expMacProgram→varProgram` 順を印字。`ocamlfind ocamlc ... EvalRwhile.cmo dump_vars.ml -o dump_vars`)。
- 計装は `show E`（CShow は反転しても CShow で安全）。`'10` は `examples/spec_av.rwhile:849`、
  `'41` は L994（動的ループ出口）。
- 最小再現 `tiny_lift`（AV-LIFT だけ）は `'41` で**不忠実**（ループ動的化）。忠実再現は実 fp2 のみ。
- hygiene 非依存：`-hygienic-macros + N=1000` でも '10 再現（衛生衝突ではない）。
- 詳細ログ：`plan_fp1_stage_c.md` §6.3.1〜6.3.7。研究方針 memory: `research-direction-core-language`、
  現況 memory: `second-futamura-projection-status`。

## 7. リスク・運用

- spec_av の入力契約変更＋partial-input 二段階化＋（場合により）AV 処理の二段階化。複数セッション規模・
  高リスク。**不変条件＝fp1 系 162 OK を毎ステップ維持**。
- 1 green サブステップ = 1 commit、push は明示時のみ。コミット前 `gitleaks git --staged --no-banner`。
  コミット末尾に `Co-Authored-By: Claude Opus 4.8 <noreply@anthropic.com>`。作業ログは Notion に 1依頼=1行。
