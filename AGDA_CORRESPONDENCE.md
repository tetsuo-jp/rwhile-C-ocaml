# Agda 形式化 ↔ 実装 の対応とギャップ（#2 棚卸し）

2026-06-19。`proofs/agda/`（README 参照、`--safe`・postulate 0、唯一の仮定は `funext`）と
実行系（`src/*.ml`・`examples/*.rwhile`）の対応を棚卸しし、「機械検査済み」「差分テストのみ」
「未接続」を区別して、コアと実装を厳密に結ぶための次手を特定する。

## 1. 対応表（実装の各部品 ↔ Agda の結果 ↔ 強さ）

| 実装の部品 | Agda 結果 | 強さ |
|---|---|---|
| `InvRwhile.invCom`（atom/seq/cond/loop） | `RWhileRev`/`RWhileRevFull`：`inv-sound`/`inv-inv`/`inv-complete` | **証明**（モデルが invCom を厳密に写す） |
| `EvalRwhile.rupdate`（可逆 XOR 代入） | `RWhileValStore`(`RAss-sym`)・`RWhileExecConcrete`(`rupdF`) | **証明**（部分対合・決定性） |
| `EvalRwhile.evalCom`（**アルゴリズム**） | `RWhileExec`：`frun ≡` 関係意味（`frun-sound/complete`）、`frun-reversible` | **証明**（ただし `frun` は手書きで evalCom を模倣） |
| パターン読み書き `CRep`（`evalPat`/`inv_evalPat`） | `RWhileCRep`/`RWhileCRepDet`：`read-write`/`write-read`/`crep-reversible` | **証明** |
| `Core.ml` `norm_exp`/`norm_pat`/`eval_cexp` | `RWhileCoreExp`：`norm-correct`/`read-norm-correct` | **証明** ＋ `core-ir` 差分テスト |
| `Core.ml` `elaborate`（com→core） | `RWhileElabCom`：`elab-sound`/`elab-complete` | **証明** |
| `MacroRwhile.expMacProgram`（衛生性） | `RWhileMacroSubst`：`subst-exp`/`subst-upd`/`capture` | **証明**（衛生的なら健全、を定理化） |
| `spec_av` fp1（構造的残余化） | `RWhileFutamura`(`mix`,`fp1`)・`RWhileRevFutamura`(`reversible-fp1`,`mix-commute`) | **証明だが op 言語の `mix` 限定**。実 AV 機構は未モデル |
| `spec_av` fp2/fp3（byte 一致） | `RWhileFutamura2`(H1+H2 から fp2/fp3)・`RWhileRevProjPaper`(`rev-proj1/2/3`) | **モジュラ定理は証明**。具体例は **closure ctor `papp`** か小 op-list（下記）で、実 `spec_av` ではない |
| 自己適用器の具体例 | `RWhileFutamura2Inst`/`RWhileRevProjInst`（`papp`/`mkpapp`, refl）・`RWhileRevProj2Self`（op-list, **実残余化**, refl） | **証明だが closure か小言語**。`ExtractRevProj` で第2可逆射影を実機計算 |
| `spec_av` の BTA 修正（`MKAV`） | `RWhileRevProj2BT`：`fp2-buggy-mistags`/`correct-uses-input`/`overstatic-wrong` | **設計仕様を証明**（真因＝無条件 `'S` タグ、修正＝束縛時刻認識） |
| `spec_av` の lift イディオム（`ASSEMBLE-FP1`） | `RWhileRevProj2Lift`：`idiom-ok`/`idiom-drift`/`fix-roundtrips`/`selfClear-masks` | **設計仕様を証明**（lift が operand 保存 ⇔ 成立） |
| 可逆化ゴミ（`spec_av_rev`） | `RWhileRevProjGen`：`garbage-necessary`/`input-preserving-inj` | **抽象は証明**。実装は −57% を実測（`FINDINGS §6`） |
| 反復ワークリスト（`PAT-READ-ITER`） | `RWhileIL`（flat-IL→R-WHILE 翻訳の意味保存・IL 可逆性） | **方法論は証明**（IL で証明し検証翻訳で移送）。`PAT-READ-ITER` 自体は未モデル |

## 2. ギャップ（埋めるべき順）

- **G1（最重要・一部クローズ ✓）：実 `spec_av` の AV 代数を Agda 化した（N2 第1段）。**
  `RWhileAVSound.agda`（`--safe`）が AV（`S`/`D`/`C`）・残余コード `⟦_⟧c`・概念化 `γ` を定義し、
  `AV-HD/TL/CONS/EQ/PAIRP/LIFT` 各演算が γ と**可換であること（健全性）**を機械検査
  （`avHd-sound`/`avCons-sound`/…/`lift-sound`）。これが特殊化の正しさ＝H1 `spec-correct` の congruence 核。
  **N2 第2段 ✓（H1 完了）**：`RWhileAVSpec.agda` が AV 記号評価 `aeval`＋健全性 `aeval-sound` を組み、
  束縛時刻分割 `C (S s)(D cVar)`（MKAV 規律）の残余化で **H1 `spec-correct`：`⟦spec p s⟧c d ≡ ⟦p⟧c (s·d)`**
  を実 AV 機構で証明（`RWhileFutamura2` の H1 を closure/op-list 代用でなく discharge）。
  **残り（G1 最後）**：H2 `spec-impl`（特殊化器を自己言語のプログラムとして表現＝自己適用）。これは IEICE
  草稿も残す工学課題。H1（正しさの核）は機械検査済みなので、fp1 は実 AV で成立、fp2/fp3 は H2 追加で従う。
- **G2：`Core.ml ≡ EvalRwhile`（実用上クローズ済 ✓ — N1 実施）。** Agda は両者の**モデル**を別個に
  証明（`RWhileCoreExp`/`RWhileElabCom`）。OCaml レベルの等価は、`core-equiv` 群（`test_core_equiv_corpus`/
  `test_core_equiv_selfinterp`）が**実例コーパス7本＋完全自己解釈器 ri.rwhile の p2d 入力3本**で
  `EvalRwhile.evalProgram == Core.eval_program_core` を表明し経験的に保証。残る厳密化（OCaml 上の証明
  または抽出）は G3。
- **G3：リテラル OCaml は抽出/証明されていない。** `frun`/`eval_core` は手書きで evalCom を模倣
  （README「Honest scope」）。
- **G4：式言語・`all_cleared` 不変条件・`p2d`/`data2program`・パーサが Agda 範囲外。** 特に `p2d`
  は射影機構の中核（プログラム⇄データ）なのに未検証。

## 3. 次手（費用対効果順）

1. **N1（安・高）✓ 実施済**：`core-equiv` 群を追加し、実例コーパス＋自己解釈器で
   `Core.eval_program_core == EvalRwhile.evalProgram` を表明（`TestSuite.ml`）。`RWhileCoreExp`/
   `RWhileElabCom` の抽象証明と合わせ「検証コアを実装が refine」を経験的に主張できる。
   （さらなる強化：spec_av fp1 も `Slow` で core-equiv に追加可能。）
2. **N2（中・最高）：AV 特殊化ステップの Agda モデルで H1/H2 を証明。**
   - **第1段 ✓ 実施済**：AV 代数の健全性 `RWhileAVSound.agda`（各 AV 演算が γ と可換）。
   - **第2段 H1 ✓**：`RWhileAVSpec.agda`＝`aeval`/`aeval-sound`/`spec-correct`（H1, MKAV 分割）。
   - **第2段 H2（残）**：特殊化器の自己言語表現（自己適用）。これで `RWhileFutamura2` 完全インスタンス化＝
     実機 fp2/fp3 が証明された定理の具体例に格上げ＝G1 本丸クローズ。IEICE 草稿も残す工学課題。
3. **N3（中）：検証コアの抽出（Agda GHC）と OCaml 差分。** `Extract*.agda` の路線で `eval_core` 相当を
   抽出し、`EvalRwhile` とコーパス差分＝G3 を縮める。
4. **N4：`p2d`/`data2program` の往復（`data2program ∘ program2data = id`）を Agda 化＝G4 の中核。**

## 4. まとめ（論文での言い方）
「surface→core 翻訳の意味保存（exp/pat/制御）・衛生的マクロ展開・`inv` の可逆性・決定性は機械検査済み。
fp1（mix）と可逆 fp1、fp2/fp3 のモジュラ定理、BTA 修正・ゴミ二分律も機械検査済み。さらに **実 AV 機構の
spec-correct（H1）と AV 代数健全性、`case` 健全性、ゴミ量的下界も機械検査済み**。実 `spec_av` の fp2/fp3 は
byte 一致テストで実機検証され、形式的には残る唯一の橋が H2（自己適用の自己言語表現）。」

## 5. 最終状態（方針 (a)：H1 まで genuine、H2 は明示的 future work）
- **Agda 形式化は 28 モジュールすべて `--safe` で通過**（postulate 0、唯一の仮定は `RWhileDetConcrete` の `funext`）。
- **済**：可逆性/決定性/翻訳意味保存/衛生/可逆fp1/モジュラfp2-3/BTA/ゴミ二分律・**量的下界**/`case`健全性/
  **AV 代数健全性**/**実 AV の H1 spec-correct**。OCaml 側は `core-equiv` で `Core.ml ≡ EvalRwhile` をコーパス保証、
  実機 fp2/fp3 は byte 一致、特殊化有効性は `specialization-gain` で回帰ガード。
- **未解決（明示的 future work）＝H2 `spec-impl`**：AV 特殊化器を自分の対象言語のプログラムとして表現する
  自己適用。これは IEICE 草稿も残す本分野の本質的課題で、実機 `spec_av` の byte 一致 fp2/fp3 がその**経験的
  証拠**。H1 が機械検査済みのため、H2 を加えれば fp2/fp3 が「証明された定理の具体例」へ格上げされる（G1 完了）。
