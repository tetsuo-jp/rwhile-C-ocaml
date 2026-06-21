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
  **N2 第3段 ✓（統一・fp1 無条件）**：`RWhileP2D.agda`（G4）が残余 `Code` の `program2data`/`data2program`
  と往復 `data2program ∘ program2data ≡ id`（＋符号化の単射性 `p2d-injective`）を機械検査。これを使い
  `RWhileAVSelfApp.agda` が U=Val の単一値型に統一（`runU pv d = ⟦d2p pv⟧c d`, `specU pv sv = p2d(spec(d2p pv)sv)`）し、
  **実 AV 機構の H1（spec-correct）を統一型で discharge**（`specU-correct`）→ **fp1 が実 AV で無条件成立**（`fp1U`）。
  fp2/fp3 はモジュラ論理 `RWhileFutamura2` を実 `runU`/`specU` でインスタンス化した `WithSelfApp`（H2 を引数に取る）で
  certify＝「実 run/spec に対し階層の論理は健全、残るは H2 ただ一本」。
  **N2 第4段 ✓（H2 の再帰核を非クロージャで discharge）**：`RWhileH2.agda`。AV 式言語 `E`（spec_av の
  AV マクロ AV-HD/TL/CONS/EQ/PAIRP に対応）と汎用全域インタプリタ `cata`（Code 構造の fold＝`aeval` が
  構造停止ゆえ全域）を定義し、スペシャライザを**データとしての代数 `specAlg`**（Code タグごとの `E` 項、
  `SPEC-EXP-AV-STEP` の忠実モデル）で表現。**`self-rep : cata specAlg c a ≡ aeval c a`**＝実記号評価器が
  `papp` 等の組込み構成子なしに genuine データプログラムであることを機械証明、`specByProg-correct :
  specByProg ≡ spec` で H1 を継承。Inst の closure 回避より厳密に強い。
  **残り（G1 最後）＝完全 `spec_av` の H2**：上記は構造的 `aeval` モデルで閉じたが、実 `spec_av` の
  非構造部（有界ワークリスト＝ループ／Turing 完全）の自己適用は未。具体式 `runU specP (pv·sv) ≡ specU pv sv`
  を単一プログラム言語で一様に閉じるには **fuel-indexed/部分性モデル（route A）**が要る。理由：(1) 残余 `Code`
  は非再帰一階式で `spec` を表現不能（→`E`+`cata` で解消）、(2) 全域メタ言語 `--safe` では Turing 完全対象言語の
  全域万能 `runU` 不在（ループ付き spec_av に残る本質障害）。実機 byte 一致 fp2/fp3 が経験的証拠。H1 は機械検査済み。
- **G2：`Core.ml ≡ EvalRwhile`（実用上クローズ済 ✓ — N1 実施）。** Agda は両者の**モデル**を別個に
  証明（`RWhileCoreExp`/`RWhileElabCom`）。OCaml レベルの等価は、`core-equiv` 群（`test_core_equiv_corpus`/
  `test_core_equiv_selfinterp`）が**実例コーパス7本＋完全自己解釈器 ri.rwhile の p2d 入力3本**で
  `EvalRwhile.evalProgram == Core.eval_program_core` を表明し経験的に保証。残る厳密化（OCaml 上の証明
  または抽出）は G3。
- **G3：リテラル OCaml は抽出/証明されていない。** `frun`/`eval_core` は手書きで evalCom を模倣
  （README「Honest scope」）。
- **G4（大幅クローズ ✓）：`p2d`/`data2program` の往復を Agda 化した。** `RWhileP2D.agda` が残余 `Code` の
  往復＋`p2d-injective` を、**`RWhileP2DProg.agda` が制御コア（exp/pat/com/program）の往復
  `dProg(transProg p) ≡ p`** を機械検査（変数 index はクリーン unary 符号化でモデル＝OCaml の off-by-one は
  一貫リラベルの incidental quirk）。**残り**：`all_cleared` 不変条件・残りの surface 構文（CShow/CLocal/
  CAutoFi/CArrAss、p2d 対象外）・パーサは依然 Agda 範囲外。

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
4. **N4（✓ 実施済）：`p2d`/`data2program` の往復（`data2program ∘ program2data = id`）を Agda 化＝G4 の中核。**
   `RWhileP2D.agda`（残余 `Code` 対象）。これを土台に `RWhileAVSelfApp.agda` が統一型 fp1 と H2 の一点化を達成。

## 4. まとめ（論文での言い方）
「surface→core 翻訳の意味保存（exp/pat/制御）・衛生的マクロ展開・`inv` の可逆性・決定性は機械検査済み。
fp1（mix）と可逆 fp1、fp2/fp3 のモジュラ定理、BTA 修正・ゴミ二分律も機械検査済み。さらに **実 AV 機構の
spec-correct（H1）と AV 代数健全性、`case` 健全性、ゴミ量的下界、`p2d`/`d2p` 往復も機械検査済み**。
**単一値型に統一した実 AV 機構で fp1 を無条件に証明し（`RWhileAVSelfApp.fp1U`）、fp2/fp3 は実 `runU`/`specU` に
対するモジュラ論理として certify**（残る入力は H2 一本）。さらに **H2 の再帰核を非クロージャで discharge**
（`RWhileH2.self-rep`：実 `aeval` は汎用全域インタプリタ上の genuine データプログラム、`specByProg ≡ spec`）。
実 `spec_av` の fp2/fp3 は byte 一致テストで実機検証され、形式的に残る唯一の橋は完全 `spec_av` の非構造部
（Turing 完全ループ）の自己適用のみで、fuel-indexed モデルが要る。」

## 5. 最終状態（案2：G4・統一 fp1・H2核・非クロージャ/一般適用ハイアラーキ／案1：簡約器健全性＋選択肢2）
- **Agda 形式化は 45 モジュールすべて `--safe` で通過**（postulate 0、唯一の仮定は `RWhileDetConcrete` の `funext`）。
- **Tier-2 #5 工学（`RWhileH2Worklist.agda`）＝実 spec_av のワークリストを燃料モデルに具体化**：`SPEC-EXP-AV`/
  `PAT-READ-ITER` は明示的**スタックマシン**（ワークリスト `Cd`＋結果スタック `RSt`、begin/end マーカ、
  AV-CONS でボトムアップ結合）で、`cata` の構造再帰**ではない**非構造ループ（`from..until`）。これを忠実に
  モデル化＝タスクスタック（`doE e`/`comb`）の**燃料付きマシン** `machineF`（1ステップ=1タスク、cf. `runF`）。
  マシン関係 `_⟱_` でボトムアップ fold `metaFold` を計算することを証明（`machine-spec`/`machine-correct`、
  抽象機械の正当性補題）し、燃料版を健全 `machineF-sound`・完全 `machineF-complete`（線形ゆえ `⊔` 不要）・
  単調 `machineF-mono-≤` で `_⟱_` と一致。Witness（木の再構成＝PAT-READ-ITER 相当）で具体計算。
  **＝H2 の燃料モデル上に実 spec_av の looping ワークリスト機構を具体化（理論障害は解消済、残りは AV 代数の移植）**。
- **Tier-2 #5 達成（`RWhileH2Fuel.agda`）＝route A の fuel/部分性モデルを構築**：`RWhileH2Hier2` の一般適用
  言語に**燃料付き全域インタプリタ** `runF : ℕ → Tm → Tm → Maybe Tm`（`apT` が計算済プログラムを計算済引数に
  適用＝Turing 完全部、燃料が `nothing` で打ち切り）を与え、大ステップ関係 `_·_⇓_` と**一致**を証明：
  健全性 `runF-sound`・完全性 `runF-complete`・単調性 `runF-mono-≤`。これにより関係的 fp1/fp2/fp3 が
  **燃料レベルの全域定理** `fp1-fuel`/`fp2-fuel`/`fp3-fuel`（十分な燃料が存在すれば成立）に格上げ。
  `runF-correct`（`= ⇓-det ∘ runF-sound`）で燃料計算値が関係の値と一致。**＝H2 が要求していた
  fuel-indexed モデルを構築し、ループ付き自己適用を `--safe` 全域で表現**（残るは実 spec_av のワークリストを
  この `runF` 上に具体化する工学）。
- **案1 Phase 2c（選択肢2＝最適化スペシャライザの本質を機械検証）** 2026-06-21。本番 spec_av の高リスク再設計を
  回避し、再帰可能関係モデルで「解釈系を消した可逆残余の存在と正しさ」を証明（FINDINGS §9 Phase 2c に詳細）。
  - `RWhileH2HierRec`：`cata` 入り大ステップ関係。`mirrorP-reversible`（再帰∧可逆）／`reify-spec-correct`（定数族 H1、
    走る残余生成）／`prepend-spec-correct`（入力依存残余）＝quoted-construction-under-recursion。
  - `RWhileH2HierRecSelf`：`RWhileRevProj2Self` の最適化性（解釈系除去・runtime 入力使用・over-static なし）を関係へ
    持ち上げ。`compileOps-correct`（op-list を `ap`-チェイン残余へ畳み込む真の再帰）。
  - `RWhileH2HierDispatch`：静的ディスパッチ解決（`=? Tag 'op`）。`dispatch-eliminated`（残余から分岐ノード消去）。
  - `RWhileOptRev`：最適化∧可逆（`foldOps-invert`、逆は invList で構文的）。
  - `RWhileMain`：上記の見出し定理を再輸出するキャップストーン（recself/disp/optrev/reify/prepend/mirrorP-reversible）。
- **案1 Phase 2a（`RWhileSimpSound.agda`）**：残余簡約器 `src/Simp.ml` の意味保存を機械検証。定数畳み込み規則
  （hd/tl/pairp of cons）＋dead 可逆分岐除去（`condF` の reversible cond 前方意味論で、入口・出口テストが定数
  同真偽なら生き枝へ＝`deadbranch-true`/`deadbranch-false`）。簡約器を「テスト済み」→「証明済み」に格上げ。
- **Phase A2 step1 達成（`RWhileH2Hier2.agda`）**：A1 の「適用をリテラル quote 限定」を外し、同じ言語 `Tm` 上に
  **大ステップ評価関係 `prog · x ⇓ v`**（`⇓ap` が関数位置を評価して一般適用、fuel 不要）を与える。関係なので `--safe`
  で全域定義可・部分性＝導出無し。決定性 `⇓-det`、H1（両方向）・H2 を自明スペシャライザで discharge、fp1/fp2/fp3 を
  一般適用つき関係定理として導出。**残る完全 A2＝ループ付き AV spec をこのモデルで表現**（route A、future。再帰構造は
  `RWhileH2` で済）。
- **Phase A1 達成（`RWhileH2Hier.agda`）**：Inst の `papp`/`mkpapp` 構成子を**実プログラム構成**に置換した
  全域・非クロージャのハイアラーキ実例。小さな適用言語 `Tm`（input/quote/pair/car/cdr/application＋builder）と
  汎用全域 `run`、自明スペシャライザ `spec p s = apT (quo p)(pr (quo s) inp)`（＝論文 rspec：p,s を埋めて実行）、
  残余を構成する genuine プログラム `specP`。**H1・H2 とも refl で成立 → fp1/fp2/fp3 が証明済み定理**（`compiler`/
  `cogen` は実プログラム）。全域の鍵＝適用をリテラル quote 限定（自明 spec が出すのはこの形だけ、fuel 不要）。
  一般適用＋ループ付き AV spec は fuel が要る＝Phase A2。
- **済**：可逆性/決定性/翻訳意味保存/衛生/可逆fp1/モジュラfp2-3/BTA/ゴミ二分律・**量的下界**/`case`健全性/
  **AV 代数健全性**/**実 AV の H1 spec-correct**/**`p2d`/`d2p` 往復（G4：残余 Code＋制御コア program、
  `RWhileP2DProg` 単射性込み）**/**ゴミ三点（下界 |garbage|≥|fiber|＋普遍達成 input-preserving＋可逆源 clean
  ＝二分律の定量化）**/**統一値型での実 AV fp1（`fp1U`、無条件）**/
  **H2 の再帰核を非クロージャで discharge（`RWhileH2.self-rep`：`aeval` は汎用全域インタプリタ上の genuine データ
  プログラム、`specByProg ≡ spec`）**。OCaml 側は `core-equiv` で `Core.ml ≡ EvalRwhile` をコーパス保証、
  実機 fp2/fp3 は byte 一致、特殊化有効性は `specialization-gain` で回帰ガード。
- **未解決（縮小）＝完全 `spec_av` の H2**：構造的 `aeval` の自己表現は `RWhileH2` で閉じた（Inst の closure 回避より
  厳密に強い）。残るは実 `spec_av` の**非構造部（有界ワークリスト＝ループ／Turing 完全）**を単一プログラム言語で
  一様に表現する自己適用で、これには **fuel-indexed/部分性モデル（route A）**が必要。理由：全域メタ言語 `--safe` では
  Turing 完全対象言語の全域万能 `runU` が存在しえない（ループ付き spec_av に残る本質障害）。実機 byte 一致 fp2/fp3 が
  その経験的証拠。**＝案2は「構造モデルで H1＋H2核を達成、Turing 完全部のみ future work」**。
