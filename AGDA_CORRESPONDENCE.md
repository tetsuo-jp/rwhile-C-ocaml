# Agda 形式化 ↔ 実装 の対応とギャップ（#2 棚卸し）

2026-06-19。`proofs/agda/`（README 参照、`--safe`・postulate 0、唯一の仮定は `funext`）と
実行系（`src/*.ml`・`examples/*.rwhile`）の対応を棚卸しし、「機械検査済み」「差分テストのみ」
「未接続」を区別して、コアと実装を厳密に結ぶための次手を特定する。

## 1. 対応表（実装の各部品 ↔ Agda の結果 ↔ 強さ）

| 実装の部品 | Agda 結果 | 強さ |
|---|---|---|
| `InvRwhile.invCom`（atom/seq/cond/loop） | `RWhileRev`/`RWhileRevFull`：`inv-sound`/`inv-inv`/`inv-complete` | **証明**（モデルが invCom を厳密に写す） |
| `EvalRwhile.rupdate`（可逆 XOR 代入） | `RWhileValStore`(`RAss-sym`)・`RWhileExecConcrete`(`rupdF`) | **証明**（部分対合・決定性）。**2026-08-05 に第 3 の場合を追加**（末尾「`rupdate` の第 3 の場合」参照） |
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
| `spec_av` の過剰静的化解消＝オフライン BTA 設計図（`MKAV`／`SPEC-CMD-AV` の 'cond 動的経路／agenda `Cd`） | `RWhileOfflineBTA1`–`9`（9 段、`RWhileMain` 再エクスポート）：`over-commit-unsound`/`mkAV-dyn-nonstatic`/`fp2-eq`/`fp3-eq`/`fix-agrees-on-fp1`/`compbug-wrong`/`seq-flatten-ok`/`specOff-keeps-branches`/`specBug-wrong`/`specOff-injective`/`specBug-not-injective` | **設計図を証明**（修正の形・fp1 安全性・ディスパッチ保存・agenda 設計規則・可逆性=単射性）。実機 comp2 の live-trace 根本原因（`TRACE_comp2_root_cause.md`）に対応。実機改造は未着手 |

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
- **Agda 形式化は 61 モジュールすべて `--safe` で通過**（postulate 0、唯一の仮定は `RWhileDetConcrete` の `funext`；
  うち `RWhileOfflineBTA1`–`9` はオフライン BTA 設計図＝§6 参照）。
- **案1-B step(a) residualize の可逆性（`RWhileLoopBTARev.agda`）**：loop-BTA が residualize する loop
  （`from (lift e) do D loop L until (lift f)`）が**可逆な R-WHILE ループ**であることを `RWhileRevFull` から継承して明示。
  テストを Val 状態述語（残余コード実行の truthiness）に、本体を残余命令にして `RWhileRevFull.Core Val` の `loop` に一致
  （`resLoop`）。`resLoop-inv`（inv は entry/exit 入替＝refl）／`resLoop-reversible`（`inv-sound`：forward s⇒t ⟹ inverse t⇒s）／
  `resLoop-inv-inv`（`inv-inv`：二重反転＝恒等）。⇒ **residualize は可逆性を保存**＝実装はこの形を emit するだけでよい。
  さらに **`constEntry-no-iter`**：entry を定数 true に畳む（AV-LIFT(`S vtrue`)＝`cVal vtrue`）と、可逆ループの `r-iter`
  （loop-back で entry が false 必須）が成立せず**反復不能**＝非可逆。⇒ 「静的 entry・動的 exit」ループの residualize は
  entry を**定数化してはならず**、制御スロット（Cnt 等）を dynamicize して entry テストを**再特殊化**し実テストとして残す
  必要がある（実装が守るべき subtlety を機械検証）。
- **案1-B ループ束縛時刻の決定（`RWhileLoopBTA.agda`, Agda-first）＝comp2 第2障害の修正青写真**：selective dynamicize で
  内側インタプリタが unroll を開始した後に出た spec_av の `'error <= '41`（'lcheck 動的 exit）の正しい修正規則を
  実装より先に Agda で証明。テストの AV を静的真理値に解決する `staticTruth`（`S`→既知, `C`→cons ゆえ true, `D`→不明）と
  その γ 健全性 `staticTruth-sound`、動的テストが実行時で変化し静的解決不能な `dynamic-varies`、**正しい unrollable は
  entry∧exit 両方が静的**（`unrollable`）で entry のみの旧判定が静的entry・動的exit ループ＝'41 状況で誤る
  （`bug-static-entry-dynamic-exit`）、**動的 exit は常に residualize を強制**（`exit-dynamic-forces-residual`）、燃料ループ上で
  unroll 1 段の健全性（`unroll-step-sound`／`exit-true-stops`＝'lcheck の2分岐）を機械検証。⇒ 実装は「'loop ハンドラで
  exit も特殊化し、両方静的でなければ residualize」に従えばよい（[[research-direction-core-language]] 方針＝証明先行）。
- **Tier-2 #5 検証済みの橋・コマンド層（`RWhileSpecAVWireCom.agda`）＝AST 全体の wire format ↔ モデルを定理化**：
  式に続き **パターン／コマンド／プログラム**を `Program2DataRwhile.transPat`/`transCom`/`transProgram` ↔
  `d_pat`/`d_com`/`data2program` に一行写しで橋渡し。`Pat`/`Com`/`Prog` を定義し、`encPat`/`parsePat`、`encCom`/`parseCom`
  （`'seq`/`'ass`/`'rep`/`'cond`/`'loop`、`'cond`/`'loop` の末尾 nil 終端も忠実）、`encProg`/`parseProg` を与え、
  **往復定理 `parse-enc-pat`／`parse-enc-com`／`parse-enc-prog`** を証明（＝**AST 全体↔実装 wire format が定理**＝
  意味保存翻訳の**構文側を完成**）。コマンドに埋め込まれた式は `encEx`/`parseEx` を再利用するので、特殊化器の
  γ 健全性（`wire-sound`）がコマンド内の全式に適用（`ass-exp-sound`）。OCaml `wire-bridge` 群に `d_com` 相互検証
  （同一 wire 木の復号＝`parseCom`、atom-free コマンドの `transCom`→`d_com` 往復）を追加。残＝コマンド層の
  **意味側**（操作的等価）は研究課題（SPEC_AV_CORRESPONDENCE §5）。
- **Tier-2 #5 検証済みの橋（`RWhileSpecAVWire.agda`）＝実装の wire format ↔ Agda モデルを定理化**：spec_av/p2d は
  式を R-WHILE 値（`'var`/`'val`/`'cons`/`'hd`/`'tl`/`'eq`/`'pairp` タグ付き木）で表す。これまで「目視 transcription」
  だった実装エンコードとモデルの対応を**機械検査済みの定理**に格上げ。wire 値型 `WVal`（7 タグ atom ＋ nil/cons）を
  定義し、`Program2DataRwhile.transExp`/`d_exp` を一行ずつ写した**符号器 `encEx : Ex → WVal`** と**パーサ
  `parseEx : WVal → Maybe Ex`**（変数 index は unary nil-count = `d_count` 準拠）を与え、**往復定理
  `parse-enc : parseEx (encEx e) ≡ just e`** を証明（＝検証済み Ex は実装 wire format の復号像）。さらに
  ワークリスト AV 特殊化器の健全性（`avEval-sound`）と合成して **wire レベルの健全性 `wire-sound`／`bridge`**：
  実装のエンコード式から組む AV 残余が γ で元の意味に概念化する。OCaml 側は新テスト群 `wire-bridge`
  （`TestSuite.ml`）が同一 wire 木を `d_exp` で復号し Agda `parseEx` と一致、かつ atom-free 式の `transExp`→`d_exp`
  往復を pin（実装側との相互検証）。
- **Tier-2 #5 工学3（`RWhileH2WorklistStore.agda`）＝partial-static 多スロット store（最後のピース）**：spec_av の
  実ストア `Vl` は独立した AV の列（一部スロットが静的 `S v`、一部が動的）。これを `List AV` でモデル化し、
  スロットアクセスは `cSlot n = cHd (cTl^n cVar)`（AUX/LOOKUP の walk、`cSlot-sound`）、範囲外は動的 `D (cSlot n)`
  に既定。新概念は **整合性 `Consistent s ρ`**（各スロットの AV が runtime store ρ の実スロットに概念化一致＝
  静的スロットは ρ と一致せねばならない）。整合性の下で worklist 残余が **γ 健全**：`γ (avEval s ex) ρ ≡ ⟦ ex ⟧ ρ`
  （`Core.worklist-store-sound`、全 AV 演算込み）。Witness は静的スロット0＋動的スロット1 から部分静的残余
  `C (S vtrue) (D (cSlot 1))` を実際に組み立て、`(vtrue · σ)` 形の任意 runtime store で健全。
  ＝**spec_av の特殊化機構（ループ＋AV全代数＋partial-static 多スロット store＋γ健全性）が機械検証で出揃った**。
- **Tier-2 #5 工学2（`RWhileH2WorklistAV.agda`）＝ワークリストに実 AV 代数＋全演算＋ストア access を搭載**：
  上記ワークリスト機械に `RWhileAVSound` の実 AV 演算（`avCons`/`avHd`/`avTl`/`avEq`/`avPairp`、`'S`/`'D`/`'C`）を
  載せ、式言語 Ex（**store-indexed var**/val/cons/hd/tl/eq/pairp）を辿って **AV 残余を組み立てる**（spec_av の
  SPEC-EXP-AV そのもの）。**ストアアクセス**は `varN n = avNth n (D cVar) = avHd (avTl^n …)`＝spec_av の
  AUX/LOOKUP（store を tl で n 歩いて hd）を既存の `avHd`/`avTl` で再現（追加証明 `avNth-sound`）。マシン関係
  `_⟱_` で `avEval ex` を組むこと（`machine-spec`/`machine-correct`）と燃料版（`machineF` sound/complete/mono）を
  証明し、**健全性** `worklist-spec-sound`：組んだ AV 残余を概念化すると元の具体評価に一致
  （`γ (avEval ex) ρ ≡ ⟦ ex ⟧ ρ`）。Witness は store slot を読む部分静的残余 `C (S vtrue) (avNth 0 (D cVar))` を
  組み立て γ 健全（`vtrue · hd ρ`）。＝**spec_av の looping AV スペシャライザを「ループ機構（ワークリスト＋燃料）
  ＋AV 全代数＋ストアアクセス＋γ 健全性」で機械検証**。残りは partial-static な多スロット store（各スロット独立 AV、
  多穴残余コード）への一般化のみ。
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

## 6. オフライン BTA 設計図（`RWhileOfflineBTA1`–`9`、2026-07-10）＝過剰静的化(2)の解消

案1 の残課題(2)＝過剰静的化の解消（束縛時刻オフライン化）に対し、後戻りしにくい本番改造に先立って
Agda で**設計図を 9 段**機械検査した（全 `--safe`・公理ゼロ、capstone `RWhileMain` に再エクスポート）。
実機 comp2 の live-trace 根本原因は `TRACE_comp2_root_cause.md` を参照。

| 段 | モジュール | 主結果 | 対応する実機事象 |
|---|---|---|---|
| 1 | `RWhileOfflineBTA` | `static-stable`／`over-commit-unsound`／`no-static-identity`／`mkAV-dyn-nonstatic`／`spec2-sound`／`spec2-static` | 過剰静的化＝束縛時刻 congruence 違反。`MKAV` の無条件 `'S`（`spec_av.rwhile:1051`）は自己適用で unsound、修正は BT 駆動 `mkAV` |
| 2 | `RWhileOfflineBTA2` | `spec2g-sound`／`spec2≡spec2g`／`spec2bug-ok-on-static`／`spec2bug-wrong-on-symbolic` | 自己適用段（記号的ソース）。凍結は fp1 で不可視・fp2 で unsound |
| 3 | `RWhileOfflineBTA3` | `gain`／`dispatch-resolved`／`dyn-survives` | 本物の Futamura 利得（静的部分の完全畳込） |
| 4 | `RWhileOfflineBTA4` | `spec1-sound`／`compile-sound`／**`fp2-eq`**／`spec1-keeps-source-symbolic`／`spec1bug-wrong-on-source` | 二段 comp2（fp2 コンパイラ）と第2射影等式 |
| 5 | `RWhileOfflineBTA5` | `gen-sound`／**`fp3-eq`**／`gen-keeps-int-symbolic`／`genbug-wrong-on-int` | 三段 cogen（fp3）と第3射影等式 |
| 6 | `RWhileOfflineBTA6` | `prodThen-car-const`／`prodThen-car-unsound`／`fix-agrees-on-fp1`／`fixThen-car-tracks`／`fixThen-car-nonstatic` | 実機症状 `('val.'swap)`＝静的リーフの `AV-LIFT`↔修正パターン、fp1 無退行 |
| 7 | `RWhileOfflineBTA7` | `spec1-sound`(dispatch込)／`comp-swap`／`comp-id`／`compbug-ignores-opcode`／`compbug-wrong` | ディスパッチ保存（`AV-EQ`:224／'cond 対応）。凍結はディスパッチを潰す |
| 8 | `RWhileOfflineBTA8` | `seq-flatten-ok`／`specOff-sound`／`specOff-keeps-branches`／`specBug-riM`／`specBug-wrong` | **根本原因＝agenda 機構**。seq は agenda 可、動的 cond は per-branch 残余（`Cd<=cons C Cd` :963／SPEC-STEP-AV :877） |
| 9 | `RWhileOfflineBTA9` | `swapV-invol`／`rexec-exec`／`specOff-id`／`specOff-injective`／`specBug-collapses`／`specBug-not-injective` | **可逆性=情報消失なし**。分岐欠落は非単射＝可逆性違反、修正が単射性回復 |

- **強さ**：**設計図（修正の形・fp1 安全性・ディスパッチ保存・agenda 設計規則・可逆性=単射性）を証明**。
  値の束縛時刻（`mkAV`）だけでなく**制御 agenda の offline 化**（動的 cond で片枝 push せず両枝を残余化）が
  必要という設計規則まで含む。実機の agenda offline 化（本番 `SPEC-CMD-AV` の 'cond 動的経路 :972-993 の改造）は
  **未着手**（`gate`/`dyncond`/`comp2-loops` で検証予定）。
- **論文反映済**：overleaf `formal/mechanization.tex` §`sec:agda-offline`（第1–9段を散文で記述、push 済）。
- **全 61 モジュール `--safe` PASS**（`proofs/agda/check.sh`、postulate 0、唯一の仮定は `funext`）。

## 7. 線形時間自己解釈系（`RWhileTime`/`RWhileSI*` 17 モジュール、2026-08-04／08-05）

Glück–Yokoyama「R-WHILE の線形時間自己解釈系」を定理化する層。詳細は `LINEAR_TIME_SI.md`。
**自己解釈系は抽象機械ではなく、対象言語で書かれた 1 本の R-WHILE プログラム**。

| 実装の部品 | Agda 結果 | 強さ |
|---|---|---|
| `EvalRwhile.eval_steps`（`./ri -steps` のコスト） | `RWhileTime`：コスト付き big-step ＋ 燃料付き `exec`/`exec-sound` | **証明**（`incr` と 1 対 1。式は平坦に限定） |
| `Program2DataRwhile.ml`（`-p2d`） | `RWhileSIEnc`：`⌜_⌝`・`encS`・`num`・タグ表（式は `(tag . (o1 . o2))` に一様化）／`RWhileSIP2D`：実装の符号化を Agda でモデル化し **`./ri -p2d` の出力と文字列一致を型検査器が照合**（8 例）、一様符号化への翻訳 `p→u-ok` も証明 | **差分テスト＋翻訳定理** |
| R-WHILE の静的条件（`X ∉ Vars(E)`、変数はストア内） | `RWhileSIWf`：分離則・`NotIn`/`evalE-frame`・`Wf`/`InR`・`⇒-length` | **証明** |
| `ri.rwhile` の主ループ＋`STEP`（todo/done アジェンダ、プログラム保存） | `RWhileSIMach`：`astep`/`step1`・`sim`・`machine-linear`（対象 1 ステップ ≤ **機械 4 ステップ**） | **証明**（実行テスト付き） |
| `ri.rwhile` の `AUX`/`LOOKUP`/`UPDATE`（`Vl` 歩行） | `RWhileSIMac`（汎用 push/pop、コスト 9）・`RWhileSIWalk`（28/セル）・`RWhileSILookup`（**`56k+27`**） | **証明**（実行テストで厳密値を照合） |
| `ri.rwhile` の `EVAL-EXP`/`INV-EVAL-EXP` | `RWhileSIEval`：`opdC`（`56M+36`）・`evalC`（式 5 形、`evalB M = 240M+178`）。compute–use–uncompute で**部分対合**＝同じコードの再実行が逆計算 | **証明** |
| `ri.rwhile` の `STEP` マクロ本体（12 タグ分岐） | `RWhileSIStep`：`STEP` と **12 ケース 17 定理**（`skip`34/`seq`80/`seqE`81/`cond`/`condE`/`loop`54/`lpA`/`lpD`/`lpB`84/`lpZ`57/`lpC`86、各 `astep` 一致つき） | **証明** |
| `InvRwhile.ml`（`./ri -inverse`）※時間付き構文版。§1 の `RWhileRev` とは別の層 | `RWhileTimeInv`：`inv` と**コスト保存の健全性** `c ⊢ σ ⇒ τ ∣ k → inv c ⊢ τ ⇒ σ ∣ k`（同じ `k`）、`rupd` の部分対合性、`inv-inv`、`Wf`/`InR` の保存 | **証明**（往復の実行テスト付き） |
| 逆プログラムの解釈 | `RWhileSIInv`：`si-inverse-linear`／`si-round-trip` — **同じ `SI`・同じ定数で両方向が線形時間** | **証明** |
| プリンタの忠実性 | `RWhileSIParse`：トークン列の構文解析器と往復定理（値・オペランド・式）。`;` は印字が平坦化するため**結合の付け替えを除いて**一致し、`seq-assocʳ/ˡ` で意味論・歩数とも保存されることを証明。命令レベルも `round-trip : ∀ c → RN c → pC … (tokC c []) ≡ just (c , [])` として**全 `Cmd` について証明済み**（`RN` は `;` の右結合＝括弧の付き方の指定で、`seq-assoc` により意味論・歩数とも不変） | **証明** |
| 逆向きの完全性 | `RWhileSIComplete`：**証明済み**＝`si-halts→todo-empty`（停止時 todo は空）・`si-answer`（停止した `SI` は誤答しない）。**未証明**＝`SiComplete`（`SI` 停止 ⇒ 対象停止）。デコード不変量が要る旨を型と docs に明示（postulate ではない） | **部分的** |
| 燃料付き評価器 | `RWhileTimeExec`：`exec-mono`／`exec-complete`（`exec-sound` と合わせて関係と評価器が完全一致）。停止しない実行は「どの燃料でも `nothing`」として特徴づけ（無限ループと行き詰まりは区別しない） | **証明** |
| 意味論の決定性 | `RWhileTimeDet`：`⇒-det`／`Rest-det`（ストアもステップ数も一意）。`RWhileSIDet.si-unique` で「`SI` のどの停止実行も正しい答え・上界内」に強化 | **証明** |
| 解釈系そのものの可逆性 | `RWhileSIInv.si-uncompute`：`inv SI` が解釈を**同じ歩数で**巻き戻す。静的条件は `RWhileTimeDec` の決定手続きで評価により discharge | **証明** |
| `ri.rwhile` をプログラムとして見た実行時間 | `RWhileSISim`：**`si-linear`（無仮定）** `j ≤ (CC M + 2)·k`、`CC M = 2940·M + 3184`。合成 `simP`/`simPR`＋算術 `RWhileSIArith`／モジュラ版は `RWhileSIProg` | **証明** |

- **ギャップ G7 は解消（2026-08-04）**: `RWhileSISim.simP`/`simPR` が完成し、定理は
  **無仮定で閉じた**。`SI` は固定された 1 本の R-WHILE プログラムで、終了時に done スタックへ
  `⌜c⌝` を組み立て直す（プログラム保存）。定数はストアのセル数 M に affine。
- **形式化の実務的教訓**: 合成で `with` 抽象を使うと機械状態の巨大な型がゴールに複製され、
  型検査が 44 GB を消費して OOM になった（`where`＋明示射影で 400 MB→最終 9.7 GB・92 秒）。
  上界の算術は別モジュールに分離し、`C * k` 形の結論をもつ補題は `C`・`k` を明示的に渡す。
- **設計上の知見**（形式化して初めて判明）: ループの入口テスト `e` は **`D` の実行前**に評価しなければ
  ならない。さもないと「初回到達か」の 1 ビットが可逆に消去できず、`astep` が非単射になり
  R-WHILE プログラムとして実装不可能になる。`ri.rwhile` が `'l1E` で `EVAL-EXP(E)` してから
  `CC ^= C` する構造は、この必然性の反映である。
- **スコープ**: 式は平坦（オペランド＝変数/定数）、`<=` は対象言語に含めない。可逆制御構造 4 種と
  `rupdate` は `EvalRwhile.ml` どおり。解釈系は対象プログラムのループ表明・条件文の出口表明を実際に検査する。
- **全 90 モジュール `--safe` PASS**（`proofs/agda/check.sh`、postulate 0、穴 0）。

## `rupdate` の第 3 の場合（2026-08-05 に形式化へ追加）

### 何が抜けていたか

`src/EvalRwhile.ml` の `rupdate` は **3 つ**の場合を持つ。

```ocaml
if vy = VNil then vx          (* 1. 空きスロットに置く   *)
else if vx = vy then VNil     (* 2. 同じ値なら消す       *)
else if vx = VNil then vy     (* 3. 右辺が nil なら恒等  *)
else error
```

ところが `RWhileValStore.RAss` の `toggle` と `RWhileExecConcrete.rupdF` は
**1 と 2 しか持っていなかった**（`RWhileExecConcrete` の冒頭は
"mirrors the OCaml `rupdate`" と書いていたが、写せていなかった）。

原因はおそらく、形式化が**実装ではなく論文を写した**こと。論文の ⊙ の定義は
2 つの場合しか挙げない — Glück & Yokoyama, *A linear-time self-interpreter of a
reversible imperative language*, Computer Software 33(3), 2016 の Eq.(8)、および
R-CORE 論文（IEICE E100-D(5), 2017）の Eq.(1) が同じ 2 場合である。

### なぜ重大か

**`examples/ri.rwhile` が第 3 の場合に依存している。** ループ処理の分岐に

```
Flag ^= =? Tag 'l4E; Flag ^= =? Tag 'loop;
```

とある。これは `Flag := (Tag='l4E) ∨ (Tag='loop)` の定型句で、`Tag = 'l4E` のとき
2 つ目が `Flag ^= nil`（`Flag` は既に true）になる。つまり
**この形式化の可逆性定理は、このリポジトリの中心的な成果物である自己解釈器を
覆っていなかった**。

（`program2data` が空枝を `X₁ ^= nil` と符号化することでも第 3 の場合が要る。
素の R-WHILE でも `read X; X ^= nil; write X` に `(nil.nil)` を与えると恒等写像として通る。）

### 追加しても壊れないこと

`toggle` に `(v ≡ nil × σ' x ≡ σ x)` を足した。この選択肢は σ と σ' について
**対称**なので、`RAss-sym`（部分対合）の証明は元と同じ形で通る。
`RWhileDetConcrete.RAss-atx`（決定性）は 3×3 の 9 節に増えるが、
どの組合せも「両辺とも nil に落ちる」ことを等式の連鎖で示すだけである。
`rupdF` も OCaml と同じ順で 3 分岐にし、`rupdF-sound`/`rupdF-complete` を
それぞれ 1 節ずつ増やした。

拡張が可逆性を保つことは独立にも確かめてある（`jones-agenda` 側）:
全数検査で定義される対が 45 → 67 に増え、単射性・対合性・ストア上の可逆性は
どちらの版でも成立、**定義域が d と e について対称なのは 3 場合の版だけ**。

### 未修正: 線形時間 SI 層に同じ欠落が残っている（2026-08-05 に発見）

上の修正は `RWhileValStore` / `RWhileDetConcrete` / `RWhileExecConcrete` の層だけ
だった。**`RWhileTime.agda` の `rupd` は依然として 2 場合しかない**:

```agda
-- The reversible update `x ^= e` (src/EvalRwhile.ml `rupdate`):
-- assigning to a nil variable sets it; assigning its current value clears
-- it; anything else is a run-time error (partial involution).
rupd : V → V → Maybe V
rupd nil     v = just v
rupd (atm m) v = if eqV (atm m) v then just nil else nothing
rupd (a ∙ b) v = if eqV (a ∙ b) v then just nil else nothing
```

コメントは「それ以外は実行時エラー」と**断定している**が、実装はそうではない。
同じ原因（論文の ⊙ を写した）で同じ誤りが新しい層に再発している。

実機で確認できる差:

```
$ ./ri -steps <(printf "read X; Y ^= 'a; Y ^= nil; Y ^= 'a; write X\n") b.val
'b
[RWHILE-STEPS] steps=5          <- OCaml は通る（中央は恒等）
```

Agda モデルでは中央の `Y ^= nil` が `rupd (atm a) nil = nothing` でスタックする。
`src/Core.ml` は `EvalRwhile.rupdate` をそのまま呼ぶので、`./ri` と `./ri -core`
の間にずれはない。**ずれは Agda モデルと実装の間だけ**である。

#### 向きと影響

Agda で定義される場合は実装でも定義され、値も一致する（1 と 2 はそのまま、
`rupd nil nil = just nil` も実装の第 1 分岐と一致）。したがって

- **健全性は保たれる**: `c ⊢ s ⇒ t ∣ k` の導出はすべて本物の実行に対応する。
- **完全性は主張できない**: 実装が受理する実行のうち、第 3 の場合を使うものには
  導出が存在しない。`si-linear`・`inv-sound`・`⇒-det` などはいずれも
  「第 3 の場合を使わない断片」についての定理と読むべきである。

上の節が指摘したとおり `examples/ri.rwhile` は第 3 の場合に依存する
（`Flag ^= =? Tag 'l4E; Flag ^= =? Tag 'loop`）ので、**この断片は実物の
自己解釈器を覆っていない**。線形時間の主定理は Agda 内で構成した `SI` について
のものなので定理自体は無傷だが、「実装の自己解釈器を検証した」とは言えない。

なお `Desugar.ml` が `local`/`for` に入れた `assert (=? X nil)` ガードは、
ブラケットを**第 3 の場合が起きない領域に閉じ込める**（X が nil であることを
入口で強制するので `X ^= E` は必ず第 1 分岐）。偶然だが、糖衣はモデル化済みの
断片の中に収まっている。

#### 直すときの範囲

`rupd` に `rupd u nil = just u` を先頭で足す。恒等なので対合性は保たれる
（`rupd (rupd u nil) nil = u`）。影響を受けるのは `rupd` を直接扱う 4 モジュール:

| ファイル | `rupd` の出現 |
|---|---|
| `RWhileTime.agda` | 12（定義・`rupd-self`・`e-ass`） |
| `RWhileTimeInv.agda` | 11（`rupd-invol` など） |
| `RWhileTimeDet.agda` | 2 |
| `RWhileTimeExec.agda` | 1 |

`RWhileTime` を import するモジュールは 27 あるので、`check.sh --si` の全体再検査
が要る。

**素朴に先頭へ 1 節足してはいけない。** `rupd w nil = just w` を先頭に置くと
`rupd nil v` が開いた `v` に対して簡約しなくなる（Agda は第 1 節のパターン `nil`
に当たるかを先に決められないため）。既存の証明はこの簡約に依存している。
**第 2 引数で分割し直して重なりを消す**こと:

```agda
rupd : V → V → Maybe V
rupd w       nil     = just w                                  -- 第 3 の場合（恒等）
rupd nil     (atm n) = just (atm n)
rupd nil     (a ∙ b) = just (a ∙ b)
rupd (atm m) (atm n) = if eqℕ m n then just nil else nothing
rupd (atm m) (_ ∙ _) = nothing
rupd (a ∙ b) (atm _) = nothing
rupd (a ∙ b) (c ∙ d) = if eqV (a ∙ b) (c ∙ d) then just nil else nothing
```

見通し:

- `rupd-self`（**191 箇所**で使われる最重要補題）は新定義でもそのまま通る。
  `rupd-self nil` は第 1 節で `just nil`、`atm`/`∙` は従来どおり `eqℕ-refl` /
  `eqV-refl` で潰れる。ここが壊れないので大半の利用箇所は無傷である。
- `rupd-invol` は `v` が nil かどうかで場合分けを 1 段増やす。`v ≡ nil` の枝は
  `u ≡ w` なので `refl`、それ以外は既存の証明がそのまま入る。
- 実質の書き換えは `rupd` を直接分解している `RWhileTimeInv` の 11 箇所と
  `RWhileTimeDet` の 2 箇所、`RWhileTimeExec` の 1 箇所に限られる見込み。
- `exec` は `rupd` を呼ぶだけなので定義の変更に追随する。

### 直した範囲

| ファイル | 変更 |
|---|---|
| `RWhileValStore.agda` | `RAss.toggle` を 3 択に。`RAss-sym` を 3 節に |
| `RWhileDetConcrete.agda` | `RAss-atx` を 9 節に |
| `RWhileExecConcrete.agda` | `rupdF` を 3 分岐に。`rupdF-sound`・`rupdF-complete` に 1 節ずつ追加 |

`Extract.agda` は `rupdF` を呼ぶだけなので変更なし。`--safe`・postulate 0 は維持。
