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
| `Simp.program_preserving`（p⁺ の構成）／`measure_proj jones-self` の判定基準 | `RWhileProgPres`(`pp-sem`/`pp-cost`/`pp-cost-exact`)・`RWhileProgPresRev`(`pp-rev`/`pp-injective`)・`RWhileProgPresMin`(`ext-not-classical`/`ext-lb`)・`RWhileJonesRev`(`residual-pp`/`pp-unique`)・`RWhileJonesRevCE`(`p⁺-not-minimal`) | **定義の側は証明**（p⁺ の意味論・定数オーバヘッド・可逆性・単射性、基準の含意関係）。**測定（7 被験の成否）は実機のまま**。下界は「p の拡張の中で」の形に限る（一般の最小性は**反証済み**） |
| `EvalRwhile.eval_work`／`eq_work`（`./ri -work` の費用モデル、課金 3 か所） | `RWhileWorkV`(`eqW`/`eqVW-≡`/`eqW-refl`/`eqW-mismatch`/`rupdW`)・`RWhileWork`(`_⊢_⇒_∣_∥_`/`expW`/`⇒w-steps`/`wk-sound`)・`RWhileWorkDet`(`⇒w-det`)・`RWhileProgPresWork`(`pp-work`/`work-not-constant`)・`RWhileProgWork`(`pp-progW-ocaml`/`measured-law`)・`RWhileJonesRevWork`(`⁺-cost`/`rev-unfold`/`classical⇒rev-work`) | **証明**（費用モデル・短絡・決定性・p⁺ の work コスト `work(p)+\|⌜p⌝\|+1`）。**実測 11 行との一致は Agda 内で `refl` 照合済み**（`measured-law`）。残る隙間は下記「正直な範囲」 |
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

## 表層言語 R-WHILE-S と compile-sound（`RWhileSurface.agda`、2026-08-06）

`src/Desugar.ml` は糖衣を**展開によって定義**しているので、「脱糖は正しい」は
そのままでは空虚な主張になる。そこで表層の各構文に**独立した意味論**を与えた —
プログラマが述べるであろう規則、`if/fi` ではなくストアの言葉で書いたもの — その上で
コンパイルがちょうどその規則を実現することを証明した。

```agda
data _⊩_⇒_∣_ : SCmd → Store → Store → ℕ → Set where
  s-assert : evalT s e ≡ just true → assert e ⊩ s ⇒ s ∣ 2
  s-local  : get s x ≡ nil            -- X は入口で空いている
           → evalE s e ≡ just v       -- E の値が
           → c ⊩ set s x v ⇒ u ∣ k    -- 本体が見るもの
           → evalE u f ≡ just w
           → get u x ≡ w              -- F は X が保持する値を名指す＝それが消去する
           → localD x e c f ⊩ s ⇒ set u x nil ∣ bcost k
```

| 定理 | 主張 |
|---|---|
| `compile-sound` | 表層の実行はすべて、コンパイル結果の**同じコストの**実行である |
| `compile-complete` | 逆も成り立つ。コンパイル結果には表層で説明できない実行が無い |
| `compile-cost` | 両者と `⇒-det` から、ストアもコストも完全に一致する |
| `bcost≡` | ブラケットのコストは本体 k に対して `10 + k` |
| `for-counter-local` | `for` のカウンタが前後で nil であることは**ループ帰納を一切使わず**ブラケットの定理から出る |
| `incr-restores-scratch` | カウンタ段 `<X++>` は X をちょうど nil 1 つ分伸ばし、**一時変数 T を nil に戻し**、コストは 7 |

| `rest-exits-at` / `loop-exits-at` | 何周したかによらず、脱出テストが `=? X B` のループは **X = B で止まる**（`Rest` の帰納。本体への仮定は一切不要） |
| `loop-body-runs` | 本体は**少なくとも 1 回**走る（`e-loop` が `Rest` を見る前に D を走らせるので、`for X = A to A` でも実行される） |
| `for-iter-step` | 本体がカウンタを触らないなら、1 周でカウンタは**ちょうど nil 1 つ分**伸び、一時変数は nil に戻る |
| `caseNest-cost` | `case` の腕 i に到達する手間は**ちょうど i**（飛ばした腕 1 つにつき条件分岐ノード 1 つ）。`./ri -steps` の実測（2/3/4 腕の最終腕で 8/9/10 歩）と一致 |
| `caseNest-exits-false` | 飛ばした腕の**出口表明はすべて最終ストアで偽**でなければならない。これが `Desugar.ml` の「出力パターンの判別子は互いに素」検査の形式的内容であり、検査が省けない理由 |

`loop-exits-at` はカウンタが最後に nil になる**理由**を与える。ループが X = B を
残すので、閉じ側の `X ^= B` が消去になる。従来は出口の表明からしか分かっていなかった。
`loop-body-runs` と `for-iter-step` は `src/Desugar.ml` が散文で書いていた
「本体は少なくとも 1 回走る（A = B なら 1 回）」「カウンタはループ局所」を定理にした
ものである。`for-iter-step` の前提「本体がカウンタを触らない」は、2026-08-06 に
実測で沈黙する誤答を見つけて脱糖時の検査にした条件そのもの。

`incr-restores-scratch` は `src/Desugar.ml` の主張を定理にしたものである。同ファイルは
「一時変数は増分の内側で設定・消去されるので前後で nil であり、割り込む余地がない。
だから複数の展開で 1 つの一時変数を共有しても安全」と書いている。T が nil に戻ること
を証明したので、この共有の根拠が形式化された（2026-08-06 の `FOR-T-n` 衝突修正で
実際に依拠した性質でもある）。証明は「実行を 1 本構成して `⇒-det` で任意の実行へ
移す」型で、`compile-cost` と同じ手口。

補助として `rupd-clear : ∀ q v → rupd q v ≡ just nil → q ≡ v`（消去できたのなら
与えた値は変数自身の値だった）を証明した。これは `rupd` の第 3 分岐を入れた後の
形でも成り立つ。

### 範囲の限界（記録しておくべき事実）

タイムド核 `RWhileTime` の命令は `skip` / `^=` / `;` / `if-fi` / `from-until` の
5 つで、**パターン置換 `<=` が無い**。したがって `<=` に展開される糖衣
（`X <-> Y`・`push`・`pop`）は**この層では時間つき意味論を与えられない**。それらは
`RWhileCRep.agda` が `<=` をモデル化している別の層に属する。`case` も同様に
`RWhileCaseInv.agda` が既に扱っている（脱糖後の入れ子条件分岐について「case の逆は
また case」「腕の入れ替えが対合」）。

つまり糖衣 7 形の形式化の現状は:

| 糖衣 | 状態 |
|---|---|
| `local`/`delocal` | **証明済み**（`RWhileSugar` + `RWhileSurface`） |
| `for` | **カウンタの局所性を証明済み**。ループ本体の意味論は未 |
| `assert` | **証明済み** |
| `skip` | タイムド核の `skip` そのもの（コスト差は `cost-split` が説明） |
| `push` / `pop` / `X <-> Y` | **証明済み**（`RWhilePushPop.agda`、`RWhileCRep` 層） |
| `case` | 反転は `RWhileCaseInv`、選択コストと出口表明の役割は `RWhileSurface.caseNest-cost` / `caseNest-exits-false`、**腕本体まで含めたコストは `RWhileCaseCost.agda`**（2026-08-09。下記） |

`--safe`・postulate 0・hole 0。`check.sh --si` は PASS=30 FAIL=0（181 秒）。

## 可逆版 Jones 最適性と p⁺（`RWhileJonesRev*` / `RWhileProgPres*` 5 モジュール、2026-08-09）

`./measure_proj jones-self` が使う判定基準そのものを機械検証した。**測定（work で
7/7 成立・steps で不成立）は実機のままで、ここで検証したのは「定義の側」**である。

### なぜ基準を動かすのか（`RWhileJonesRev`）

可逆 Futamura 射影は**プログラム保存**インタプリタ
`⟦rint⟧ ⟨⌜p⌝,d⟩ = ⟨⌜p⌝, ⟦p⟧ d⟩` を要求する。だから fp1 残余
`⟦spec⟧(rint, ⌜p⌝)` にも「元プログラムを出力する」義務が伝播する。素の `p` は
その仕事をしないので、古典的な `残余 ≤ p` は**射影の定義を測っているだけ**になる。

抽象層（データ・プログラム・意味・コスト・符号化・対をすべてパラメタ化した
`Criterion` モジュール）で証明したのはこの伝播そのものである。

| 定理 | 内容 |
|---|---|
| `Fp1.residual-pp` | 射影の 2 本の定義式（`def-rint`/`def-spec`、`RWhileRevProjPaper` と同じ形）だけから、**fp1 残余が義務 `PP` を継承する**。基準側も同じ義務を負わねばならない理由 |
| `pp-unique` | 義務は**関数を一意に決める**（`PP q₁ p → PP q₂ p → ⟦q₁⟧ ≗ ⟦q₂⟧`）。したがって義務を負う 2 本を比べる作業に残る自由度は**コストだけ**＝Jones 流の比較が成立する |
| `Fp1.basis-adequate` | 残余と任意の `PP` 基準は同じ関数を計算する。`残余 ≤ p⁺` は**同じ仕様の 2 実装**の比較、`残余 ≤ p` は**違う仕様**の比較 |
| `pp-injective` / `Fp1.residual-injective` | `p` が単射なら p⁺ も残余も単射（可逆性の側） |
| `classical⇒rev` / `rev-mono` | 基準が `p` 以上なら古典版は可逆版を含意する |

### p⁺ の構成・意味論・コスト（`RWhileProgPres`）

`src/Simp.ml: program_preserving` を**タイムド核**（`RWhileTime`、`./ri -steps` と
同じ「実行した命令ノード 1 個 = 1」）の上で構成した。スロット添字 `y`（p の出力）・
`self`（`P-SELF`）・`out`（`OUT-PP`）と `pd = ⌜p⌝` でパラメタ化してある。

| 定理 | 内容 |
|---|---|
| `pp-sem` | p の本体が σ→τ（答えは `y`、`self`/`out` は nil）なら、p⁺ は `out = (⌜p⌝ . 答え)`・`self = nil`・`y = nil` に至る。**`all_cleared` のストア不変条件が生き残る**（＝R-WHILE のプログラムとして合法） |
| `pp-cost` | そのコストが `cost(p) + 8`。**入力に依らない定数**オーバヘッド |
| `pp-cost-exact` / `pp-store-exact` | 決定性より、それが唯一の走り方（上界ではなく等式） |
| `final-frame` | emit は他のスロットを一切触らない（ゴミを増やさない） |
| `Examples.run-pp-exec` | 具体例（1 命令の p）を**型検査器の中で `exec` に流し** 9 = 1+8 歩を確認 |

### p⁺ は可逆（`RWhileProgPresRev`）

`RWhileTimeInv` のコスト保存反転を使う。`inv (body ⨾ emit) = inv emit ⨾ inv body`
なので、emit を先に巻き戻して p の答えを `y` に戻し、次に p 自身を巻き戻す。
emit の 4 命令はすべて XOR 代入＝自己逆なので追加コストはない。

| 定理 | 内容 |
|---|---|
| `emit-Wf` / `pp-Wf` | `X ^= E` が X を含まない（R-WHILE の整形式条件）。**p が整形式なら p⁺ も整形式** |
| `InR-emit` / `InR-pp` | 2 つの新スロットが確保されていれば p⁺ もストア内に収まる |
| `pp-rev` | **`inv(p⁺)` が p⁺ の出力を入力へ戻す。コストはちょうど同じ `k+8`** |
| `pp-injective` | p⁺ は 2 つの入力を 1 つのストアへ潰さない（反転＋決定性から） |

### p⁺ の「最小性」はどこまで言えるか（`RWhileProgPresMin` / `RWhileJonesRevCE`）

依頼にあった「義務を果たす任意のプログラムのコストは p⁺ 以上」という下界は
**一般には成り立たない。反例を機械検証してある**（`RWhileJonesRevCE.p⁺-not-minimal`）。

理由は構造的である。義務 `PP q p` は**外延的**（計算する関数を固定する、`pp-unique`）
のに対しコストは関数から決まらない。`p` が無駄をしていれば、同じ関数をもっと安く
計算する `q` が存在しうる。p⁺ の最小性を主張することは、**任意の計算可能関数
`⟨⌜p⌝, ⟦p⟧ ·⟩` に対する計算量の下界**を主張することであり、射影の定義からは出ない。

代わりに成り立つのは「**p の拡張の中での**最小性」で、こちらは証明した。

| 定理 | 内容 |
|---|---|
| `ext-cost` | `p ; e` の走りは必ず `cost(p) + 2` 以上（`⨾` ノード 1 ＋ 空でない後続 1） |
| `ext-not-classical` | ゆえに **p を走らせてから何かする残余は、古典的基準 `残余 ≤ p` を原理的に満たせない**。基準を動かさざるを得ない形式的理由 |
| `cost1-one-slot` | コスト 1 の走りが書き換えるスロットは高々 1 個 |
| `two-slots-cost` | ゆえに 2 スロットを書き換える走りはコスト 2 以上 |
| `ext-lb` | 出力スロットを埋め、かつ p の答えスロットを消す義務を負う後続をもつ拡張は `cost(p) + 3` 以上 |
| `gap` / `+8-not-≤` | p⁺ が払う `+8` はその下界から**加法的に 5 以内**。そして常に定数であって係数ではない |
| `RWhileJonesRevCE.resid-not-classical` | 可逆版が古典版を**含意しない**（逆向きは `classical⇒rev` で成立）。両基準とも空虚でないことも確認 |

### 正直な範囲（この形式化が言っていないこと）

- **定数 8 は最適とは主張しない**。厳密な最適値は 4 命令形にわたる小さな合成問題で、
  そもそも下のモデル差に飲まれる。
- **`CRep` のモデル差**。OCaml の emit は `CAss` 1 本＋置換 `CRep (OUT-PP, cons P-SELF Y)`
  1 本だが、タイムド核に `<=` は無いので**平坦な `^=` 4 本**で同じ効果を出している
  （`self` を置く → 対を `out` に組む → `self` を XOR で消す → `y` を `tl out` で消す）。
  どちらもストアを綺麗に戻し、どちらも定数を足す。**違うのは定数の値だけ**（モデル 8、
  実機 `-steps` は 4）。定理が主張しているのは**定数性**であって 8 ではない。
  `RWhileCaseCost` が置換をタイムド核へ翻訳した路線を使えばこの差は詰められるが、
  そこは未着手。
- **抽象層と具象層は橋渡ししていない**。`Criterion` は全域の `⟦_⟧ : P → D → D` を
  要求するのに対し、タイムド意味論は関係（部分的）である。Maybe 持ち上げは未。
  したがって「R-WHILE の p⁺ が `Criterion` の `PP` を満たす」は**両層で別々に
  述べてあるだけ**で、1 本の定理にはなっていない。
- ~~**測定は形式化していない**~~ **→ 2026-08-09 に `-work` 側を追加した**（下節
  「`-work` 指標のコストモデル」）。`RWhileTime` の ℕ が `-steps` の側なのは変わらず、
  work は**別の注釈として加算的に**足してある（`RWhileTime.agda` は無改変）。

`--safe`・**postulate 0・hole 0**。`check.sh` は **PASS=108 FAIL=0**（5 分 00 秒、
最大 532 MB）。**work 層 6 本を足して PASS=114**（下節）。

## `case` のコストを腕本体まで（`RWhileCaseCost.agda`、2026-08-09）

上の表で `case` だけが「腕本体は不透明」と残っていた。理由は「腕本体は `<=` を
含み、タイムド核には `<=` が無い」——**層をまたぐ必要があると思われていた**。
実際には、またぐ必要はなかった。**平坦なパターンの置換はタイムド核で定義できる**:

```
Y <= X          ==  Y ^= X ; X ^= Y                        コスト 3
cons A B <= X   ==  A ^= hd X ; B ^= tl X ; X ^= cons A B  コスト 5
X <= cons A B   ==  X ^= cons A B ; A ^= hd X ; B ^= tl X  コスト 5
```

いずれも R-WHILE 自身の常用イディオムであり、新しい意味論を足していない。

| 定理 | 内容 |
|---|---|
| `movePat-run` / `splitPat-run` / `joinPat-run` | 各置換がストアを所定の位置へ移し、コストがちょうど 3 / 5 / 5 |
| `split-join-restores` | 分解して組み直すと**全変数が元の値に戻る**（コスト 11）。R-WHILE が `<=` を「パターンを入れ替えて」反転することの意味論版。**等式ではなく各点で述べている**のは `set` が短いストアを nil で伸ばすため（`s = []`・`a = 0` で propositional 等式は偽） |
| `caseNest-cost-taken` | **腕 i が選ばれたとき**の選択コストがちょうど i（既存の `caseNest-cost` は素通り側のみ） |
| `swapArm-run` / `caseSwap-run` | `examples/case_swap.rwhile` の cons 腕が実際に入れ替え、`case` 全体でコスト 12 |
| `ex-swap` / `ex-arm` / `ex-split-join` | 上を**型検査器の中で実行**して確認（`exec`） |

**範囲**: 平坦なパターン（変数、または変数 2 つの cons）。**入れ子パターンは一時変数
なしにはこの形へコンパイルできない**——特殊化器が `cons (cons V1 V2) St <= St` で
ぶつかったのと同じ壁（`examples/spec_av.rwhile` のノート）。意図的な境界である。

**コストの約束**: ここの数はコンパイル後の形の費用で、`./ri -steps` の数（`case_swap`
は 6）とは違う。解釈器は `<=` 1 つを 1 ノードで数え、モデルは 3 か 5 使う。表層と核の
いつもの差（`RWhileSugar.assertNil-cost` はモデル 2・解釈器 1）で、隠さず明記してある。
一致するのは**法則の形**——選択＋腕、飛ばした腕 1 つにつき 1 ノード。

変異注入で確認済み（コストを 12→13 にすると `11 != 12`、線形性条件 `a ≠ b` を落とすと
3 か所が落ちる）。

## `<=` に展開される糖衣 push / pop / `<->`（`RWhilePushPop.agda`、2026-08-06）

タイムド層に置けない 2 つの糖衣を、`<=` をモデル化している `RWhileCRep` 層で形式化
した。

```agda
pushC x s = crepC (pvar s) (pcons (pvar x) (pvar s))                  -- S <= cons X S
popC  x s = crepC (pcons (pvar x) (pvar s)) (pvar s)                  -- cons X S <= S
swapC x y = crepC (pcons (pvar x) (pvar y)) (pcons (pvar y) (pvar x)) -- cons X Y <= cons Y X
```

| 定理 | 主張 |
|---|---|
| `push-pop` / `pop-push` | 互いに逆。**独自の反転規則を一切持たない** |
| `push-sem` | S は `(X . S)` になり、X は nil に残る |
| `pop-sem` | pop は積みを**分解**する: `σ S ≡ cons (σ' X) (σ' S)` |
| `pop-needs-nil` | pop が走るのは X が事前に nil のときだけ |
| `swap-inv` | `X <-> Y` の逆は `Y <-> X`。これもパターン入れ替えそのもの |
| `swap-sem` | X と Y は実際に値を交換する |
| `swap-frame` | それ以外のストアは動かない |

`push-pop` / `pop-push` は `crep-reversible` そのものである。R-WHILE は `q <= r` を
**2 つのパターンの入れ替え**で反転し、push と pop はまさに互いの入れ替えなので、
他に何も要らない。`src/Desugar.ml` がこの 2 つに反転規則を与えていないことの、
これが理由である。

`pop-needs-nil` は `push-sem` の「X は nil に残る」と対になっていて、
`push X S ; pop X S` が単に型が付くだけでなく**打ち消し合う**理由になっている。

2 変数は異なる必要がある（`S <= cons S S` は S を 2 回読む）。実装は
`Desugar.ml` で拒否し、ここではパターンの線形性が禁じている。

`--safe`・postulate 0・hole 0。

## 糖衣のガード付きブラケット（`RWhileSugar.agda`、2026-08-06）

`src/Desugar.ml` が `local`/`delocal` と `for` のカウンタを展開する形

```
assert (=? X nil) ;  X ^= E ;  C ;  X ^= F ;  assert (=? X nil)
```

を形式化し、**2 つの表明が飾りではないこと**を証明した。

（**訂正**: 当初これを「糖衣で初めての Agda 対応物」と書いたが誤り。`case` は
`RWhileCaseInv.agda` が既に扱っており、脱糖後の入れ子条件分岐について
「case の逆はまた case」「腕の入れ替えが対合」を証明済みである。正しくは
**タイムド層（`RWhileTime`）で初めての糖衣**、かつ `local`/`for` について初めて、
である。）

証明したもの:

| 名前 | 主張 |
|---|---|
| `bracket-needs-nil` | 実行が存在するのは入口で X が nil のときだけ |
| `bracket-clears` | 出口でも X は nil に戻っている |
| `bracket-binds` | 本体は `set s x v`（v は E の値）から始まる＝ローカルは**束縛**されていて、トグルではない |
| `no-dirty-run` | ガード付きの形は、X が既に束縛されたストアからは**実行が存在しない** |
| `bracket-wf` | 本体が Wf で E・F が X を含まなければブラケットも Wf（`local X = E` の自然な条件） |
| `bracket-inv-cost` | `inv-sound` の系。逆が同じコストで戻る |

**バグを型検査器の中で走らせた。** X を変数 0、Y を変数 1、本体を `Y ^= X`（本体が
何を見たかが答に残る）として:

```agda
ex-clean : exec 10 unguarded (nil ∷ nil ∷ []) ≡ just (nil ∷ atm 1 ∷ [] , 5)
ex-dirty : exec 10 unguarded (atm 1 ∷ nil ∷ []) ≡ just (atm 1 ∷ nil ∷ [] , 5)
```

どちらも `refl`。**同じプログラム・同じコストで答が違う**（Y が `'a` か nil か）。
X が既に `'a` を持っていると開き側の `X ^= 'a` が設定ではなく消去になり、本体は
X = nil を見て、閉じ側が元の値を戻すためエラーも出ない。2026-08-05 に実機で見つけた
誤りそのものである。ガード付きの `guarded` は同じ汚れたストアから**実行が存在しない**
（`no-dirty-run`）。

補助的に `assertNil-cost` で表明のコストがモデルでは 2 であることも示した。実装は
1 しか課金しない（R-WHILE の文法は空枝を印字するが、モデルは `skip` を書かねば
ならない）。これは既知の差で `RWhileTimeSkip.cost-split` が説明する。

`--safe`・postulate 0・hole 0。`check.sh --si` は PASS=29 FAIL=0。

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

### 線形時間 SI 層に残っていた同じ欠落（2026-08-05 発見・同日修正）

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

#### 直した内容（PASS=27 FAIL=0）

**第 2 引数で分割し直す設計は失敗した。** `rupd w nil = just w` を先頭に置くと
`rupd nil v` が開いた `v` に対して簡約しなくなる（Agda は第 1 節のパターン `nil`
に当たるかを先に決められない）。`RWhileSIMac` / `RWhileSIStep` / `RWhileSIEval`
には `rupd nil <開いた値> ≡ just _` を `refl` で閉じている証明が多数あり、
27 モジュール中 **12 が落ちた**。

採用したのは、**第 1 節を温存して第 3 の場合を非 nil 側の 2 節の内側に足す**形
（実装の分岐順と同じ）:

```agda
rupd nil     v = just v                                 -- 1. 空きスロットに置く
rupd (atm m) v = if eqV (atm m) v then just nil         -- 2. 同じ値なら消す
                 else if eqV v nil then just (atm m)    -- 3. 右辺が nil なら恒等
                 else nothing
rupd (a ∙ b) v = if eqV (a ∙ b) v then just nil
                 else if eqV v nil then just (a ∙ b) else nothing
```

- `rupd nil v` の簡約が保たれるので下流の `refl` が無傷。
- `eqV v nil` を使ったので `eqV-sound` がそのまま再利用できる。
- `rupd (atm m) (atm n)` と `rupd (a ∙ b) (c ∙ d)` は `eqV (atm n) nil = false`
  等が定義的に潰れて**元と同じ形**に戻るため、`rupd-invol` の該当節は元の証明の
  ままでよい。
- `rupd-self`（**191 箇所**で使われる最重要補題）は**無修正**で通る。
- 追加した補助補題は `rupd-nil : ∀ w → rupd w nil ≡ just w` の 1 つだけ
  （`rupd` は第 1 引数で分割するので `rupd w nil` は開いた `w` で簡約しない）。
- `rupd-invol` に `v ≡ nil` の枝が 1 つ増えた。そこは `u` が `w` そのものなので、
  「写像が自分自身の逆である最も安い理由」で済む。
  `rupd (atm _) (_ ∙ _)` と `rupd (_ ∙ _) (atm _)` は定義的に `nothing` に潰れる
  ので `with` が不要になり、節はむしろ簡単になった。
- `RWhileTimeDet` / `RWhileTimeExec` は `rupd` を場合分けしていない（`cong` の
  引数に置くだけ）ので**変更不要**だった。

変更したのは `RWhileTime.agda` と `RWhileTimeInv.agda` の 2 ファイルのみ。
`check.sh --si` は **PASS=27 FAIL=0**（275 秒）。`--safe`・postulate 0 は維持。

これで `si-linear`・`inv-sound`・`⇒-det` はいずれも第 3 の場合を含む断片について
の定理になり、`examples/ri.rwhile` の論理和イディオムもモデルの内側に入った。

### 直した範囲

| ファイル | 変更 |
|---|---|
| `RWhileValStore.agda` | `RAss.toggle` を 3 択に。`RAss-sym` を 3 節に |
| `RWhileDetConcrete.agda` | `RAss-atx` を 9 節に |
| `RWhileExecConcrete.agda` | `rupdF` を 3 分岐に。`rupdF-sound`・`rupdF-complete` に 1 節ずつ追加 |

`Extract.agda` は `rupdF` を呼ぶだけなので変更なし。`--safe`・postulate 0 は維持。

## `-work` 指標のコストモデル（`RWhileWork*` / `RWhileProgPresWork` / `RWhileProgWork` / `RWhileJonesRevWork`、2026-08-09）

このリポジトリの可逆版 Jones 最適性の主張は **`-work` 指標で測って**いる
（`./measure_proj jones-self` の `wk_p+` / `wk_res` 列）。ところが Agda 側の
コストモデルは `-steps`（実行した命令ノード数）しか無く、**測定と証明が別の
土台に載っていた**。ここを埋めた 6 モジュールである。

`RWhileTime.agda` は**無改変**。work は `∣ k` を置き換えるのではなく、
**第 2 の注釈として加算**してある（`⇒w-steps` で忘れると元の関係に戻るので、
`∣ k` に依存する既存 100 本以上のモジュールは一切影響を受けない）。

### 費用モデルの明文 ↔ Agda（`RWhileWorkV` / `RWhileWork`）

`src/EvalRwhile.ml` 冒頭 30〜75 行の宣言をそのまま定義に落とした。

| OCaml | Agda | 内容 |
|---|---|---|
| `eq_work a b`（`incr eval_work` ＋ `&&` の短絡） | `RWhileWorkV.eqW` | 構造比較で調べた**値ノード対**を 1 つ 1 単位。`&&` が短絡なので不一致で止まる |
| （`eq_work` は bool と counter を同時に返す） | `eqVW` ＋ **`eqVW-≡`** | 1 回の走査で bool とコストを同時に出し、**bool の側が既存の `eqV` と等しいこと**を証明（`eqVW-bool` / `eqVW-cost`）。work 計量は既存の等値判定の**注釈**であって別物ではない |
| `EEq (e1,e2) -> eq_work …`（課金①） | `RWhileWork.expW s (eqE a b)` | 式で課金されるのは `=?` **だけ**。他の 5 形は定義が**リテラルに `0`**（`expW-opd-free` … `expW-pair-free` に個別の補題として書き出してある） |
| `rupdate` の `if vy = VNil then vx else if eq_work vx vy …`（課金②） | `RWhileWorkV.rupdW` | **現在値が nil なら 0**（nil 判定は無課金）。それ以外は `eqW`。`rupdW-fresh` / `rupdW-self` |
| `inv_evalPat` の `PVal`（課金③） | **対応なし**（タイムド核に `<=` が無い） | 平坦核ではパターンが現れないので `PVal` も現れない。層の限界としてヘッダに明記 |
| 無課金（nil 比較・`is_true`・hd/tl/cons・`pair?`・パターン変数） | 上の `expW` の `0` 節と `rupdW nil _ = 0` | 「課金しないもの」が定義から読み取れる形になっている |

短絡の模型化は 2 本の定理で押さえてある。

| 定理 | 内容 |
|---|---|
| `eqW-refl : eqW v v ≡ nodes v` | 自分自身との比較は**全ノードを歩く**（可逆増分が毎反復払う clearing test はこれ） |
| `eqW-mismatch` / `short-circuit` | 先頭が食い違えば**残りの大きさに依らず定数**。`eqW (atm 0 ∙ b) (atm 1 ∙ d) ≡ 2` を任意の `b`/`d` で。これが無ければ work は単なるノード数 |
| `eqW-≤-nodesˡ` | 比較は引数のノード数を超えない |

### 走りに対するコスト関係（`RWhileWork` / `RWhileWorkDet`）

`c ⊢ s ⇒ t ∣ k ∥ w` は `RWhileTime` の関係に第 2 カウンタ `w` を足したもの。

| 定理 | 内容 |
|---|---|
| `⇒w-steps` / `RestW-Rest` | work を**忘れると `RWhileTime` の `∣ k` に戻る**（歩数は同一）。既存資産との互換性 |
| `wk` / `wk-sound` / `⇒-has-work` | 逆に、**既存の任意の導出は work 注釈を持つ**。`wk` は導出上の再帰関数なので `exec-sound` で作った具体導出に対して**計算する** |
| `⇒w-det` | 結果ストア・歩数・**work のすべてが一意**。上界でなく等式を言うために要る |
| `skip-free` / `fresh-ass-free` | 命令をいくら実行しても work が 0 の走りがある |
| `one-step-much-work` | 逆に **1 命令で任意に大きな work**（`x ^= =? A B` を等しい大きな値に）。**歩数は work を抑えない**＝どちらの指標で測ったかを言わないと主張が定まらない、の形式版 |

### p⁺ の work コスト（**本題**）

`-steps` では `cost(p)+8` の**定数**だった。**work では定数ではない**。

- **平坦核の emit（`RWhileProgPresWork`）**: emit の 4 命令のうち、前 2 本は
  **空きスロットへの書き込みなので 0**、3 本目 `self ^= con pd` は `self` が
  `⌜p⌝` を持った状態での clearing test なので `|⌜p⌝|`、4 本目 `y ^= tl out` は
  答えの clearing test なので `|⟦p⟧d|`。よって

  **`pp-work` : `work(p⁺) = work(p) + |⌜p⌝| + |⟦p⟧d|`**（`pp-work-exact` で等式）。

  `work-not-constant` が「どんな定数でも置き換えられない」ことを証明している
  （1 ノードの `⌜p⌝` と 3 ノードの `⌜p⌝` でオーバヘッドが違う）。

- **実機の emit（`RWhileProgWork`）**: OCaml の `program_preserving` は
  `CAss (P-SELF, ⌜p⌝)` ＋ 置換 `CRep (OUT-PP, cons P-SELF Y)` の 2 本で、
  **どちらもこの費用モデルでは 0**（前者は空きスロット、後者はパターン変数の
  読み書き）。代わりに `|⌜p⌝|` は**1 命令あとに現れる**——`evalProgram` 末尾の
  `rupdate (y, res)`（`write` の clearing test）が、`res` の代わりに
  `⟨⌜p⌝, res⟩` を歩くからである。したがって

  **`pp-progW-ocaml` : `work(p⁺) = work(p) + |⌜p⌝| + 1`**。

  一般形は `pp-progW`（emit 自身の課金 `we` をパラメタに取る）で、`we = 0` が
  実機、`we = |⌜p⌝| + |⟦p⟧d|` が平坦核。**両者の差はちょうど `CRep` がただで
  済ませている 2 つの clearing test**。

### 実測との突き合わせ（`RWhileProgWork.measured-law`）

`./measure_proj jones-self` の `wk_dir` / `wk_p+` 列と、`./ri -p2d` が印字する
`⌜p⌝` の `nodes` を Agda のリテラルとして書き、**定理の予言と `refl` で照合**した。
**11 行すべて誤差ゼロで一致**する。

| 被験 | `wk_dir` | `wk_p+` | `\|⌜p⌝\|` | `wk_dir + \|⌜p⌝\| + 1` |
|---|---:|---:|---:|---:|
| `id` | 3 | 23 | 19 | 23 |
| `id2` | 3 | 25 | 21 | 25 |
| `id3` | 4 | 38 | 33 | 38 |
| `rep` | 3 | 25 | 21 | 25 |
| `swap` | 3 | 57 | 53 | 57 |
| `sx_splitjoin` | 3 | 57 | 53 | 57 |
| `sx_three` | 6 | 72 | 65 | 72 |
| `loop_static2` | 16 | 104 | 87 | 104 |
| `loop_static3` | 26 | 118 | 91 | 118 |
| `reverse` | 11 | 103 | 91 | 103 |
| `dyncond3` | 6 | 78 | 71 | 78 |

依頼時の予想「`wk_p+` は被験のサイズとともに増える（23→25→38→57→72）」は
**当たっていた**が、**増分の出どころは予想と違った**。予想は
「`self ^= con pd` の clearing test が ⌜p⌝ を比較する」だったが、実機ではその
代入は**空きスロットへの書き込みで無課金**であり、`|⌜p⌝|` を払うのは
`write` の clearing test である。平坦核のモデルでは予想どおりの場所で払う
（そのぶん `|⟦p⟧d|` も余計に払う）。**モデルの差であって実装の差ではない**。

`jones-work-holds` / `reverse-not-work-optimal` / `dyncond3-not-work-optimal` /
`classical-fails` として、判定結果も Agda 内に固定してある: 閉じた 9 被験は
`wk_res ≤ wk_p+` が成立、動的制御の 2 本（`reverse` 17.2×・`dyncond3` 5.5×）は
**不成立**、古典的基準 `wk_res ≤ wk_dir` は 9 被験すべてで**不成立**
（`RWhileProgPresMin.ext-not-classical` の予言どおり）。

### 可逆版 Jones 最適性の work 版（`RWhileJonesRevWork`）

`RWhileJonesRev.Criterion` は `cost` をパラメタに取り、**中身を一切覗かない**ので
work はそのまま差し込める。`WorkModel` が `cost := progW` で `Criterion` を開き、

| 定理 | 内容 |
|---|---|
| `⁺-PP` | p⁺ が義務 `PP` を満たす |
| `⁺-cost` | **`work(p⁺ on d) = work(p on d) + \|⌜p⌝\| + 1`**（上の法則をモデル側で） |
| `⁺-mono` | ゆえに基準は p 以上——`classical⇒rev` の側条件を**仮定でなく証明**で供給 |
| `classical⇒rev-work` | 古典版 ⇒ 可逆版が work でも成立 |
| `rev-unfold` / `rev-fold` | 基準を展開すると **`work(残余) ≤ work(p) + \|⌜p⌝\| + 1`**。`-steps` の `+8`（絶対定数）との違いはここに集約される |
| `pp-injective-∙` | `⊗-injectiveʳ` は R-WHILE の対（`_∙_`）で**成り立つので仮定を落とせる** |
| `Fp1Work.residual-pp` ほか | fp1 層は**そのまま再エクスポート**。コストを見ないので work でも無条件に成り立つ |
| `Model.*` | 具体インスタンス（空虚でないことの確認）。`workOf 1 nil ≡ 7 = 3 + (3+1)` を `refl` で |

### 正直な範囲（この work 層が言っていないこと）

- **課金③（リテラルパターン）は入っていない。** タイムド核に `<=` が無いため。
  `RWhileCaseCost` が平坦パターンの置換をタイムド核へ翻訳した路線を使えば
  届くが、未着手。`measured-law` が合っているのは、被験のどれも `<=` の
  **リテラル**パターンを走らせていないからである（変数パターンは無課金）。
- **`_▷_⇒_∥_`（プログラム層）は入力ストアを `set [] x d` で近似**している。
  実機は「全変数を nil で初期化してから `rupdate (x,d)`」だが、
  `rupd nil d = just d` かつコスト 0 なので、値・コストとも一致する。
  `all_cleared` は前提として明示してある。
- **`wk_res`（残余の work）は測定値のまま**。残余を Agda で構成してはいないので、
  `jones-work-holds` は「測った数を定理の形に固定した」ものであって、
  残余の work の**証明**ではない。証明されたのは**基準の側**（p⁺ の work）である。
- **`v ≡ nil`（答えが nil）は除外**している。そのとき `write` の clearing test は
  無課金になり法則が 1 ずれる。R-WHILE のプログラムとしては退化した場合。

`--safe`・**postulate 0・hole 0**。`check.sh` は **PASS=114 FAIL=0**（4 分 57 秒、
最大 498 MB）。
