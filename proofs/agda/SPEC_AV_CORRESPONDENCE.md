# spec_av.rwhile ↔ Agda モデル 対応表

実装 `examples/spec_av.rwhile`（実 AV スペシャライザ）と、その特殊化機構を機械検証した
Agda モデル群との**構造的対応**を明示する。完全な意味保存翻訳（実装→モデルのコンパイラを
書き、両者の意味一致を証明）は研究規模の課題であり、本表はその前段＝**目視で検査可能な
対応づけ**である。各行で「Agda 側で何が**証明済み**か」と「対応自体は**目視（transcription）**か」を
区別する。

## 1. 値・概念化（意味）

| spec_av.rwhile | Agda (`RWhileAVSound`) | 状態 |
|---|---|---|
| AV エンコード `('S.v)`/`('D.code)`/`('C.(a.b))` | `data AV = S Val \| D Code \| C AV AV` | 目視（同型のタグ付き表現） |
| 残余コード（`'var`/`'val`/`'cons`/`'hd`/`'tl`/`'eq`/`'pairp`） | `data Code`（`cVar`/`cVal`/`cHd`/`cTl`/`cCons`/`cEq`/`cPairp`） | 目視 |
| 残余を動的入力で評価した意味 | `⟦_⟧c : Code → Val → Val` | 定義 |
| AV を実行時値 ρ で具体化 | `γ : AV → Val → Val` | 定義（特殊化の正しさの基準） |

## 2. AV 代数（各演算は γ と可換＝特殊化が意味保存）

| spec_av.rwhile マクロ | Agda (`RWhileAVSound`) | 健全性（**証明済み**） |
|---|---|---|
| `AV-CONS`（L115） | `avCons` | `avCons-sound : γ(avCons a b)ρ ≡ γ a ρ · γ b ρ` |
| `AV-HD`（L42） | `avHd` | `avHd-sound : γ(avHd a)ρ ≡ hd(γ a ρ)` |
| `AV-TL`（L65） | `avTl` | `avTl-sound` |
| `AV-EQ`（L213） | `avEq` | `avEq-sound` |
| `AV-PAIRP`（L93） | `avPairp` | `avPairp-sound` |
| `AV-LIFT`/`AV-LIFT-STEP`（L138/146） | `lift` | `lift-sound : ⟦lift a⟧c ρ ≡ γ a ρ` |

これらが「spec_av は意味を保って特殊化する」の congruence 核（gap G1）。

## 3. 式の特殊化＝ワークリスト・スタックマシン

| spec_av.rwhile | Agda (`RWhileH2WorklistAV` / `RWhileH2WorklistStore`) | 状態 |
|---|---|---|
| `SPEC-EXP-AV`（L322）：`Cd` 作業スタックを `from..until` で回す | 燃料機械 `machineF`／関係 `_⟱_`（タスクスタック上のループ） | 目視（非構造ループの忠実化） |
| `SPEC-EXP-AV-STEP`（L330–352）：`cons (cons ETag EArg) Cd <= Cd` で1タスク処理 | `machineF`/`_⟱_` の1ステップ（`doEx`/`k*` の各規則） | 目視 |
| `'cons`/`'consE` の begin/end（子を積む→`AV-CONS`） | `doEx(exCons a b)`→`doEx a;doEx b;kCons`、`⟱kCons` | 目視＋`avCons` 健全 |
| `'hd`/`'hdE`、`'tl`/`'tlE` | `doEx(exHd e)`→`kHd`、`doEx(exTl e)`→`kTl` | 目視＋`avHd`/`avTl` 健全 |
| `'eq`/`'eqE`、`'pairp`/`'pairpE` | `kEq`/`kPairp` | 目視＋`avEq`/`avPairp` 健全 |
| `'var => LOOKUP(Vl,EArg,SX)`（L333） | `doEx(varN n)`→`lookupAV n s` | 目視 |
| `'val`（L334） | `doEx(exVal v)`→`S v` | 目視 |
| 結果スタック `RSt` | `_⟱_`/`machineF` の AV 結果スタック | 目視 |
| **ループ全体の停止＝燃料**（`from..until` の有界性） | `machineF : ℕ → …`（燃料減少で `--safe` 全域） | **証明済み**：`machineF`-sound/complete/mono が関係 `_⟱_` と一致 |
| 組み立てた残余の正しさ | `worklist-spec-sound`：`γ(avEval ex)ρ ≡ ⟦ex⟧ρ` | **証明済み** |

## 4. ストア（`Vl`）アクセス

| spec_av.rwhile | Agda (`RWhileH2WorklistStore`) | 状態 |
|---|---|---|
| `AUX`（L32）：`Cnt` で index `J` までストアを歩く（`from..until (=? Cnt J)`） | `cSlot n = cHd(cTl^n cVar)`（tl で n 歩いて hd） | **証明済み**：`cSlot-sound : ⟦cSlot n⟧c ρ ≡ vNth n ρ` |
| `LOOKUP`（L22）＝`AUX; read; INV-AUX` | `lookupAV n s`（スロットの AV を返す） | 目視 |
| ストア `Vl`：スロットごとに `('S.v)`/`('D.…)` | `s : List AV`（partial-static 多スロット環境） | 目視 |
| ストアが実行時の実値と整合（静的スロットが正しい） | `Consistent s ρ` | **証明済み**：整合性の下で `Core.worklist-store-sound` が γ 健全 |

## 4b. 式の wire format ↔ モデル（**検証済みの橋**、`RWhileSpecAVWire`）

§3 の「目視」のうち**式エンコード**は、機械検査済みの往復定理に格上げ済み。

| spec_av.rwhile / p2d | Agda (`RWhileSpecAVWire`) | 状態 |
|---|---|---|
| 式の値エンコード（`'var.i`/`'val.v`/`'cons.(a.b)`/`'hd.e`/`'tl.e`/`'eq.(a.b)`/`'pairp.e`） | `WVal`（7 タグ atom＋nil/cons）、`encEx : Ex → WVal` | 目視（`transExp` を一行写し） |
| 残余を評価する復号器 `d_exp`（`Program2DataRwhile.ml:96-104`） | `parseEx : WVal → Maybe Ex`（`d_exp` を一行写し） | 目視 |
| 変数 index＝unary nil-count（`d_count`、nil=0） | `encIdx`/`decIdx`、`dec-enc-idx` | **証明済み** |
| 往復（実装 wire format が同じ式へ復号） | `parse-enc : parseEx (encEx e) ≡ just e` | **証明済み**（＝対応が定理） |
| 復号した式の AV 残余の正しさ | `wire-sound`／`bridge`（`avEval-sound` と合成、γ 健全） | **証明済み** |
| 実装側の相互検証（同一 wire 木を `d_exp` で復号＝`parseEx`、`transExp`→`d_exp` 往復） | OCaml テスト群 `wire-bridge`（`src/TestSuite.ml`） | **テスト済み** |

＝`encEx`/`parseEx` は依然 `transExp`/`d_exp` の**一行写し（目視）**だが、両者が**互いに逆**であることと、
復号像の特殊化が健全であることは**機械検査済みの定理**になった。残る目視は「写しが忠実か」だけで、それも
OCaml `wire-bridge` テストが同一入力で実装と一致を確認している。

## 4c. パターン・コマンド・プログラム層の wire format（**検証済みの橋**、`RWhileSpecAVWireCom`）

§4b を AST 全体に拡張し、意味保存翻訳の**構文側を完成**。

| spec_av.rwhile / p2d | Agda (`RWhileSpecAVWireCom`) | 状態 |
|---|---|---|
| `transPat`/`d_pat`（`'cons`/`'var`/`'val`） | `Pat`、`encPat`/`parsePat` | **証明済み**（往復 `parse-enc-pat`） |
| `transCom`/`d_com`（`'seq`/`'ass`/`'rep`/`'cond`/`'loop`、末尾 nil 終端込み） | `Com`、`encCom`/`parseCom` | **証明済み**（往復 `parse-enc-com`） |
| `transProgram`/`data2program`（`(('var.i).(c.('var.j)))`） | `Prog`、`encProg`/`parseProg` | **証明済み**（往復 `parse-enc-prog`） |
| コマンド内の式の健全性 | `ass-exp-sound`（`wire-sound` 再利用） | **証明済み** |
| 実装側相互検証（同一 wire 木を `d_com` 復号、atom-free コマンドの `transCom`→`d_com` 往復） | OCaml `wire-bridge` 群 | **テスト済み** |

⇒ **AST 全体（式＋パターン＋コマンド＋プログラム）↔ 実装 wire format が定理**になった。残る目視は「写しの忠実さ」のみ。

## 5. 何が証明され、何が残るか

- **証明済み（全49モジュール `--safe`、公理ゼロ）**：AV 代数の γ 健全性、ワークリスト機械の正当性
  （関係＝燃料機械、sound/complete/mono）、ストアアクセスの健全性、整合性下の特殊化の γ 健全性、
  **AST 全体（式＋パターン＋コマンド＋プログラム）の wire format 往復（`parse-enc`/`parse-enc-pat`/
  `parse-enc-com`/`parse-enc-prog`）と式復号像の健全性（`wire-sound`／`ass-exp-sound`）**。
  ＝spec_av の特殊化機構を「ループ機構（ワークリスト＋燃料）＋AV 全代数＋partial-static 多スロット
  ストア＋γ 健全性＋AST 全体の検証済みの橋」で機械検証。
- **目視（transcription）対応**：§2/§3/§4 の各「目視」行＝Agda 定義が spec_av マクロを忠実に写していること。
  wire format（式・パターン・コマンド・プログラム）については §4b/§4c で**往復定理＋OCaml 相互検証**まで進み、
  意味保存翻訳の**構文側は完成**。純粋な目視は「写しの忠実さ」に縮小。
- **残（研究規模・任意）**：(a) wire 翻訳の**意味側**＝コマンド層の操作的意味＋AV 特殊化器と操作的等価
  （`ass-exp-sound` は式の健全性まで。コマンド全体の意味保存はこれの先）。(b) `MKAV`（L895、束縛時刻認識の
  部分入力）と自己適用下の BT＝comp2 を非自明 fp2 にする本番改造（`HANDOFF_fp2.md`／`analysis_store_bti.md`、
  高リスク）。理論的核は本対応で出揃っているため、(a)(b) は「実装との橋」を太くする工学であり、本質的障害は無い。

## 6. 残課題の分解（2026-07-16）

前提：`RWhileFutamura3.agda` により **fp2/fp3 は契約（基本方程式
`[[spec_av]((p.('S.s)))](d) = [p]((s.d))`）に還元済み**（H2 は定義的に消え、階層は契約を超える
証明義務を追加しない）。残るは §5 の (a)(b) ＝独立な2系統：

- **C 系（正しさ）**：契約そのものを実物 spec_av について証明する（§5(a) 意味側の橋）。
- **O 系（品質）**：comp2 ≪ |spec_av| の本番 BTI（§5(b)）。契約とは直交（自明 comp2 でも契約は満たす）。

### C 系：契約の証明 — 各ステップ単独で機械検査可能

| # | 何をするか | 既存資産 | 成果物 | 規模 |
|---|---|---|---|---|
| **C1** | wire の `Com`（§4c）に big-step 意味 `⟦_⟧com : Com → Val → Maybe Val` を直接定義（RWhileExec/RWhileRevFull は control-core の別 AST なので、wire AST に与えるのが最短）。OCaml `EvalRwhile.evalCom` と差分テスト（`wire-bridge` 群拡張） | `RWhileExec`、`RWhileElabCom`、`parse-enc-com` | `RWhileWireSem.agda`＋OCaml テスト | 小〜中 |
| **C2** | コマンド層 AV 特殊化器 `specCom`（SPEC-COM 相当：ass→cond→seq→loop→rep の順に増分）を、検証済みの式ワークリスト＋多スロットストア上に定義し、ケースごとに γ-sound | ass=`ass-exp-sound`、cond dead-branch=`deadbranch-true/false`、loop BT 規則=`RWhileLoopBTA`（unrollable / exit-dynamic-forces-residual）、rep=`RWhileCRep`、燃料流儀=`machineF` | `RWhileSpecCom.agda`（ケース別に順次緑化） | 中（山は loop） |
| **C3** | プログラム全体 `specProg-sound : ⟦specProg p s⟧ d ≡ ⟦p⟧(s·d)` ＝**契約のモデル定理**。`RWhileFutamura3.Contract` に渡すと fp1/2/3 がモデルで**無条件**成立 | C2 の合成＋`RWhileFutamura3` | `RWhileSpecProg.agda`＋Contract インスタンス | 小 |
| **C4a** | 転写忠実性の機械化：MAlonzo 抽出（`Extract*` の既存流儀）で specCom/specProg を OCaml に出し、実物 spec_av 実行と**大量ランダム入力で差分テスト**（pointwise 橋の大量化） | `ExtractRevProj` 等の build-extract.sh 流儀、`wire-bridge` | 抽出＋QuickCheck 風テスト群 | 小〜中 |
| **C4c** | 最終形（任意・研究規模）：spec_av.rwhile 自体を C1 意味論で走らせた結果と specProg の一致定理（42KB の deep-embedding が必要） | C1–C4a 全部 | — | 研究規模 |

**到達点の整理**：C1–C3 で「契約はモデルの定理、fp3 はモデルで無条件」。C4a で「実物との一致は
大量差分テストで裏付け」。**真に研究規模なのは C4c のみ**で、C1–C4a は工学。

### O 系：本番 BTI — blueprint は全て証明済み、残るは実装

| # | 何をするか | 対応する証明済み blueprint |
|---|---|---|
| **O1** | loop BT 修正を `spec_av_bti.rwhile` へ（fp1 ゲート保護下） | `RWhileLoopBTA`／`RWhileLoopBTARev` |
| **O2** | MKAV／:1051 over-static 修正（mkAV 流儀） | `RWhileOfflineBTA`–`7` |
| **O3** | agenda の offline 化（dynamic cond は両枝残余化、agenda へ積まない） | `RWhileOfflineBTA8` |
| **O4** | 計測：comp2 縮小率（目標 <0.5×）＋可逆性維持の確認 | `RWhileOfflineBTA9`（可逆性）、`measure_proj` |

依存：O1→O2→O3 の順が安全（各段 fp1/fp2 回帰ゲートで保護）。

### 推奨着手順（費用対効果順）
1. **C1**（wire Com 意味論＋差分テスト）— 全ての土台、既存部品の組み立て。
2. **C2 の ass+cond+seq**（部品は証明済み、合成のみ）→ 続けて loop。
3. **C3**（契約のモデル定理）— 論文に書ける区切り：「fp3 はモデルで無条件、実物へは契約1本」。
4. **C4a**（抽出差分テスト）— 実物との橋を「目視＋点」から「大量点」へ。
5. **O1–O4** — 品質系。論文本体では「今後の課題」の筋。

### 進捗（2026-07-16 実施）
- **C1 済**：`RWhileWireSem.agda`（wire AST の big-step 意味論、fuel 単調性込み）＋
  OCaml `wire-sem` 差分テスト群（同一 wire 木を本番 evalProgram とモデル鏡写しで実行、
  成功時一致＋失敗モード一致、実例コーパス6本）。
- **C2 済（静的制御フラグメント）**：`RWhileSpecCom.agda` — 多スロット partial-static
  ストア上の specEx/specPat/specInv/specAss/specCom、成功シミュレーション
  `specCom-sim`、**契約のモデル定理 `spec-contract`**。動的テスト・動的更新衝突は
  refuse（＝O系 blueprint の残余化が将来対応）。
- **C3 済**：`RWhileSpecProg.agda` — 実際に残余化する specialiser を持つ宇宙での
  fp1/fp2/fp3（`fp3-run`）。fp1 は仮定でなく **証明済み spec-contract**、自己適用は
  closure コンストラクタ経由（specProg 自身の wire 化＝研究規模のまま、実物側は
  OCaml fp2/fp3 テストが担保）。
- **C4a 済**：(a) OCaml `wire-spec` 群 — 検証済みモデル特殊化器の鏡写し（WS）と
  **実物 spec_av** の残余を、swap／静的分岐／静的ループ展開（op-list）コーパスで
  **3者一致**（モデル残余・spec_av 残余・直接実行）まで確認。(b) `ExtractSpecProg.agda`
  — C1–C3 の検証済みコードを MAlonzo/GHC でネイティブ化し、cogen→compiler→residual→run
  の全鎖を実行（各段が機械検証済み定理に対応）。
- **O 系 step 0 済**（rproj `analysis_store_bti.md` 再構成・計測ログ参照）：
  stale だった spec_av_bti 作業コピー（fp1 ゲートは通るのに自己適用 comp2 が
  小さくて誤り＝旧 over-static 症状）を現行 spec_av のコピーに更新、
  正ベースライン comp2=812,515（0.994×）・correctness true・CLoop=125 を確立。
  教訓：**fp1 ゲート＋comp2-loops の correctness 行をセットで運用**。
- **O1 済（2026-07-16）**：spec_av_bti の 'loop ハンドラに **出口テストの BT を先読み**する
  判定を実装（静的入口＋動的出口 → RAW テストのままループ全体を残余化、
  `constEntry-no-iter` の罠回避のため定数畳み込み入口は emit しない）。旧挙動は
  'lcheck で `'error '41`。fp1 ゲート PASS、新テスト `bti-loop`（残余ループ存在の
  検査込み）green、自己適用 comp2 の正しさ維持（true/true、133 CLoop・0.995×＝
  ソース肥大分の増加で想定通り。縮小は O2 の領分）。
- **C2-dyn 済（2026-07-16）**：`RWhileSpecComDyn.agda` — 動的 cond を**両枝特殊化＋
  pointwise `rIf` ストア join**で扱う拡張（OfflineBTA8 の keep-both-branches 規則の
  wire レベル版）。`spec-contract-dyn` が動的制御プログラムまで契約を拡張。
  check.sh PASS=66 FAIL=0。
- 残：**C4c**（deep-embedding、研究規模）、**O2**（index/Cd の partially-static 化＝
  本丸・研究規模）、**O3**（agenda offline 化＝残余 cond コマンド emit。モデル側の
  対応物は C2-dyn で先行検証済み）。blueprint は Agda で証明済み、ベースラインと
  プロトコルは整備済み。

関連：`AGDA_CORRESPONDENCE.md`（全モジュール↔結果マップ）、`HANDOFF_fp2.md`、`FINDINGS_reversible_projections.md`。
