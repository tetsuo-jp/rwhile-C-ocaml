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

## 5. 何が証明され、何が残るか

- **証明済み（全48モジュール `--safe`、公理ゼロ）**：AV 代数の γ 健全性、ワークリスト機械の正当性
  （関係＝燃料機械、sound/complete/mono）、ストアアクセスの健全性、整合性下の特殊化の γ 健全性、
  **式 wire format の往復（`parse-enc`）と復号像の健全性（`wire-sound`）**。
  ＝spec_av の特殊化機構を「ループ機構（ワークリスト＋燃料）＋AV 全代数＋partial-static 多スロット
  ストア＋γ 健全性＋式 wire format の検証済みの橋」で機械検証。
- **目視（transcription）対応**：§2/§3/§4 の各「目視」行＝Agda 定義が spec_av マクロを忠実に写していること。
  式エンコードについては §4b で**往復定理＋OCaml 相互検証**まで進み、純粋な目視は「写しの忠実さ」に縮小。
  コマンド／ストア更新側（`'seq`/`'ass`/`'rep`/`'cond`/`'loop`、UPDATE 等）の wire 翻訳はまだ未着手。
- **残（研究規模・任意）**：(a) §4b と同じ往復・健全性をコマンド層（`d_com`/`transCom`）まで広げ、最終的に
  実装 AST → モデルの**完全な意味保存翻訳**へ。(b) `MKAV`（L895、束縛時刻認識の部分入力）と自己適用下の BT＝
  comp2 を非自明 fp2 にする本番改造（`HANDOFF_fp2.md`／`analysis_store_bti.md`、高リスク）。理論的核は本対応で
  出揃っているため、(a)(b) は「実装との橋」を太くする工学であり、本質的障害は無い。

関連：`AGDA_CORRESPONDENCE.md`（全モジュール↔結果マップ）、`HANDOFF_fp2.md`、`FINDINGS_reversible_projections.md`。
