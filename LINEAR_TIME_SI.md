# R-WHILE の線形時間自己解釈系 — Agda 形式化（2026-08-04）

Glück–Yokoyama の *A linear-time self-interpreter of a reversible imperative language*
の主張「**R-WHILE には線形時間の自己解釈系が存在する**」を、定理証明系（Agda 2.8 /
stdlib、`--safe`・postulate 0・穴 0）で機械検証する開発。**自己解釈系は抽象機械ではなく、
対象言語そのもので書かれた 1 本の R-WHILE プログラム**である。

<!-- METRICS:SUMMARY:BEGIN -->
新規モジュール（`proofs/agda/`、全 27 本・6527 行、`./check.sh` は PASS=93 FAIL=0）:
<!-- METRICS:SUMMARY:END -->

| モジュール | 内容 |
|---|---|
| `RWhileTime` | **時間付き意味論** `c ⊢ σ ⇒ τ ∣ k`（`EvalRwhile.ml` の `eval_steps` と一致）＋燃料付き `exec`／`exec-sound` |
| `RWhileSIEnc` | プログラム↔データ符号化 `⌜_⌝`（`Program2DataRwhile.ml` の Agda 版）・タグ表 |
| `RWhileSIWf` | ストア分離則、`NotIn`／**frame 補題**、`Wf`／`InR`、実行のストア長不変 `⇒-length` |
| `RWhileSIMach` | **アジェンダ機械**（`ri.rwhile` の主ループの抽象）と**シミュレーション定理**（対象 1 ステップ ≤ 機械 4 ステップ、プログラム保存） |
| `RWhileSIRun` | **上界付き実行 `Run c s t B`** と合成子（`_»_`／`rSeq`／`rThen`／`rElse`／`rWeak`） |
| `RWhileSIMac` | 解釈系の 19 スロットのレジスタファイル、**汎用 `push`/`pop`**（`^=` のみで実装、コスト 9） |
| `RWhileSIWalk` | 対象ストア `Vl` の**歩行**（往復とも、コスト 28/セル） |
| `RWhileSILookup` | **`LOOKUP`／`UPDATE`**（コスト `56k + 27`）とストア分割補題 |
| `RWhileSIEval` | オペランド評価 `opdC`（`56M+36`）と**式評価 `evalC`**（平坦式 6 形、上界 `evalB M`） |
| `RWhileSIStep` | **`STEP`（ディスパッチ本体）と全 12 ケースの実行補題**（17 定理、各 `astep` 一致つき） |
| `RWhileSIArith` | 合成の**上界計算**（対象 1 ケース＝補題 1 本、純 ℕ。巨大な機械状態の型を算術から隔離） |
| `RWhileSISim` | 主ループ `SI`、反復連鎖 `PChain`/`PC`、`Rest` への変換、一様定数 `CC`、**合成 `simP`/`simPR` と主定理 `si-linear`** |
| `RWhileSIProg` | 同じ主張のモジュラ版（`Realises` を仮定。`RWhileSISim` が具体的に discharge） |
| `RWhileTimeInv` | **プログラム反転 `inv`（`InvRwhile.ml` の Agda 版）とコスト保存の健全性**・`rupd` の部分対合性・`inv-inv`・`Wf`/`InR` の保存 |
| `RWhileTimeDet` | **意味論の決定性** `⇒-det`／`Rest-det`（結果ストアもステップ数も一意） |
| `RWhileTimeExec` | **燃料付き評価器の完全性**（単調性 `exec-mono` ＋ `exec-complete`）と、停止しないプログラムの特徴づけ |
| `RWhileSIDet` | 上を `si-linear` に載せた **`si-unique`**（`SI` の**どの停止実行も**正しい答え・上界内） |
| `RWhileSIComplete` | 逆向き（`SI` 停止 ⇒ 対象停止）について**証明できた範囲と残る義務**を明示 |
| `RWhileSIShow` | **具象構文プリンタ**（`Cmd` → R-WHILE テキスト）。`SI` を実際に走る `.rwhile` として抽出するために使う |
| `RWhileSIParse` | **プリンタの往復定理**（トークン列の構文解析器と `parse (tok e) ≡ just (e , ts)`）と `;` の結合に関する曖昧性の解消 |
| `RWhileSINorm` | **右結合化 `nf`**（印字は不変・実行と歩数も不変）。抽出テキストが表す項と `SI` を結ぶ |
| `RWhileSIRoundTrip` | 上の実例化: **抽出テキストは `nf SI` に読み戻る**（`si-text`） |
| `RWhileSIExecTest` | **`SI` を型検査器の中で実際に走らせる**（`exec`）。skip/代入/逐次/ループの 5 例 |
| `RWhileSIP2D` | **実装 `-p2d` との差分テスト**（実装の符号化を Agda でモデル化し、`./ri -p2d` の出力と文字列一致を型検査器が検証）と一様符号化への翻訳定理 |
| `RWhileTimeDec` | `Wf`/`InR` の**決定手続き**（`wf?`/`inR?`/`Wf!`/`InR!`）。具体プログラムの静的条件を評価で discharge |
| `RWhileSIInv` | 上を合成した系：**逆プログラムの解釈**（`si-inverse-linear`・`si-round-trip`）と**解釈系自身の逆走**（`si-uncompute`） |
| `RWhileSITest` | **実行テスト**（型検査器が `exec` を走らせ、結果とステップ数を照合） |

## 1. コストモデル（実装と一致）

`src/EvalRwhile.ml` の `evalCom` は呼び出しごとに `incr eval_steps` → **実行コマンドノード 1 個 = 1 ステップ**。
`./ri -steps` と `examples/measure_ri_overhead.sh`（実測 a-rev ≈ 364）のモデルそのもの。

## 2. 対象言語（スコープ）

```
skip | X ^= E | C ; D | if E then C else D fi F | from E do D loop L until F
E ::= A | cons A B | hd A | tl A | =? A B | pair? A        (A, B は変数か定数)
```
値は `nil | atom n | (u . v)`、ストアは値のリスト、`^=` は `rupdate` と同じ部分対合。
条件文の出口表明・ループの入口/反復表明も `EvalRwhile.ml` どおり。
**式は平坦**（オペランド＝変数か定数、符号化は `(tag . (o1 . o2))` に一様化）。表層のネスト式と `<=` は範囲外。
`pair?`（cons 判定）は 2026-08-05 に追加（実装の `pair? E` と同じ意味論）。

## 3. 自己解釈系の構造（`ri.rwhile` と同じ）

```
SI = from (=? Cd' nil) do skip loop STEP until (=? Cd nil)
STEP = (pop Cd→Hd ; splitT) ; (DISPATCH ; (buildT ; push Hd→Dn))
```

- **todo/done の 2 スタック**。done は単なる Bennett ゴミではなく**ソースを組み立て直す**ので、
  実行終了時に done には `⌜c⌝` がちょうど 1 個（プログラム保存）。
- **`DISPATCH` は 12 段の条件文ネスト**。各ケースが**相異なる最終タグ**を残すので、各段の出口表明
  `=? Tg <最終タグ>` が成立する — 機械のタグ代数がそのまま可逆性の根拠。
- ループのプロトコル: `loop → lpA(e を評価) → ⌜D⌝ → lpD(f を評価) → {lpZ | lpB} → ⌜L⌝ → lpC → lpA → …`。
  **入口テスト `e` を `D` の前に評価**するのが本質的で、「初回到達か」は `e` の真偽と一致する
  （初回＝真、再入＝偽＝R-WHILE のループ可逆性表明）ため、**消去不能なビットが生じない**。
  この点を誤ると `astep` が非単射になり R-WHILE では実装できない（設計の途中でこれを発見・修正した）。
- **compute–use–uncompute**: `opdC`・`evalC`・`LOOKUP` はいずれも正味の効果が 1 つの `^=` だけなので
  部分対合であり、**同じコードをもう一度走らせるだけで逆計算できる**（`ri.rwhile` の `INV-` マクロ）。

## 4. 証明された定理

### (a) 機械レベル（`RWhileSIMach`）— 無仮定

```agda
machine-linear : c ⊢ σ ⇒ τ ∣ k
               → Σ[ n ] (Steps ⟨ ⌜c⌝∙nil , nil , σ ⟩ ⟨ nil , ⌜c⌝∙nil , τ ⟩ n × n ≤ 4 * k)
```
正当性・プログラム保存・**対象 1 ステップあたり機械 4 ステップ**。

### (b) 各ディスパッチケース（`RWhileSIStep`）— 無仮定・17 定理

| ケース | STEP 上界 | ケース | STEP 上界 |
|---|---|---|---|
| `skip` | 34 | `loop` | 54 |
| `seq` | 80 | `lpA`(初回/再入) | `lpAStep M` |
| `seqE` | 81 | `lpD`(終了/継続) | `lpDStep M` |
| `cond`(真/偽) | `condStep M` | `lpB` | 84 |
| `condE`(真/偽) | `condEStep M` | `lpZ` | 57 |
| `ass` | `assStep M` | `lpC` | 86 |

`M` は対象ストアのセル数。`M` 依存の上界はすべて `evalB M = 224M + 179` を含み、
その源は `Vl` の歩行（`56k + 27`）— これが `a_p` をストアサイズに affine にする唯一の箇所。

### (c) プログラムレベル（`RWhileSISim.si-linear`）— **無仮定**

```agda
si-linear : Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
          → Σ[ j ] (SI ⊢ ⟨⌜c⌝∷todo, done, σ⟩ ⇒ ⟨todo, ⌜c⌝∷done, τ⟩ ∣ j
                    × j ≤ (CC M + 2) * k)
```

- **`SI` は固定された 1 本の R-WHILE プログラム**（`STEP` は `RWhileSIStep` の実コード）。
- 定数は `CC M = 2940·M + 3184`（M = 0,1,2 で機械検証。M はストアのセル数）。
  したがって `a_p = 2940·M + 3186` で、**ストアサイズに affine な定数の線形時間**。
- 終了時、done スタックには `⌜c⌝` がちょうど 1 個 — **入力プログラムを組み立て直す**ので
  「解釈系」であって消費するプログラムではない。
- 合成は `simP`（対象導出の 6 ケース）と `simPR`（ループの `Rest` 2 ケース）の相互再帰。
  上界の算術は `RWhileSIArith` の 6 補題（`lemAss`/`lemSeq`/`lemCond`/`lemLoop`/`lemExit`/`lemIter`）に分離。

モジュラ版 `RWhileSIProg.si-linear`（`Realises` を仮定して `j ≤ (4(C+1)+2)·k`）も残してある。

### (d) 逆方向（`RWhileTimeInv` / `RWhileSIInv`）— 無仮定

```agda
inv-sound         : Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k → inv c ⊢ τ ⇒ σ ∣ k     -- k は同じ
si-inverse-linear : … → SI ⊢ ⟨⌜inv c⌝, τ⟩ ⇒ ⟨⌜inv c⌝, σ⟩ ∣ j × j ≤ (CC M + 2) * k
si-round-trip     : … → j₁ + j₂ ≤ (CC M + 2)*k + (CC M + 2)*k
```

- **反転はコストを完全に保存する**（`≤` ではなく同じ `k`）。`^=` は `rupd` が部分対合なので
  自分自身が逆、条件文はテストと表明の交換、ループは入口テストと出口表明の交換。
- ループの証明が要点: 逆向きの実行は同じストア列を逆順にたどるが、**反復が 1 つずれる**
  （逆向きの各反復は、ある反復の `inv L` と**ひとつ前**の反復の `inv D` を組にする）。
  `inv-rest` は前向きの `Rest` を歩きながら後ろ向きの `Rest` を蓄積し、
  「現在のストアに入ってきた `D` の逆実行」を持ち回ることでこのずれを吸収する。
- 系として、**同じ 1 本の解釈系 `SI` が両方向を同じ定数で回す**（`si-round-trip`）。
- 実行テスト: `inv` の構文（列の反転・テストの交換）と、往復（`p₁` 3 ステップ・ループ例 4 ステップが
  逆向きでも同じ歩数で元のストアに戻る）を `exec` で照合。

### (d′) 決定性と一意性（`RWhileTimeDet` / `RWhileSIDet`）— 無仮定

```agda
⇒-det     : c ⊢ σ ⇒ τ₁ ∣ k₁ → c ⊢ σ ⇒ τ₂ ∣ k₂ → τ₁ ≡ τ₂ × k₁ ≡ k₂
si-unique : Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
          → ∀ {t j} → SI ⊢ ⟨⌜c⌝∷[], [], σ⟩ ⇒ t ∣ j
          → t ≡ ⟨[], ⌜c⌝∷[], τ⟩ × j ≤ (CC M + 2) * k
```

意味論は関係だが**関数的**である（式評価と `rupd` が関数で規則が構文主導）。これにより
`si-linear` の主張は「そう実行**できる**」から「**どの停止実行もそうなる**」に強まる。
上界も同様に「ある実行が速い」ではなく「その実行が速い」になる。

### (d″) 実行可能な評価器との一致（`RWhileTimeExec`）— 無仮定

```agda
exec-mono     : exec n c σ ≡ just r → exec (suc n) c σ ≡ just r
exec-complete : c ⊢ σ ⇒ τ ∣ k → Σ[ n ] exec n c σ ≡ just (τ , k)
```

`exec-sound`（計算した実行は導出である）と合わせて、**関係と実行可能な評価器は完全に一致**する。
帰結として「停止する実行が存在しない」ことが検査可能な形になる:

```agda
no-run→exec-nothing : (どの導出も存在しない) → ∀ n → exec n c σ ≡ nothing
exec-nothing→no-run : (∀ n → exec n c σ ≡ nothing) → どの導出も存在しない
```

**この定理が言わないこと**（正直に）: `exec` が常に `nothing` であることは「無限ループ」と
「行き詰まり（`rupd` の失敗・条件文の出口表明が成立しない）」を**区別しない**。
時間付き big-step 意味論では両者を区別できず、そのためには小ステップ意味論が要る（本開発の範囲外）。

### (d‴) 逆向きはどこまで言えるか（`RWhileSIComplete`）

**証明済み**

```agda
si-halts→todo-empty : SI ⊢ s ⇒ t ∣ j → evalT t emptyTodo ≡ just true
si-answer           : Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
                    → ∀ {t j} → SI ⊢ ⟨⌜c⌝∷[], [], σ⟩ ⇒ t ∣ j
                    → t ≡ ⟨[], ⌜c⌝∷[], τ⟩ × j ≤ (CC M + 2) * k
```

- `SI` が停止したなら **todo スタックは空**＝積まれたタスクはすべて処理された。
- `SI` が停止し、かつ対象も停止するなら**答えは必ず一致**する。つまり
  **停止した `SI` が嘘をつくことはない**。

**未証明（型として明示、仮定はしていない）**

```agda
SiComplete = ∀ {c σ t j} → Wf c → InR c σ → SI ⊢ ⟨⌜c⌝∷[], [], σ⟩ ⇒ t ∣ j
           → Σ[ τ ] Σ[ k ] ((c ⊢ σ ⇒ τ ∣ k) × t ≡ ⟨[], ⌜c⌝∷[], τ⟩)
```

「`SI` が停止するなら対象プログラムも停止する」。必要なのは**デコード不変量** —
到達可能な任意の機械状態（タスクとマーカの todo スタック・done スタック・対象ストア）から
対象レベルの継続への写像と、「`STEP` 1 回がちょうど対象 1 ステップ動かす」ことの証明。
`RWhileSIMach` は導出から実行列を作る（易しい向き）だけなので、この写像は別途の開発が要る。
**健全性の穴ではない**ことに注意: `si-answer` により停止した `SI` は誤答しない。
開いているのは「対象が停止しないのに `SI` が停止しうるか」だけである。

### (e) 解釈系そのものの可逆性（`RWhileSIInv.si-uncompute`）— 無仮定

```agda
si-uncompute : Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
  → Σ[ j ] ( SI     ⊢ ⟨⌜c⌝∷[], [], σ⟩ ⇒ ⟨[], ⌜c⌝∷[], τ⟩ ∣ j
           × inv SI ⊢ ⟨[], ⌜c⌝∷[], τ⟩ ⇒ ⟨⌜c⌝∷[], [], σ⟩ ∣ j     -- 同じ j
           × j ≤ (CC M + 2) * k )
```

`SI` も 1 本の R-WHILE プログラムなので `inv` が適用できる。その静的条件（`Wf SI`・`InR SI`）は
**型検査器が評価で片付ける**（`RWhileTimeDec` の決定手続き。`Wf SI` は 3.9 秒・405 MB で `yes`）。
結果として、**1 回の解釈とその逆計算は同じ歩数**であり、どちらも対象プログラムの実行時間に線形。

## 4.5 定数の内訳と削減ログ

`proofs/agda/metrics.sh` が**証明で使っている定数そのもの**を型検査器に計算させて表示する
（見積りではない）。現在値（`./metrics.sh` が生成）:

<!-- METRICS:CONSTANTS:BEGIN -->
```
constant            M=0      M=1   slope
CC                 3196     5940   2744
lpDStep             464      912   448
lpAStep             444      892   448
assStep             429      933   504
condStep            445      893   448
condEStep           470      918   448
evalB               179      403   224
```
<!-- METRICS:CONSTANTS:END -->

**削減ログ**

| 日付 | 変更 | `CC 0` | 傾き |
|---|---|---:|---:|
| 2026-08-04 | 基準（`si-linear` 成立時） | 3184 | 2940 |
| 2026-08-05 | `pair?` を追加（EDISP が 1 段深くなり、compute+uncompute で 1 ケースあたり +2） | 3196 | 2940 |
| 2026-08-05 | カウンタ加算・減算を専用命令列に（`push`/`pop` の 9 → `incC`/`decC` の 7） | 3196 | **2744** |

式形を 1 つ増やす代価は**定数 +12・傾き 0**（歩行を増やさないため）。

`CC M = lpDStep + 2·lpAStep + assStep + condStep + condEStep + 500`（500 は合成の余裕）。

**傾き 2940 の出どころ**（1 セルあたりに分解）:

```
2744 = 448(lpD) + 896(lpA×2) + 504(ass) + 448(cond) + 448(condE)
 448 = 2 × 224      … compute–use–uncompute で式評価が 2 回
 224 = 4 ×  56      … オペランド 2 個 × 2 回 × 歩行 56/セル
 504 = 448 + 56     … 代入は UPDATE の歩行が 1 回分多い
  56 = 28 + 28      … 往路と復路
  28 = 19 + 7 + 2   … セル移動(pop 9 + push 9 + seq 1) ＋ カウンタ加算(incC 7) ＋ ループ 2
```

**削減の見通し（計測して判明したこと）**:

- ~~カウンタ加算は専用命令列で 9 → 7 にできる~~ → **2026-08-05 実施済み**（`incC`/`decC`。
  傾き 2940 → 2744、**−6.7%**）。`push` の `x ^= hd t` が Hd = nil で無駄だった。
- セル移動 19 歩は**平坦式の核言語では下がらない**。融合版を書いても代入 10 個＝19 歩になる。
  1 歩で書ける `T1 ^= cons (hd Vl) Rv` が**ネスト式を要求する**ため。
- ⇒ **定数削減の本丸は A1（ネスト式）**であり、それ以前の削減余地は約 7%。
  この計測結果にもとづき、ループの優先順を「解釈系自身の可逆性（F2）→ 式形の追加 → 定数削減」に変更した。

## 4.6 実装の `-p2d` との差分テスト（`RWhileSIP2D`）

形式化が「理想化した符号化」ではなく**実物**を語っていることを担保するため、
`src/Program2DataRwhile.ml` の符号化を Agda でモデル化し（`⌜_⌝ᵖ`）、実装の具象構文で
印字して（`showV`）、**`./ri -p2d` の出力と文字列一致することを型検査器に検証させる**。
8 プログラム（代入・`cons`・`hd`・`pair?`・`=?`・逐次・条件・ループ）で一致を確認済み。

両者の相違（意図的なもの）と対応:

| 対象 | 実装 `-p2d` | 本形式化 `⌜_⌝` |
|---|---|---|
| 変数 | `('var . num k)`（1 始まり） | 同じ（0 始まり） |
| 定数 | `('val . v)` | `('cst . v)`（名前だけの違い） |
| 裸のオペランド | そのまま | `('opd . (o . dummy))` に包む |
| `hd`/`tl`/`pair?` | `(tag . o)` | `(tag . (o . dummy))` |
| `cons`/`=?` | `(tag . (o1 . o2))` | 同じ |
| `if`/`from` | 末尾に `nil` が付く | 付かない |
| `skip` | **無い**（`doNothing` = `X0 ^= nil`） | `('skip . nil)` |

この対応は**証明されている**: 総翻訳 `p→uC` について

```agda
p→u-ok : ∀ c → p→uC ⌜ c ⌝ᵖ ≡ ⌜ deskip c ⌝
```

すなわち実装の `-p2d` 出力を機械的に変換すれば、検証済み解釈系 `SI` がそのまま食える。
`deskip` は `skip` を `X0 ^= nil` に置き換える写像で、実装に `skip` が無いことを明示する
（X0 = nil のとき同じ振る舞い・同じ 1 歩）。

## 4.7 抽出と実測（`extract-si.sh` / `extracted/SI.rwhile`）

検証済みの `SI` を**実際に走る R-WHILE プログラムとして抽出**し、実装 `src/ri` で走らせた。

```sh
cd proofs/agda && ./extract-si.sh          # extracted/SI.rwhile（2,124 行・37 KB）
cd ../../src && ./ri -exp ../proofs/agda/extracted/SI.rwhile      # パース成功
./ri -steps ../proofs/agda/extracted/SI_run.rwhile <input.val>    # 実測
```

`SI.rwhile` は `read X0（todo）; SI; write X1（done）`。`SI_run.rwhile` は入力を
`(todo . store)`、出力を `(done . store)` にする 10 歩のラッパを前後に付けたもの。

**実測と証明された上界 `(CC M + 2)·k`**（ラッパの実費は順方向 20・逆方向 16 歩。
`;` ノードも 1 歩数えるので、代入 5 個のラッパは 10 歩になる。素の `SI` で `skip` が
34 歩であることとの差で実測した）:

| 対象プログラム | M | k | 順方向 | **逆方向** | 上界 | 比 |
|---|---:|---:|---:|---:|---:|---:|
| `skip` | 0 | 1 | 34 | **34** | 3198 | 1.1% |
| `X0 ^= 'a`（定数オペランド） | 1 | 1 | 178 | **178** | 5942 | 3.0% |
| `X1 ^= X0`（変数オペランド） | 2 | 1 | 344 | **344** | 8686 | 4.0% |
| `X0 ^= 'a; X0 ^= 'a` | 1 | 3 | 516 | **516** | 17826 | 2.9% |

- **どの実行も上界の内側**（余裕 25〜90 倍）。`CC M` は「1 対象ステップあたりの一様な予算」で、
  最悪ケース（ループ手順 ＋ 両オペランドが変数で末尾まで歩行）に合わせてあるため。
- **順方向と逆方向の歩数が 4 例すべてで完全に一致**した — `si-uncompute`（`inv SI` は解釈を
  同じ歩数で巻き戻す）の実測による裏づけ。逆方向は `extract-si.sh` が出す
  `extracted/INV_SI_run.rwhile`（入力 `(done . store)`／出力 `(todo . store)` なので
  順方向の出力をそのまま食える）で走らせ、**対象ストアが初期値に戻る**ことも確認した。
- 出力を見ると **done スタックに `⌜c⌝` が組み立て直され、対象ストアが正しく更新されている**
  （例: `X0 ^= 'a; X0 ^= 'a` は可逆性どおりストアを元に戻す）。プログラム保存と正当性の実測確認。
- 実測の `a_p`（対象 1 ステップあたりの解釈系歩数）は 34〜344。手書きの `ri.rwhile`（実測
  a-rev ≈ 364）と**同じ桁**であり、核言語に絞った形式化でも実物並みの効率が出ている。

## 4.75 検証済み解釈系を、型検査器の中で走らせる（`RWhileSIExecTest`）

`exec`（健全かつ完全）で `SI` を実際に走らせ、最終状態と歩数の両方を `refl` で照合する。
**証明された解釈系が本当に計算する**ことの機械検証であり、抽出物の実測（§4.7）と対をなす。

| 対象プログラム | M | k | Agda の実行歩数 | 上界 `(CC M + 2)·k` |
|---|---:|---:|---:|---:|
| `skip` | 0 | 1 | 37 | 3198 |
| `X0 ^= 'a` | 1 | 1 | 182 | 5942 |
| 同（逆向き＝もう一度）| 1 | 1 | **182** | 5942 |
| `X0 ^= 'a; X0 ^= 'a` | 1 | 3 | 525 | 17826 |
| `from =? X0 nil loop X0 ^= '7 until =? X0 '7` | 1 | 4 | 1869 | 23768 |

- ストアが正しく更新され（`[nil] → ['7]`）、done スタックに `⌜c⌝` が組み立て直される。
- 同じ代入をもう一度解釈すると**同じ 182 歩でストアが元に戻る**（可逆性の端から端までの確認）。
- ループの例は `lpA`/`lpD`/`lpB`/`lpZ`/`lpC` の全プロトコルを通る。
- 実行は 0.41 GB・4.8 秒で済む（`exec` は素直な評価なので、型検査器の負担にならない）。
### モデルと実装の歩数の差（実測で確定）

同じ対象プログラムについて、本モデル（`exec`）と抽出テキストの実測（`./ri -steps`、
ラッパ 20 歩を除く）を並べる:

| 対象プログラム | 実装 | モデル | 差 |
|---|---:|---:|---:|
| `skip` | 34 | 37 | 3 |
| `X0 ^= 'a`（定数オペランド） | 178 | 182 | 4 |
| `X1 ^= X0`（変数オペランド） | 344 | 358 | 14 |
| `X0 ^= 'a; X0 ^= 'a` | 516 | 525 | 9 |
| `from =? X0 nil loop X0 ^= '7 until =? X0 '7` | 1821 | 1869 | 48 |

**差は一定ではない**（初期の「1 反復あたり 3」という説明は 1 例からの誤った一般化だった。
変数オペランドの 14、ループ例の 48 が反例）。差の源は、本モデルが `skip` を 1 歩と数えるのに対し
R-WHILE の文法では**空の分岐**として印字され実装が課金しないことにある。したがって差は
**実行された空分岐の個数**に比例し、とくに歩行 `walk`（`from … do skip loop wbody until …`）を
含む実行で大きくなる — 変数オペランドとループ例で差が開くのはこのためである。

重要なのは向きで、**5 例すべてでモデルの側が大きい**（モデルが保守的）。したがって証明した
上界は実装の実行にもそのまま効く。なお**これを定理にはできない**: 実装の歩数の数え方は
形式化の対象外（OCaml は検証していない）なので、比較はあくまで実測どうしの突き合わせである。

## 4.8 印字したテキストは読み戻せるか（`RWhileSIParse` / `RWhileSINorm` / `RWhileSIRoundTrip`）

抽出したテキストが本当に Agda の項を表しているかは、**印字が情報を失わないか**の問題である。
曖昧性が宿るのはトークン列の水準なので、`Rwhile.cf` に沿った構文解析器を Agda 側に書いた
（先頭トークンごとに 1 節・燃料付きで構造的に停止）。トークンは**差分リスト方式**
（`tokV v ts` ＝ v のトークンの後に ts が続く）で生成するので `_++_` が現れず、結合律の
補題が一切要らない。

```agda
pV-ok / pO-ok / pE-ok : 値・オペランド・式の往復
round-trip : ∀ c → RN c → pC (suc (depthC c)) (tokC c []) ≡ just (c , [])
```

**`;` の曖昧性と、その解消**: `showC (c ⨾ d) = showC c ; showC d` は木を平坦化するので
`(a;b);c` と `a;(b;c)` は同じテキストになる。さらに R-WHILE の文法
`CSeq. Com ::= Com ";" Com1` は**左再帰**なので実装の構文解析器は左結合に組み、本開発の
`_⨾_` は infixr である。つまりテキストが表すのは**結合の付け替えを除いて**同じ命令であり、
それが無害であることを `seq-assocʳ`／`seq-assocˡ`（**意味論も歩数も完全に保存**）で示した。

**抽出物への適用**: `SI` は `STEP` が `(pop ⨾ splitT) ⨾ (DISPATCH ⨾ …)` と括られているため
右結合ではない。そこで右結合化 `nf` を定義した:

```agda
nf-tok  : ∀ c ts → tokC (nf c) ts ≡ tokC c ts    -- 印字は完全に同一
nf-⇒    : c ⊢ σ ⇒ τ ∣ k → nf c ⊢ σ ⇒ τ ∣ k       -- 実行も歩数も不変
si-text : pC (suc (depthC (nf SI))) (tokC SI []) ≡ just (nf SI , [])
```

すなわち **`extract-si.sh` が書き出したテキストは `nf SI` を表し、それは意味論が見るかぎり
`SI` そのものである**。

証明を通すために定義を書き直した箇所が 3 つある: (1) 分岐の印字を
`if isSkip c then ts else kw ∷ tokC c ts` に（catch-all 節は `c` の構成子が分からないと
簡約しない）、(2) 構文解析器の先頭判定を `Bool` に（リストの節分けも同様）、(3) `depthC` は
1 命令あたり 2 を数える（`pC → pC1` の委譲で 1 単位使うため）。いずれも
「証明が進むように定義を書く」典型で、定義を変えずに証明だけ書こうとすると詰まる。

## 5. 実装上の教訓（形式化して判明したこと）

- **`with` 抽象を合成で使ってはいけない**。機械状態の型（19 スロット × 符号化プログラム）が
  ゴールに複製され、`simP` の型検査が 44 GB を消費して OOM で落ちた。`where` と明示的な
  射影に書き換えると **400 MB**（最終形で 9.7 GB、92 秒）。
- 上界の算術は別モジュール（`RWhileSIArith`）へ。巨大な型と `Data.Nat.Solver` を混ぜない。
- 結論を `C * k` の形で述べる補題は、`C`・`k` を**明示的に渡す**（暗黙のままだと Agda が
  `_*_` の逆転を試みて `--inversion-max-depth` に当たる）。
- **巨大な項の上で `rewrite` を使わない**。`rewrite` は書き換え対象の出現箇所を照合で探すため、
  37,000 トークンの項では 26.7 GB・154 秒を消費した。motive を明示した `subst` に替えると
  **0.43 GB・5.0 秒**（62 倍の削減）で同じ定理が通る。`with` 抽象で 44 GB を踏んだ件と同根で、
  原則は「**Agda に探させない**」。切り分けも同じ手順: 部分ごとに `/usr/bin/time -v` で測る
  （このときは判定手続き `rn?` の評価が 0.42 GB で無罪と判明した）。
- **`sed`/`python` の無条件置換は黙って空振りする**。本開発では docs の更新が 2 回失われた。
  置換は必ず `assert a in s` で当たりを確認し、直後に `grep` で結果を検証する。

## 5.5 型検査のコスト（`bench.sh`）

`./bench.sh [module …]` が**モジュール単位の再検査コスト**（ピーク RSS と実時間）を出す。

> **計測の罠**: Agda 2.7 以降は interface を `_build/<version>/agda/` に置き、再検査するか
> どうかを**内容ハッシュ**で決める。したがって `touch` では無効化されず、ソースの隣の
> `*.agdai` を消しても何も測れない（どれも約 400 MB＝interface 読み込みだけの値になる）。
> `bench.sh` は `_build` 側の interface を消してから測るので、依存は interface から読みつつ
> **そのモジュール自身のコスト**が得られる。

計測値（`./bench.sh` が生成。`./update-docs.sh --bench` で更新）:

<!-- METRICS:BENCH:BEGIN -->
```
module                         MB        s
RWhileTime                    339     3.58
RWhileTimeDec                 327     3.11
RWhileTimeDet                 334     3.21
RWhileTimeExec                384     5.21
RWhileTimeInv                 376     4.63
RWhileSIArith                 376     3.93
RWhileSIComplete              426     3.44
RWhileSIDet                   422     4.12
RWhileSIEnc                   297     3.33
RWhileSIEval                  418     5.16
RWhileSIExecTest              403     4.32
RWhileSIInv                  8144    58.84
RWhileSILookup                377     4.10
RWhileSIMac                   336     3.83
RWhileSIMach                  492     5.58
RWhileSINorm                  369     4.20
RWhileSIP2D                   523     5.71
RWhileSIParse                 381     5.32
RWhileSIProg                  375     4.25
RWhileSIRoundTrip             426     4.90
RWhileSIRun                   304     2.61
RWhileSIShow                  515     6.01
RWhileSISim                  9499    53.47
RWhileSIStep                 6562    33.50
RWhileSITest                  382     3.77
RWhileSIWalk                  363     3.53
RWhileSIWf                    325     2.99
```
<!-- METRICS:BENCH:END -->

重い 3 モジュールの原因:

| モジュール | 原因 |
|---|---|
| `RWhileSISim` | 合成 `simP`/`simPR` の暗黙引数が巨大な機械状態（19 スロット×符号化プログラム） |
| `RWhileSIInv` | **`si-uncompute` の 1 行**で 7.7 GB（切り分け済み）。`inv-sound` を `SI` に実例化する際に `inv SI` を正規化するため |
| `RWhileSIStep` | 17 のケース定理を具体状態の計算で証明するため |

3 つとも「**Agda が巨大な具体項を正規化する**」ことに帰着する。これはこの開発の様式
（具体的な解釈系＋計算による証明）に固有のものである。

**`embM` を `opaque` にする案は検討のうえ見送った**。実際に構造を調べると、必要なのは
`RWhileSISim` 側の 16 か所の `refl` を補題に替えることだけではなく、

- `RWhileSIStep` の証明部（約 1,100 行）を `opaque unfolding embM` ブロックに入れる＝**全体の
  再インデント**、かつ
- そのブロックの中に入れてはいけない定数関数（`condStep` 594 行目・`lpAStep` 803 行目・
  `assStep` 1030 行目など、`metrics.sh` が**評価する**もの）を**前方に移す再編**

の 2 つが要る。新しい定理は 1 つも増えないので、1,145 行のファイルを組み替える危険に
見合わない。**計測基盤と原因特定を成果とし、この最適化は行わない**と決めた。

## 6. 検証方法

```sh
cd proofs/agda && ./check.sh          # 全 93 モジュール（約 3 分 50 秒）
./check.sh --si                      # この層の 27 モジュールだけ（約 1 分 40 秒）          # 84 モジュール、PASS=84 FAIL=0
./metrics.sh                         # 証明が使っている定数（型検査器に計算させる）
./bench.sh [module …]                # モジュール別の型検査コスト（_build の interface を消して測る）
./update-docs.sh [--bench]           # 上の数値で本書の <!-- METRICS:* --> 区画を書き換える
./extract-si.sh                      # 検証済み SI と inv SI を .rwhile として書き出す
```

実行テスト（型検査器が検証）: `push`/`pop` 各 9、`walk` 2 セル 58、`lkE` 変数 1 で 83（= 56k+27）、
`updE` の可逆更新（2 回で消去）、`opdC` 92/6、`evalC` 227（と再実行で消去＝対合）、
`STEP` の `skip` 34・`seq` 80・`seqE` 81・`loop` 54・`lpZ` 57、機械の 2 例（3 ステップ/4 ステップ、
ループ 4 ステップ/11 ステップ）。

## 7. 位置づけ

- Glück–Yokoyama の主張「R-WHILE には線形時間自己解釈系が存在する」は、上の `si-linear` で
  **機械検証済み・無仮定**（`--safe`、postulate 0、穴 0）。
- `plan_reversible_levin_R3.md` の R3c/R3d を、このリポジトリの言語（R-WHILE）で実施したもの。
  R3e（`while-C-ocaml` の `RevLevinAbstract` へ定数を供給）に接続できる形。
- 実物 `ri.rwhile`（実測 a-rev ≈ 364）との差: 本形式化は `<=` を持たない核言語なので `push`/`pop` が
  `^=` 5 命令になり、定数は実物より大きい。設計（アジェンダ・再組立・タグ代数・compute-use-uncompute）は同一。
