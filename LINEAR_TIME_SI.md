# R-WHILE の線形時間自己解釈系 — Agda 形式化（2026-08-04）

Glück–Yokoyama の *A linear-time self-interpreter of a reversible imperative language*
の主張「**R-WHILE には線形時間の自己解釈系が存在する**」を、定理証明系（Agda 2.8 /
stdlib、`--safe`・postulate 0・穴 0）で機械検証する開発。**自己解釈系は抽象機械ではなく、
対象言語そのもので書かれた 1 本の R-WHILE プログラム**である。

新規モジュール（`proofs/agda/`、全 17 本・約 4,900 行、`./check.sh` は PASS=83 FAIL=0）:

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
（見積りではない）。現在値（2026-08-05）:

| 定数 | M=0 | M=1 | 傾き |
|---|---:|---:|---:|
| `CC` | 3196 | 5940 | 2744 |
| `lpDStep` | 464 | 912 | 448 |
| `lpAStep` | 444 | 892 | 448 |
| `assStep` | 429 | 933 | 504 |
| `condStep` | 445 | 893 | 448 |
| `condEStep` | 470 | 918 | 448 |
| `evalB` | 179 | 403 | 224 |

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

## 5. 実装上の教訓（形式化して判明したこと）

- **`with` 抽象を合成で使ってはいけない**。機械状態の型（19 スロット × 符号化プログラム）が
  ゴールに複製され、`simP` の型検査が 44 GB を消費して OOM で落ちた。`where` と明示的な
  射影に書き換えると **400 MB**（最終形で 9.7 GB、92 秒）。
- 上界の算術は別モジュール（`RWhileSIArith`）へ。巨大な型と `Data.Nat.Solver` を混ぜない。
- 結論を `C * k` の形で述べる補題は、`C`・`k` を**明示的に渡す**（暗黙のままだと Agda が
  `_*_` の逆転を試みて `--inversion-max-depth` に当たる）。

## 6. 検証方法

```sh
cd proofs/agda && ./check.sh          # 82 モジュール、PASS=82 FAIL=0
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
