# 可逆 Levin R3 — このリポジトリへの引き継ぎ（可逆自己解釈器 → a-rev を定理化）

作成日: 2026-07-06。**R3（可逆 Levin の最後の深い brick）を while-C-ocaml から本リポジトリ
（rwhile-C-ocaml）へ引き継ぐ。** 理由: R3 の核心は「可逆自己解釈器の線形オーバヘッドを定理化」
することで、本リポジトリには既に**実行可能な可逆自己解釈器 `examples/ri.rwhile`** と**可逆意味論の
Agda 形式化**（`RWhileRev*`/`RWhileExec*`/`RWhileValStore`）がある。R3c–R3e はここで進めるのが最短。

正本の設計は `while-C-ocaml/docs/REV-LEVIN-R3-PLAN.md` と `REV-LEVIN-SKELETON.md`。本ファイルは
それを本リポジトリの資産に接続する引き継ぎメモ。既存の `plan_reversible_levin.md`（a-rev 実測の
受け口）の続編。

## いま可逆 Levin はどこまで来たか（2026-07 時点、全て公理ゼロ）

`while-C-ocaml/proofs/agda`（Agda `--safe`）:
- **R0** `RevLevinAbstract`: Layer A が抽象 `a-rev` で発火（時間最適性を単一定数に還元）＋ ガーベジ
  挟み撃ち `|fibre| ≤ g ≤ |input|`（Theorem A）。
- **a-rev 実測 ≈ 364×**（本リポジトリ `examples/measure_ri_overhead.sh` = `ri.rwhile` の
  `steps(ri,⌜p⌝·x)/steps(p,x)`、非自明 5 被解釈体の平均、範囲 228–466、サイズ非依存）。
- **R1a/R1b/R1c** `RevCore`/`RevXor`: 最小可逆言語＋`inv-sound`（`bwd∘fwd=id`）＋step count＋
  **時間対称性 `cost-sym`**（後向き=前向きコスト）＋ Bennett 入力保存コピー（GF(2) 全域＋木部分）。
- **R3a+R3b** `RevInst`（新規、2026-07-06）: **具体的で encodable な可逆命令言語 `RCmd`**
  （`swp`=部分木交換, `sq`, `ifn`=nil 分岐）。全命令が nil 性を保つので `inv-sound` は**無条件**。
  `cost`/`cost-sym`、そして **`⌜_⌝ : RCmd → V` + `decode` + `decode-⌜⌝`**（自己解釈器が食う encoding）。

**残るのは R3c–R3e のみ**（＝ここでの仕事）。

## なぜ本リポジトリで R3c–R3e をやるのか

R3 の設計ブロッカーは解決済み（抽象 `Upd`=関数は encode 不能 → `RevInst.RCmd` で有限構成子・
encodable にした）。次は:
- **R3c 可逆自己解釈器**: 本リポジトリの `examples/ri.rwhile` が**まさにそれ**（実行可能・program-
  preserving・r-Turing complete）。`while-C-ocaml` 側で新規に書くより、`ri.rwhile` を Agda で
  形式化する方が筋が良い（既存の `RWhileExec`/`RWhileRev` が土台）。
- **R3d a-rev 定理**: `ri.rwhile`（または `RCmd` 自己解釈器）の**線形オーバヘッド `time_ri ≤ a-rev·time_p`**
  を証明。実測 ≈364× が目標値、設計指針は「1 命令の解釈コストを変数リスト `Vl` 走査で上から押さえる」
  （`plan_reversible_levin.md` の実測考察）。
- **R3e 閉じる**: 証明した `a-rev` を `while-C-ocaml` の `RevLevinAbstract.rev-levin-optimal`（抽象
  `a-rev` で発火する Layer A）に食わせ、**無条件の可逆 Levin 最適性**に。ガーベジ挟み撃ち（R0b/c）と
  合わせて時間↔ガーベジ**トレードオフ定理**を完成 —「初の機械検証・可逆探索最適性」。

## 本リポジトリの資産 → R3 brick の対応

| R3 brick | 使える本リポジトリの資産 |
|---|---|
| R3c（可逆自己解釈器の形式化） | `examples/ri.rwhile`（実体）、`proofs/agda/RWhileExec*.agda`（実行意味論）、`RWhileRev*.agda`（反転の健全性 `inv-sound`/`inv-inv`）、`RWhileValStore.agda`（`RAss-sym`=`^=` の部分対合）、`RWhileCoreExp`/`RWhileP2D*`（プログラム↔データ） |
| R3d（a-rev 定理＝線形オーバヘッド） | `src/EvalRwhile.ml` の `eval_steps` と `examples/measure_ri_overhead.sh`（実測データ・回帰）、`while-C-ocaml` の古典 `IntEfficient`(a=73)/`CostRelation`/`SintCost` が**証明テンプレート**（Steps 帰納＋per-op dispatch 定数） |
| R3e（閉じる） | `while-C-ocaml/proofs/agda/RevLevinAbstract`（`rev-levin-optimal` at abstract a-rev — ここに証明済み定数を食わせるだけ）＋ `LevinGrounded` の書き方が雛形 |

**verbatim 再利用（コストモデル非依存、`while-C-ocaml` 側で証明済み）**: `LevinBudget`/`NatPairing`/
`LevinOptimal`/`LevinDovetail*`/`LevinComplete`（古典 11 層中 6 層）。R3e はこれらを触らない。

## R3d の証明戦略（古典 a=73 の可逆版）

古典 `IntEfficient.int-efficient` の構造をなぞる:
1. **可逆 step count 意味論**（`RWhileExec` を step 計数版に、or `RCmd` に `evalT` を足す）。
   本リポジトリの `eval_steps` は既にコマンド単位のカウンタ。`while-C-ocaml` の `StepCount`/
   `StepCountMono`（`evalT-mono` 済み）が雛形。
2. **big-step コスト関係 `Steps`**（`CostRelation` の可逆版）: 各命令 1 rule、部分実行は opaque premise。
3. **per-op dispatch 定数**（`SintCost` の可逆版）: `ri`/`rsint` の各命令解釈の実 step 数。実測が示唆
   するのは「`Vl`（~75-nil 変数リスト）の `LOOKUP`/`UPDATE` 走査が支配」→ その定数を出す。
4. **`int-efficient-rev`**（`IntEfficient` の可逆版）: `Steps` 帰納で `time_rsint ≤ a-rev·time_c`。
   `a-rev = max per-op 定数`（古典の a=73=max と同じ構図）。`cost-sym`（R1b）で前向き=後向きなので
   片側の bound で足りる。
5. Rocq への移植も自然（古典側で `SintCostR` の `vm_compute` カスケード技法が確立済み）。

## リスク／注意

- 可逆自己解釈器の**正当性の形式化**（`ri.rwhile` が本当に `⟦p⟧` を計算し program-preserving）が
  R3c の山。`ri.rwhile` を `RCmd`-流の最小言語に絞ると tractable（`RevInst` はその最小版）。
  `ri.rwhile` フル（マクロ・`Vl`）は L。
- `a-rev` の正準コストモデルを決める（コマンド単位 vs node-summed）。定理は「線形オーバヘッドの
  存在」で、定数は二次的（古典 a=73 と同じ）。
- 本リポジトリの Agda は `funext` のみ仮定（`postulate` は funext のみ）。R3 の新規モジュールも
  `--safe`・公理ゼロを保つこと（`while-C-ocaml` 側は funext すら不使用）。

## 進め方（各 brick は緑コミットで区切る）

1. **R3c-min**: `RevInst.RCmd` の自己解釈器 `rsint : RCmd`（`⌜c⌝` を解釈）を書き、`inv-sound`/
   走行を refl で（`while-C-ocaml/SelfInterp` の作り方が雛形。ただし `RCmd` 版）。または `ri.rwhile`
   を Agda 形式化。
2. **R3d**: 上の step count ＋ per-op 定数 ＋ `int-efficient-rev`。
3. **R3e**: `RevLevinAbstract` に食わせて `rev-levin-optimal` を無条件化 → 定理完成。

## 参照

- 正本設計: `while-C-ocaml/docs/REV-LEVIN-R3-PLAN.md`, `REV-LEVIN-SKELETON.md`
- R3a+R3b（encodable 可逆言語）: `while-C-ocaml/proofs/agda/RevInst.agda`
- 基盤: `RevCore.agda`（inv-sound/cost-sym/Bennett/iterC）, `RevXor.agda`（部分対合 `^=`）,
  `RevLevinAbstract.agda`（R0）
- 実測: 本リポジトリ `examples/measure_ri_overhead.sh`, `plan_reversible_levin.md`
- 古典テンプレート: `while-C-ocaml` の `StepCount`/`StepCountMono`/`CostRelation`/`SintCost`/
  `IntEfficient`/`LevinGrounded`

## 進捗更新 + 残り R3d/R3e の分解（2026-07-06）

引き継ぎ後、while-C-ocaml 側の並行セッションで大きく前進（全て green・公理ゼロ・コミット済み）:
- **R3c step 1 完了**: `RevSelfInterp.agda` — 意味論的自己解釈器 `usint`（fuel 付き tag dispatch）
  + `usint-correct` + 無償の `usint-reversible`。
- **R1a'-guard 完了**: `RevLoop.agda` — データ依存可逆ループ + `inv-sound`。
- **R3c step 2 の brick 1–2 完了**: `RCmdL.agda`（ループ付き encodable 一階可逆言語）+
  `RCmdLEnc.agda`（encoding round-trip）。
- **R3d fuel レベル完了**: `RevSintCost.agda` — **`int-efficient-rev : size c ≤ n →
  usintC n ⌜c⌝ s ≤ a-rev · ocost c s`（a-rev = 4）**。driver レベルの線形オーバヘッドは定理に。

**残りの分解（3トラック・各 brick は緑コミット単位）**: 正本
`while-C-ocaml/docs/REV-LEVIN-R3D-BRICKS.md` 参照。要旨:
- **Track 1（今すぐ・S+S）**: R3e driver レベル — `RevLevinGrounded`（`LevinGrounded` の
  双子、a-rev=4 を Layer A に食わせる）+ トレードオフ束ね（× no-clean × Bennett 上界）
  → **可逆 Levin 定理が driver レベルで主張可能に**。
- **Track 2（364× モデル）**: 抽象ストア（lookup/update コスト = 長さ L の walk、S1）+
  **汎用線形オーバヘッド補題**（per-op 課金 κ≤K ⇒ icost ≤ suc K·ocost、一度だけ証明して
  3 回使う、S2）+ 多変数言語 S3 + ストア持ち回り解釈器 S4（per-op ≤ k+2L = Vl-walk 指針の
  補題化）→ **a-rev(L) はストアサイズに affine**（L≈75 で実測 364× の形、S5）。
- **Track 3（プログラムレベル rsint）**: **可逆 defunctionalization** — fuel の再帰を
  agenda ループ（todo/done スタック + store）に。todo→done の移動が単射性を保ち、
  **done スタックこそ Bennett ガーベジ**（R0b の具体化 = ri.rwhile が (⌜p⌝ . result) を
  出す理由そのもの）。P1 costL → P2 メタ agenda ≡ usint → P3 RCmdL 本体 → P4 反復数
  bound ⇒ プログラムレベル a-revL → P5 コストモデル正準化。

順序推奨: E1→E2（定理主張）→ S2（共有補題）→ Track 2/3 は並行可。
