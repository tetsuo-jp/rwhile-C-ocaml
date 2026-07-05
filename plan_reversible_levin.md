# 可逆 Levin（R-track）— rwhile-C-ocaml 側の受け口と役割分担

作成日: 2026-07-05。**正本は `while-C-ocaml/docs/REV-LEVIN-SKELETON.md`**（設計・定理候補・
再利用マップ・補題順序はすべてそちら）。本ファイルはその要約と、**このリポジトリが担当する部分**の
メモ。fork しない — 設計変更は正本側を更新し、ここには役割の差分だけ書く。

## 何が起きたか（2026-07 時点）

古典側（`while-C-ocaml`）で **Levin の定理（Jones Thm 20.1.2）の機械検証が完結**した:
Agda 59 モジュール + Rocq 22 モジュール（公理ゼロ）、自己解釈器の線形オーバヘッド
**a = 73 が定理**（`IntEfficient` / `IntEfficientR`）。その上で**可逆 Levin**（R-track）が
開始され、抽象ブリック R0 が証明済み（`proofs/agda/RevLevinAbstract.agda`, `--safe`）:

- **R0a** 最適性の抽象層（Layer A）はコストモデル非依存 — 可逆版のオーバヘッド定数
  `a-rev` を入れるだけで最適性不等式がそのまま発火する。**時間最適性は定数 1 個に還元済み**。
- **R0b** Bennett 埋め込み `⟨id, f⟩` は常に可逆実現（ガーベジ上界 = 入力、値レベル）。
- **R0c** 証人を共有する探索に**クリーンな可逆実現は存在しない**（Theorem A、下界）。

つまり可逆 Levin は「**時間最適性（a-rev 待ち）+ ガーベジ挟み撃ち |fibre| ≤ g ≤ |input|**」
という*対*の定理になる — 最適性とクリーン性は両立不能で、このトレードオフが Jones を超える
新規部分。

## このリポジトリ（rwhile-C-ocaml）の役割

分業は既存の proven-vs-tested 方針のまま: **形式化（REXP・step count・可逆 sint ⇒ a-rev）は
while-C-ocaml/proofs/agda 側で自己完結に行い、rwhile は実行系・実測・差分クロスチェックを担う**。

1. **`examples/ri.rwhile`（可逆自己解釈器）= R3 の実行的クロスチェック。**
   古典側の a=73 も「実測 → 証明」の順で進んだ（probe で定数を測ってから `SintCost` で固定）。
   同じ順で、**a-rev の実測が rwhile 側の最初の具体タスク**:
   - `src/EvalRwhile.ml` に `eval_steps`（コマンド単位の step カウンタ）が既にある。
   - 数本の被解釈プログラム p × 入力 x で `steps(ri, ⌜p⌝·x) / steps(p, x)` の比を取り、
     その上限（= a-rev の経験値）を出す。古典側の 73 との比較が最初の科学的成果物
     （可逆化のオーバヘッド係数が古典比で何倍かは誰も知らない）。
   - 成果は本ファイルに追記 + 正本の R3 節に反映。
2. **Theorem A 側の対応はすでにこちらにある。**
   `RWhileRevProjGen` / `RWhileGarbageBound`（input-preserving 上界）は R0b の Bennett
   値レベル上界の rwhile 版そのもの。R-track はこの既存 bracket を「探索の witness map」で
   読み替えただけ — 新しい概念は不要（正本の R2 節）。
3. **REXP は R-WHILE の完全な構文モデルにはしない**（正本のリスク節）。Agda 側の REXP は
   `UniversalInterp` 流の最小自己完結言語で、`ri.rwhile` は差分テストの oracle という位置づけ。
   ゆえに rwhile 側の Agda（33+ モジュール、`funext` のみ仮定）に R-track の証明義務は発生しない。

## 最初のタスク（このリポジトリ、サイズ S）

`a-rev` 実測スクリプト（例: `examples/measure_ri_overhead.sh`）:
p ∈ {swap, reverse, …（`examples/` の小物）} × 数入力で
`steps(ri ⌜p⌝·x)` と `steps(p, x)` を出力し比を表にする。
注意: ri の入力エンコード（⌜p⌝·x の形）と step の数え方（コマンド単位）を正本の
コストモデル（batch model (A)、unit-cost）と揃えて記録すること — 数え方が違うと
古典 73 と比較できない。

## 参照

- 正本: `while-C-ocaml/docs/REV-LEVIN-SKELETON.md`（設計全体）
- 抽象ブリック: `while-C-ocaml/proofs/agda/RevLevinAbstract.agda`（R0a/R0b/R0c）
- 古典チェーン: `while-C-ocaml/docs/AGDA_CORRESPONDENCE.md` §Rocq cross-check
  （Agda↔Rocq 対応、a=73 が両系で定理）
- こちら側の関連: `RWhileRevProjGen`/`RWhileGarbageBound`（ガーベジ bracket）、
  `analysis_store_bti.md`（両リポジトリが同じ壁を相互検証した前例）
