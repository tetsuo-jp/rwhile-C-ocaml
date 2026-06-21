# 案1 候補(A) の他言語実証と移植スケッチ（while-C-ocaml 参照）

2026-06-21。`analysis_store_bti.md` §3 の候補(A)（環境の partially-static 化）は、
**古典（非可逆）側の姉妹リポジトリ `while-C-ocaml` で実機実証済み**。本書はその成果と、
`spec_av_bti.rwhile` への移植の要点（＝可逆性の差分）をまとめる。書き手が別repoなので、
ここでは設計参照のみ。実装は fp1 ゲートを緑に保ちつつ刻む（§4 のプロトコル）。

## 1. 同じ壁だった（独立に再現）

`while-C-ocaml` の自己解釈器 `universal.while` を `cogen --online` で特殊化すると、
被験体に依らず残差が ~265KB・主ループ残余化。診断は本書 §1 と同型：
**ストア index（内側プログラムポインタ `Cd` 由来）が動的化** → 変数店の歩行ループが残余化。
静的命令列では `#while=0`（＝ループ機構は健全）も同じく確認済み。つまり
「index/プログラムポインタの動的化」が唯一の真因、というここの結論は**言語をまたいで成立**する。

## 2. 候補(A)+(B) を古典側で解いた構成

二つの facet を組み合わせて解決した（`while-C-ocaml` `docs/FUTAMURA.md`, `usi.while`,
`src/core/Cogen.ml`）：

- **(B) プログラムポインタを静的に保つ — `usi.while`（単一 scrutinee ディスパッチ）。**
  本書 §2「漏れ点」は `case Cd, St of` の合成ガード：脱糖が Cd テストと St テストを
  **非短絡 AND** で連言化し、動的な値スタック St が静的な Cd ディスパッチの束縛時刻を汚染する。
  対策は **ディスパッチを Cd 単独に**（`case Cd of`、St は各腕で hd/tl/cons 直接アクセス、ガードに出さない）。
  すると Cd（=静的プログラム）のガードが畳まれ、主ループが展開＝Cd が静的に保たれる。
  （`universal` を書き換えず別ファイル `usi.while` として実証。`spec_av` でいえば
  `SPEC-EXP-AV-STEP` の `'var => LOOKUP(Vl,EArg,SX)` で EArg を outer から静的に保つこと＝(B)。）

- **(A) partially-static 店 — spine-preserving emit（`Cogen.ml`）。**
  「静的 cons スパイン＋動的葉」を持つ値（店 Vl など）を emit するとき、スロットを
  **同形スパインで各動的葉を「自スロット変数への hd/tl パス（self-reference）」に置換**して保持。
  Sv 部（スパイン終端含む）は静的に残す。これでスパインが既知化＝index 静的な LOOKUP/UPDATE の
  歩行が**展開され消える**。健全性は emit-model（自己参照スロットは他変数の再具現化に安定）で、
  機械検証済み：`while-C-ocaml/proofs/agda/SpinePreservingEmit.agda`（`readback`＝忠実再構成、
  `stable`＝健全、`cross-unsound`＝対照）。**ただし residualized 動的制御の内側では実行時スパイン長が
  変わり得るため自己参照は不健全**→そこは従来通り単一動的参照に潰す（=(A)の「index 動的→残余ループ」）。

- **停止性**：(A) で静的展開が増えるため、BTA に widening（C 領域の無限上昇鎖を打ち切り）＋
  有界展開＋一般化フォールバックを併用。widening は機械検証済み（`BTAWiden.agda`）。

### 実証結果（古典側）
`[cogen --online](usi, swap)` = **#while=0・#eq=0**（ループフリー）・解釈比 ~30×、正しい。
`universal`（合成ガード版）は依然 1 ループ（=ここの comp2 と同じ未解決＝PP memoization 待ち）。
つまり (B) を効かせた `usi` で初めて (A) が活き、ループが完全に消えた。

## 3. 可逆側（spec_av_bti）への移植：差分は「静的選択を可逆に」

古典側の (A)/(B) はそのまま使えるが、R-WHILE は可逆制約があるため次の二点を追加で守る：

1. **静的選択（展開された LOOKUP/UPDATE）を可逆代入で。** index が静的 AV のとき `AUX` 歩行を
   特殊化時に unroll するが、各スロットアクセスは `X ^= X` 系の自己クリアを使わず、
   既存の `SWAP-VIA-TEMP`（naive-swap 衝突対処と同系統）で行う。本書 §3(A)「可逆性：静的選択も
   SWAP-VIA-TEMP 系で」と一致。
2. **self-reference 葉の可逆対応。** 古典の「動的葉＝自スロットへの hd/tl パス」は、可逆側では
   「スロット更新後にその葉を自身の var の部分から読む」読み出しパターン（`PAT-READ-ITER` の深さ一般化）
   として残余化する。emit-model のクロス参照禁止（他変数を参照しない）は、可逆側の uncompute 規律と整合
   （`FINDINGS §5` の dead-path 退避とは別レイヤ：こちらは**生きた**残差の store 機構の話）。

### 刻み（fp1 ゲート緑を維持、本書 §4 に従う）
- step1：(B) 観測。`spec_av_bti` で `EArg` の AV タグを観測し、自己適用下で 'D 化する箇所を1つ特定
  （本書 §2 の漏れ点 L333 ほか）。Cd 単一ディスパッチ化が大きすぎるなら、まず LOOKUP/UPDATE の
  index 引数だけを「静的なら unroll」に二相化（(A) の最小版）。
- step2：固定小ストア（ri_min 規模）で (A) を実証 → `measure_proj full` で CLoop≪125 を確認。
- step3：一般化＋ fp2/fp3 緑（d2p 直接評価で byte 一致）＋ INV round-trip。
- 各 step で `./measure_proj gate ../examples/spec_av_bti.rwhile` が `GATE PASS`。崩れたら即 revert。

## 4. 参照
- 古典側実装・証明：`while-C-ocaml/examples/desugar/usi.while`、`src/core/Cogen.ml`
  （`selfref` を含む emit 枝、`widen`）、`proofs/agda/SpinePreservingEmit.agda`・`BTAWiden.agda`、
  `examples/desugar/test-usi.sh`・`test-bench.sh`、`docs/FUTAMURA.md`・`docs/AGDA_CORRESPONDENCE.md`。
- ここの該当：`analysis_store_bti.md` §3(A)/(B)、`FINDINGS_reversible_projections.md` §2、
  `RWhileRevProj2BT.agda`（束縛時刻の真因）、`src/measure_proj.ml`。
