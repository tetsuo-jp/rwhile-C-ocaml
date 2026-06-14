# Partially-static values for spec.rwhile — design (Stage 1 toward fp1/fp2)

作成日: 2026-06-14
目的: spec.rwhile の束縛時（binding-time）表現を拡張し、**部分的に静的な構造値**を扱えるようにする。
これにより第1射影 `[spec]((rint . src))` が解釈系をきちんと特殊化でき（残余が縮約され）、
ひいては第2射影に進める。

## 1. なぜ必要か（根本原因）

現行 SPEC-EXP（`spec.rwhile` 49–216 行）の注釈付き結果は `(A . V)`：
- `A = (nil.nil)`（非nil・真） → **静的**、`V` = 静的値
- `A = nil`（偽） → **動的**、`V` = 残余式コード

`cons` の合成（`consE`, 100–117 行）では：
- 両方静的 → 静的 `((nil.nil) . (V1.V2))`
- **混在・両方動的 → 完全に動的**（静的側は `(cons 'val Vi)` でリテラル埋め込みして捨てる）

つまり **`cons(静的, 動的)` が完全動的化**し、car が静的だったという情報が失われる。
その後 `hd` してももう静的に取り出せず、ディスパッチ（`=? Tag 'ass` 等）が動的化 →
解釈系全体が残余化（ri_fp3 で残余 714KB, cond 343 個）。

部分的静的値があれば `cons(静的, 動的)` を「car 静的・cdr 動的」と覚え、`hd` が静的、`tl` が動的を返せる。
fp1 の入力 `V0 = (prog . data)`（prog 静的・data 動的）を最初の `cons Prog Data <= V0` で
分解した瞬間に Prog が**完全静的**になり、デコード/ディスパッチが静的解決される。
→ peel ハックも ri_fp3 の prelude ハックも不要になる（本筋）。

## 2. 新しい注釈付き値（AV: annotated value）— 再帰的・自己タグ付け

現行の `(A . V)` 2値エンコードを、再帰的に自己記述する単一木 AV に置き換える：

```
AV ::= ('S . v)            -- 完全静的。v は素の値（さらに AV を含まない）
     | ('D . code)         -- 動的。code は残余式コード（'var/'val/'cons/'hd/'tl/'eq ...）
     | ('C . (av1 . av2))  -- cons。av1, av2 は AV（部分的静的を表現）
```

タグに atom `'S` / `'D` / `'C` を使い、現行の nil/(nil.nil) の 2 値判定と衝突しないようにする
（現行 `if A then` 方式は廃止し、`=? Tag 'S` 等の 3 分岐に統一）。

### 正規化規則
- `cons(av1, av2)`:
  - 両方 `'S` → `('S . (v1.v2))`（完全静的に畳む）
  - それ以外 → `('C . (av1 . av2))`
- `hd(av)`:
  - `('S . (h.t))` → `('S . h)`／`('S . leaf)` は静的エラー（実行時 hd エラーに対応）
  - `('C . (a1.a2))` → `a1`
  - `('D . code)` → `('D . ('hd . code))`
- `tl(av)`: 対称（`'C` → a2、`'S.(h.t)` → `('S.t)`、`'D` → `('D.('tl.code))`）
- `eq(av1, av2)`:
  - 両方が完全静的（`av_to_static` が成功＝'D を含まない）→ 比較して `('S . bool)`
  - それ以外 → `('D . ('eq . (lift av1 . lift av2)))`
- `var k`: ストア slot（AV）をそのまま読む
- `val v`: `('S . v)`

### LIFT（AV → 残余式コード）
動的文脈で AV をコードへ落とす関数 `lift`:
- `('S . v)` → `('val . v)`
- `('D . code)` → `code`
- `('C . (a1.a2))` → `('cons . (lift a1 . lift a2))`

## 3. 変更が必要な箇所（spec.rwhile）

| 箇所 | 変更 |
|---|---|
| ストア Vl の slot | `(nil.nil)`/`((nil.nil).v)` → AV（初期 dynamic = `('D . ('var.k))`? 要検討。むしろ slot は「その変数の現在 AV」） |
| `SPEC-EXP-STEP` 49–216 | `var`/`val`/`cons`/`hd`/`tl`/`eq` を §2 の AV 規則に全面書換 |
| `SPEC-STEP` の `'ass` 393–437 | `if AnnK/AnnE then` の 2 分岐 → AV による更新。静的×静的 update、動的なら residual + slot を `'D` 化 |
| `'rep` 442–460 + `CHECK-PAT-STATIC`/`PAT-READ`/`PAT-WRITE` | パターンを AV 上で読み書き。部分静的 slot からの cons パターン分解が肝 |
| `'cond`/`'loop` のテスト 477–… | テスト AV が完全静的なら分岐確定、そうでなければ residual |
| `LIFT`（既存） | §2 の `lift` に統一 |
| Vl 初期化（698 行）/ クリーンアップ（815 行 `Vl ^= Vl`） | 初期値 = 全 slot 動的 AV。クリーンアップは self-XOR のままで可 |
| 入力設定（normal/partial） | peel を撤去し、read 変数 slot に AV を直接設定。fp1 は `V0 = ('C . (('S . prog) . ('D . ('var . 0))))` 相当を与える（prog 静的・data 動的） |

## 4. 後方互換と移行戦略

現行の 2 値エンコードと新 AV は非互換のため、**spec.rwhile の SPEC-EXP/SPEC-STEP/PAT を一括で AV に移行**する必要がある。段階的テスト：

1. AV ユーティリティ（cons/hd/tl/eq/lift/正規化）を macro 化し、`spec-macros` 流の単体テストで検証。
2. `SPEC-EXP` を AV ベースに置換 → SPEC-EXP の単体テスト（静的/動的/部分静的）で検証。
3. `SPEC-STEP` の ass/rep/cond/loop を AV 対応に置換 → spec-partial（swap）が通ることを確認。
4. 入力設定を AV 直接指定に変更（peel 撤去）→ fp1(id/swap) を green に。
5. fp1(reverse)・ri_fp3 で残余が縮約されることを確認。
6. ri.rwhile（配列ストア）でも改善するか確認（動的インデックスは別問題として残る可能性）。

## 5. リスクと注意

- spec.rwhile は**可逆プログラム**。AV の各操作を可逆に書く必要があり、特に「正規化（両静的なら畳む）」
  の分岐は可逆性を壊しやすい。各 if は対応する exit assertion / クリーンアップが要る。
- 既存で通っている `spec-partial`（swap）を壊さないこと。各段階でテスト。
- これは複数セッション規模。1 ステップずつコミット可能な単位で進める。

## 6. 進捗

### ステップ1 完了（2026-06-14）: AV 代数の実装と検証 ✅
`examples/av.rwhile` に非再帰 AV 演算 `AV-CONS`/`AV-HD`/`AV-TL` を可逆 R-WHILE で実装し、
単体テスト（TestSuite の `av-algebra` 群6件）で検証済み。可逆性（store invariant）も維持。
実証された核心：
- `cons ('S.'a) ('D.x)` → `('C.(('S.'a).('D.x)))`（**静的 car を保持**。現行 spec はここで
  完全 dynamic 化していた）
- その `hd` → `('S.'a)`（静的部を復元）、`tl` → `('D.x)`（動的部）
これにより「静的×動的の cons → 後で静的部を取り出せる」ことが可能になり、過剰残余化を解く
土台ができた。

### 次の一手
ステップ2: `SPEC-EXP`（spec.rwhile 49–216）を AV ベースに置換。まず `av.rwhile` の AV 演算を
spec.rwhile に取り込み、SPEC-EXP の var/val/cons/hd/tl/eq を AV 規則へ。LIFT と eq の全静的判定は
再帰が要るためスタックマシン化（既存 SPEC-EXP の B/E マーカー方式を踏襲）。spec-partial(swap) を
壊さないこと。
