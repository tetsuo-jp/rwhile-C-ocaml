# 可逆二村射影 — 残った研究課題とロードマップ

論文 `2025_Reversible_Projection_IEICE_D`（Okubo–Yokoyama, IEICE-D 論文版）に紐づく
研究課題の統合ロードマップ。2026-07-09 時点。一次情報＝論文「おわりに」・
`FINDINGS_reversible_projections.md` §8・`proofs/agda/`・研究方針メモ。

参照メモ: `research-development-ideas-2026-06`（5案）、`second-futamura-projection-status`
（fp2/fp3 詳細）、`reversible-levin-rtrack-status`（R-track）、`methodology-agda-first`
（Agda 先行方針）、`research-direction-core-language`（記述=R-WHILE / 証明=小コア / 橋=意味保存翻訳）。

---

## 0. 直近で解けたもの（除外）

- **fp1/fp2/fp3 実機 GREEN**（spec_av、d2p 直接評価判定、byte 一致）。
- **spec_av_rev（可逆版 PE）の自己適用 fp2/fp3 GREEN**（2026-07-06, commit `2ce7cc6`、
  NewV deloc→CLEAR 修正）。native+Map 高速化で fp2-rev 689s→16s、fp3-rev 完走 109s。
- **②の理論障害は解消済み**：`RWhileH2Fuel`（fuel-indexed route A）、`RWhileH2Worklist*`
  （実 spec_av ワークリスト＝ループ機構＋AV 全代数＋partial-static 多スロット store＋γ健全性
  の四要素）、`RWhileH2HierOpt`（非自明 fp2/fp3 が証明済定理）。全56モジュール --safe・公理ゼロ。

---

## 1. 中核フロンティア（この研究の主軸・最優先）

### ① 本物の Futamura 利得＝最適化する可逆スペシャライザ〔必達目標・本論文で達成すべき〕
現状 `rspec` は Jones の自明スペシャライザで `comp2 ≈ 1×|spec|`。コンパイルが解釈より速い
という御利益が**可逆世界で未実証**。2段の独立課題に分解済み（2026-06-25 fb965fd で確定）:

- **(1) ループ trivial 化＝解決済み**：selective dynamicize＋loop-BTA で
  `comp2` を 0.994×→**0.005×**（CLoop 125→4）。`spec_av_bti.rwhile`（dev WIP）。
- **(2) 原 fp2 over-static 束縛時刻バグ＝未解決・本丸**：`spec_av.rwhile:1051` の
  `FpPart <= cons 'C (cons (cons 'S Src) …)` が Src を**無条件に `'S`（静的）で固定タグ**。
  fp1 では Src は実際に静的で正しいが、fp2 では OUTER から見て inner の Src(=d) は**動的**なのに
  'S 固定 → 束縛時刻の不整合。DYNAMICIZE-ALL がこれを（全 runtime 実行で）マスクしていたのを
  selective+loop-BTA が unmask（`[comp2]('S.swap)` が 'swap を値埋め込みし ri_min の cond を
  dispatch しない誤コンパイラを出す）。
  - **根本**：online/値運搬型 AV（`'S` タグ付き AV が具体値を運ぶ前提で AV-LIFT/AV-EQ/AV-HD…が
    処理）と offline/二段階 BT 分離（'S は「静的位置・存在保証だが記号的でよい」）の本質的不整合。
  - **真の修正**：AV 代数に「静的・存在保証だが記号的」区分を入れる offline 化（大規模研究）。
    MKAV を congruence 駆動（BT=dynamic なら S でなく D/記号 AV を出す）に。
  - **会場**：RC / PEPM / IEICE 続報。

### ② 完全 spec_av の自己適用を Agda で閉じる〔機械検証の本丸・理論は済〕
H1（spec 正当性）・H2 核（`RWhileH2HierOpt` で fp1/fp2/fp3 が証明済定理）・fuel/worklist モデル
（route A）まで達成。**残るは本番 OCaml/R-WHILE 実装との対応づけ（工学）**＝実 spec_av の
有界ワークリストを `RWhileH2Worklist*` の `runF`/関係モデルへ具体対応させる証明。会場: CPP/ITP/ESOP。

---

## 2. 論文が「おわりに」で明示している課題

### ③ ゴミ除去（Bennett 逆計算との組合せ）＋ゴミ下界のタイト化
各特殊化段で出力に入れ子状に蓄積するプログラム符号列（＝可逆計算のゴミ）を Bennett 法の
逆計算で消す手法との統合が未着手。関連: 下界 `|garbage| ≥ |fiber|`（`RWhileGarbageBound.agda` 済）
に達成可能性の上界を足しタイト化、g-極小クリーン生成を構成的に、Landauer 消去ビットへ接続。
`spec_av_rev`（dead-path ゴミ埋込）は実機プロトタイプあり（1739→755 nodes, −57% まで最小化済）。

### ④ 可逆射影のより詳細な性質の精査
第1/第2/第3可逆射影の代数的性質・合成則・最適性など、論文が留保した部分。

---

## 3. スケール／基盤／探索

### ⑤ 完全自己インタプリタ ri.rwhile の特殊化停止性
深い入れ子パターンで発散。オフライン PE の「静的配置有限」を AV 配置で定式化し、発散軸を `'D` に
格下げする一般化（`case` 判別子で停止判定）。①②を自明でない自己インタプリタへスケールさせる前提。

### ⑥ 可逆 Levin 探索（R-track, 別トラック・正本 while-C-ocaml）
Agda ブリック（RevSintCost の a-rev 定数、full-run 反転、program-level a-rev）完了。残 crux＝
**rsint 本体**（richer atom＋スタックマシンの設計）と **364× の Vl モデル**。可逆 Levin 定理
（時間最適性＋ゴミブラケット |fibre|≤g≤|input|）を実機レベルで閉じる。

### ⑦ 量子アンシラ/Landauer 接続 or 逆射影の符号一致〔高リスク探索〕
(a) 射影ゴミ ↔ 量子 ancilla/uncompute コスト、(b) Glück–Normann 2024「逆は符号列一致」を可逆へ
拡張「ゴミ一致 ⇒ 残余符号列一致」。Q-Intent/QDSL と接続。

---

## 4. 直近成果に紐づく小課題

- **spec_av_rev fp2/fp3 は GREEN だが遅い**（native+Map で大幅改善済だが、①の BTI と両立する
  最適化は未検討）。
- **ri.rwhile bug2（自己クリア `X^=X` 非可逆）**：残余から self-clear を排せば `run_via_ri` が
  忠実に（`spec_av_rev` 方式）。ツール側一般化が残課題。判定は当面 d2p 直接評価。

---

## 推奨と進め方

**①（速度実証）と②（機械検証完結）を並行**させ「正しく・効率的で・機械検証された可逆 Futamura
射影」の完結論文へ。ラボ方針 `methodology-agda-first` に従い、①-(2) の offline BTA 再設計
（＝後戻りしにくい大規模変更）は**先に Agda で設計図（健全性＋no-over-commit）を固めてから**
本番 `spec_av` 実装に落とす。

**着手済み（Agda 設計図・全 --safe 公理ゼロ、`check.sh` PASS=55）**：①-(2) の offline BTA を
3ブリックで機械検証。本番 `spec_av` 実装の設計図が揃った。
- **stage1 `RWhileOfflineBTA.agda`**（commit 6b8bf7e）：`static-stability`（静的 AV は ρ 非依存）
  → `over-commit-unsound`/`no-static-identity`（動的スロットは静的 AV で表現不能＝'S 凍結 unsound）、
  BT 駆動 offline 構成子 `mkAV`＋`mkAV-dyn-nonstatic`（`dyn` は決して静的 AV を返さない＝:1051 の
  正しい修正形）、誠実 offline `spec2` の `spec2-sound`＋`spec2-static`（congruence 構成的）。
- **stage2 `RWhileOfflineBTA2.agda`**（commit de66afc）：静的ソース Val→AV 一般化で自己適用段
  （記号的ソース）をモデル化。`spec2g`（ソース位置を束縛時刻 pass-through）の任意ソース健全性
  `spec2g-sound`、fp1＝静的インスタンス `spec2≡spec2g`。バグモデル `spec2bug`（:1051 の 'S 凍結）の
  `spec2bug-ok-on-static`（fp1 では不可視）／`spec2bug-wrong-on-symbolic`（fp2 で unsound）。
- **stage3 `RWhileOfflineBTA3.agda`**（commit 42c372a）：本論文①目標（comp2<|spec|）に対応。
  `spec2-noD-isS`/`gain`（完全静的部分式は単一静的リーフに畳込＝最大利得）、`dispatch-resolved`
  （静的ディスパッチ解決）、`dyn-survives`（動的部分は D ホールで残余化＝非凍結）。

**結論**：over-static fp2 バグ＝束縛時刻 congruence 違反。修正＝ソース位置を **AV pass-through
／`mkAV` 駆動**（BT が動的なら S でなく D）。この設計図に沿って本番 `spec_av.rwhile:1051`
（`FpPart <= cons 'C (cons (cons 'S Src) …)` の無条件 'S）を BT 駆動に置換するのが次の実装ステップ。

**次の一手（未着手）**：(a) この設計図を本番 `spec_av_bti.rwhile` の :1051 修正へ落とす
（selective+loop-BTA と統合、`measure_proj gate`/`comp2-loops` で fp1 緑＋comp2 非自明を確認）、
または (b) Agda 側をさらに進め、二段合成 `spec2g∘spec2g` で comp2 相当の非自明残余を構成し
サイズ減を定理化。
