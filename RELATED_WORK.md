# 関連研究と新規性の位置づけ（可逆二村射影）

2026-06-19 時点の文献サーベイ。`FINDINGS_reversible_projections.md` の成果（`spec_av` による
第1〜第3可逆二村射影の実行可能デモ＋Agda 形式化）が、既存研究に対してどこに新規性を持つかを確定する。

## 0. 主張（claim）の候補

> **可逆 Futamura 射影の理論・正当性は親論文 IEICE 2025（Okubo–Yokoyama, §0.5）が確立済み。
> 本研究の貢献は、その論文が「未実現／別途の工学的課題」と明記した第2・第3可逆射影の
> 自己適用を、実機で実行・検証（byte 一致）した最初の実現である。** 鍵は、発散原因だった
> (a) 深い入れ子パターンの読みの一般化（`PAT-READ-ITER`）と (b) 束縛時刻認識の部分入力
> （`MKAV`）。併せて (i) 可逆化ゴミの最小化の実測（−57%）と dead-path 埋め込み実装、
> (ii) 対称可逆マッチ `case`（健全性条件付き脱糖）、(iii) Core/射影の Agda 形式化を与える。

> ⚠️ **重要（2026-06-19 修正）**：初版は外部先行研究のみで「可逆 fp2/fp3 初」と書いたが、
> 親論文 IEICE 2025 が可逆射影の定義・正当性・R-WHILE 具体化（fp1 は実機達成）を既に与えている。
> 正しい差分は「**理論は親論文、本研究は親論文が残した fp2/fp3 自己適用の実機実現**」（§0.5 参照）。

以下、この claim を支える先行研究との差分を整理する。

## 0.5. 直接の親論文 — IEICE 2025 草稿（Okubo–Yokoyama、**未発表**）

`~/dev/overleaf/2025_Reversible_Projection_IEICE_D/paper123.tex`（研究速報 OkYo26 の拡張、**現在執筆中／未発表**）。
※未発表のため「外部の公表済み先行研究」ではなく**同時進行のコンパニオン草稿**。本リポジトリの実機実現は
この草稿の貢献の一部、または対になる成果として一体で主張しうる（独立公表時も親草稿と整合させる）。
- 与えている：可逆射影 fp1/2/3 の**定義と正当性証明**（生成物がソースの可逆シミュレーションを与える）、
  「実装言語が可逆なら通常の fp1/2/3 はソース自明時のみ成立」という不成立定理、R-WHILE による具体化、
  ゴミ解析。形式化は Isabelle/HOL・Rocq・Lean・**Agda**（本リポジトリ `proofs/agda/RWhileRevProj*`）。
- **R-WHILE 具体化で論文自身が明記する到達点と限界**（§可逆言語 R-WHILE による具体化）：
  - `rint` は実機動作（swap, 65 ノード）。
  - `rspec` は**存在証明＋テンプレート**（Jones のいう自明スペシャライザの可逆版；最適化は今後）。
  - **fp1 は最小インタプリタ `ri_min`(op∈{swap,id}) で実機 end-to-end 達成**、残余 103 < `ri_min` 163
    ノード＝特殊化が実際に効いている。
  - しかし「完全自己インタプリタは**深い入れ子パターンで発散**」「**第2・第3可逆射影の自己適用は
    未実現**」「完全実機実現は別途の課題」と明記。
- **本リポジトリが埋める差分**：この「未実現／別途の課題」を解消し、`spec_av` で
  `comp2 = [spec_av]((spec_av.ri_min))`（fp2）・`comp3 = [spec_av]((spec_av.spec_av))`（fp3）を
  **byte 一致で実機検証**（`FINDINGS §1`、`test_fp2_second_projection`/`test_fp3_cogen`）。
  発散の解消は `PAT-READ-ITER`（深さ一般の読み）と `MKAV`（束縛時刻認識の部分入力）による。
  → 本研究は IEICE 2025 の**実機実現コンパニオン**であり、新規性は「理論初」ではなく
    「**親論文が未解決とした fp2/fp3 自己適用の実行可能化＋それを可能にした工学的補題**」。

## 1. 古典（非可逆）二村射影と cogen — 確立済み、本研究の前提

- **Futamura 1971 / Ershov / Jones-Gomard-Sestoft**：3射影の枠組み。
- **Mix（Gomard-Jones）, Similix, C-mix**：自己適用可能 PE と第2/第3射影による cogen。
- **Glück, "Is there a fourth Futamura projection?"（PEPM 2009）**、**"Bootstrapping Compiler
  Generators from Partial Evaluators"（2012）**：cogen の力学・自己適用に依らない生成。
- いずれも**非可逆（古典）設定**。可逆計算とは独立。

→ 第2/第3射影・cogen の概念自体は古典では既知。本研究の差分は「**可逆領域での実現**」。

## 2. 可逆部分評価（最も近い先行研究）— fp1＋反転射影どまり

- **Mogensen, "Partial evaluation of the reversible language Janus"（PEPM 2011）**
  - Janus（手続き呼出を除く全体）の部分評価器。Janus→可逆フローチャート→polyvariant 特殊化→
    構造化へ逆変換。**第1射影（解釈オーバヘッド除去＝コンパイル）**を示す。
  - **自己適用は扱わない**（fp2/fp3 なし）。PE 自体が可逆言語で書かれた自己適用可能器という
    主張ではない。最も近いが射影は1段。
- **"Partial Evaluation of Reversible Flowchart Programs"（PEPM 2024）**
  - 可逆フローチャート言語の PE を体系的・形式的に展開。**反転と PE の合成**の最初の実験
    （対称暗号、Bennett RTM 解釈器）。RTM 解釈器で**第1射影と反転射影が textually equivalent**な
    プログラムを生成しうることを示す。射影は fp1＋inversion 水準。
- **Glück & Normann, "Inversion by Partial Evaluation: A Reversible Interpreter Experiment"
  （arXiv:2412.03122, 2024, DIKU）**
  - RTM 解釈器で**第1射影と反転射影**が機能的のみならず字面的にも一致しうることを実証。
    abstract で明示的に "the first Futamura and inversion projections"。**fp2/fp3 なし**。

→ **外部の可逆 PE 先行研究はいずれも fp1（＋反転射影）まで**で、自己適用 fp2/fp3 の実行可能デモは
  無い。理論面での fp2/fp3 は親論文 IEICE 2025（§0.5）が与えており、**本研究の差分はその自己適用の
  実機実現**（外部研究に対しても親論文に対しても、ここが新規）。
- 補足（Mogensen 比）：Mogensen は「可逆プログラム(Janus)を**非可逆 PE で**特殊化」に近く、残余の
  可逆性保証が論点。本研究/親論文は「**可逆言語で書かれた PE**が**可逆な残余**を生む」点で枠組みが異なる。

## 3. 可逆言語基盤・可逆メタ言語 — 基盤であって射影ではない

- **Yokoyama & Glück, "A reversible programming language and its invertible self-interpreter"
  （PEPM 2007）**：Janus と履歴なしの可逆自己解釈器。**本研究が立つ基盤**（自己解釈器の存在）だが、
  部分評価・射影そのものではない。
- **Glück, Kaarsgaard, Yokoyama, "From reversible programming languages to reversible
  metalanguages"（TCS 920, 2022）**、**Glück & Yokoyama, "Reversible computing from a programming
  language perspective"（TCS 953, 2023）**：可逆メタプログラミングの一般論。射影の自己適用デモは別。

→ 自己解釈器・可逆メタ言語は既知。これに**自己適用可能な可逆 PE を載せて fp2/fp3 を回す**のが差分。

## 4. 横山先生自身の近年業績（2020–）との切り分け

直接の前駆は **IEICE 2025（Okubo–Yokoyama）= 親論文（§0.5）** と、その元の**大久保修論
（`2024_okubo`「可逆二村射影」）／研究速報 OkYo26**（fp1 不成立＋第1可逆射影）。親論文 paper123.tex は
**未発表（執筆中）**。論文化での分担：**理論・正当性・具体化の枠組み＝親論文／
本研究＝親論文が "未実現・別途の課題" と明記した fp2・fp3 自己適用の実機実現と、それを可能にした
工学的補題（`PAT-READ-ITER` 深さ一般読み、`MKAV` 束縛時刻認識入力）、ゴミ最小化の実測**。
本リポジトリは親論文の Agda 形式化（`proofs/agda/RWhileRevProj*`）の置き場でもある。

## 5. 差別化ピース（fp3 以外で独自性を足す点）

- **可逆化のゴミ（reversibilization cost）**：`spec_av` は非可逆（`X^=X`）。可逆版 `spec_av_rev` は
  非単射ゆえ入力相当のゴミを保持せざるを得ない（Landauer/Bennett）。dead-path 埋め込み＋N-sizing で
  −57% を実測。古典 PE 研究にこの「特殊化器そのものの可逆化コスト」の議論は無い。
- **対称可逆マッチ `case`**：入出力パターンの互いに素性 ⇔ 反転可能、という健全性条件付きの脱糖。
  RFun/Janus のパターンマッチと対比可能な小さな言語設計の貢献。
- **Agda 形式化**：`proofs/agda/RWhileRevProj2*`（postulate 0）。実行デモに機械検査の裏付け。

## 6. 公表前に詰めるべき確認事項（claim を堅くする）

1. **主張の枠組みを「理論初」ではなく「親論文の未実現課題の実機実現」に統一**（最重要）。
   IEICE 2025 が理論・具体化（fp1 実機）を持つので、本研究を独立に「可逆 fp2/fp3 初」と書くと
   親論文と衝突する。コンパニオン/拡張として位置づけ、親論文 §具体化末尾の「未実現」記述を
   引用して差分を明示する。なお外部（PEPM 2024 フローチャート PE 等）が fp2/fp3 自己適用を
   扱っていないことは確認済み（補強材料）。
2. **「可逆」の定義の明示**：本研究の「可逆 PE」＝(a) 特殊化器自体が可逆プログラム、かつ
   (b) 残余も可逆、かつ (c) 自己適用可能。Mogensen は「可逆プログラムを非可逆 PE で特殊化」に近く、
   この3点で差分が立つことを論文で明記する。
3. **大久保修論との関係**：理論的帰結（fp2 は fp1 の代数的持ち上げ）は修論、本研究は実行・検証・
   実装規模（spec 2.1MB の p2d 等）という整理。

## 出典

- Mogensen, *Partial evaluation of the reversible language Janus*, PEPM 2011 — https://dl.acm.org/doi/10.1145/1929501.1929506
- *Partial Evaluation of Reversible Flowchart Programs*, PEPM 2024 — https://dl.acm.org/doi/10.1145/3635800.3636967
- Glück & Normann, *Inversion by Partial Evaluation: A Reversible Interpreter Experiment*, 2024 — https://arxiv.org/abs/2412.03122
- Yokoyama & Glück, *A reversible programming language and its invertible self-interpreter*, PEPM 2007 — https://dl.acm.org/doi/10.1145/1244381.1244404
- Glück, *Is there a fourth Futamura projection?*, PEPM 2009 — https://dl.acm.org/doi/10.1145/1480945.1480954
- *Bootstrapping Compiler Generators from Partial Evaluators*, 2012 — https://link.springer.com/chapter/10.1007/978-3-642-29709-0_13
- Glück, Kaarsgaard, Yokoyama, *From reversible programming languages to reversible metalanguages*, TCS 920, 2022
- Glück & Yokoyama, *Reversible computing from a programming language perspective*, TCS 953, 2023
- dblp: Tetsuo Yokoyama — https://dblp.org/pid/96/6619.html
- dblp: Torben Æ. Mogensen — https://dblp.org/pid/19/4483.html
