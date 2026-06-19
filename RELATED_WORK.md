# 関連研究と新規性の位置づけ（可逆二村射影）

2026-06-19 時点の文献サーベイ。`FINDINGS_reversible_projections.md` の成果（`spec_av` による
第1〜第3可逆二村射影の実行可能デモ＋Agda 形式化）が、既存研究に対してどこに新規性を持つかを確定する。

## 0. 主張（claim）の候補

> **可逆言語で記述された自己適用可能な可逆部分評価器を構築し、その自己適用により
> 第2射影（可逆コンパイラ）と第3射影（可逆コンパイラ生成器 cogen）までを実行可能な形で
> 実現・検証した最初の研究。** 併せて (i) 出力残余の可逆化に伴うゴミの理論（非単射性・
> Landauer/Bennett）と dead-path 埋め込みによる実装、(ii) 対称可逆マッチ `case`（健全性条件付き）、
> (iii) コアの Agda 形式化を与える。

以下、この claim を支える「先行研究には無い差分」を整理する。

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

→ **可逆 PE の先行研究はいずれも fp1（＋反転射影）まで**。自己適用による fp2/fp3（可逆コンパイラ・
  可逆 cogen）の実行可能デモは**確認できない**（複数クエリで一貫）。ここが本研究の中核的差分。

## 3. 可逆言語基盤・可逆メタ言語 — 基盤であって射影ではない

- **Yokoyama & Glück, "A reversible programming language and its invertible self-interpreter"
  （PEPM 2007）**：Janus と履歴なしの可逆自己解釈器。**本研究が立つ基盤**（自己解釈器の存在）だが、
  部分評価・射影そのものではない。
- **Glück, Kaarsgaard, Yokoyama, "From reversible programming languages to reversible
  metalanguages"（TCS 920, 2022）**、**Glück & Yokoyama, "Reversible computing from a programming
  language perspective"（TCS 953, 2023）**：可逆メタプログラミングの一般論。射影の自己適用デモは別。

→ 自己解釈器・可逆メタ言語は既知。これに**自己適用可能な可逆 PE を載せて fp2/fp3 を回す**のが差分。

## 4. 横山先生自身の近年業績（2020–）との切り分け

dblp（2020–）に Futamura/cogen/部分評価の論文は無い（RC2024 可逆Zip、TCS2022/2023 メタ言語、
string-matching 等）。よって **本 fp3 可逆結果は未公表**。直接の前駆は**大久保修論
（`2024_okubo/thesis/chap4.tex`「可逆二村射影」, eq:rev_proj2 等）**であり、論文化に際しては
この内部研究を明示的に位置づけ・クレジットする必要がある（理論は修論、本研究は **R-WHILE 上の
実行可能・自己適用デモ＋Agda 形式化＋ゴミ理論** という実装・検証側の貢献）。

## 5. 差別化ピース（fp3 以外で独自性を足す点）

- **可逆化のゴミ（reversibilization cost）**：`spec_av` は非可逆（`X^=X`）。可逆版 `spec_av_rev` は
  非単射ゆえ入力相当のゴミを保持せざるを得ない（Landauer/Bennett）。dead-path 埋め込み＋N-sizing で
  −57% を実測。古典 PE 研究にこの「特殊化器そのものの可逆化コスト」の議論は無い。
- **対称可逆マッチ `case`**：入出力パターンの互いに素性 ⇔ 反転可能、という健全性条件付きの脱糖。
  RFun/Janus のパターンマッチと対比可能な小さな言語設計の貢献。
- **Agda 形式化**：`proofs/agda/RWhileRevProj2*`（postulate 0）。実行デモに機械検査の裏付け。

## 6. 公表前に詰めるべき確認事項（claim を堅くする）

1. **「first」主張の最終確認**：PEPM 2024 フローチャート PE の本文を入手し、自己適用/fp2/fp3 を
   扱っていないことを確認（ACM は 403、著者版/RC 系を当たる）。可逆 cogen を扱う未索引文献が
   無いか、RC（Reversible Computation）会議録を直近まで確認。
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
