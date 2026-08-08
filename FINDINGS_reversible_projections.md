# 可逆二村射影 — 知見まとめ (spec_av)

2026-06-18 時点。AV ベースの可逆部分評価器 `spec_av.rwhile` で第1〜第3二村射影を達成した過程で
得られた知見の統合記録（論文用）。旧 `FUTAMURA.md` は spec.rwhile 配列版・2026-06-14 時点で古い。

---

## 1. 達成したこと（fp1/fp2/fp3 すべて green）

`spec_av` の契約：入力 `In = (Prog . (BT . Src))`、`Prog` を静的入力 `Src` で特殊化（`BT='S`=Src 静的）。
基本方程式：`[spec_av]((p . ('S . s))) = comp,  [comp](d) = [p]((s . d))`。

- **fp1**：`[spec_av]((ri_min . ('S.op)))` = 残余 `comp`、`[comp](d)=[ri_min]((op.d))`。
  検証：`[[spec_av]((ri_min.('S.'swap)))](('a.'b)) = ('swap.('b.'a))`。`B` := この残余(436B)。
- **fp2（コンパイラ）**：`comp2 = [spec_av]((spec_av . ('S.ri_min)))`、`[comp2](('S.op)) == B`。
- **fp3（cogen）**：`comp3 = [spec_av]((spec_av . ('S.spec_av)))`、`[comp3](('S.ri_min)) == comp2`、
  ゆえに `[[comp3]('S.ri_min)]('S.'swap) == B`。

回帰テスト：`second-projection` 群（`test_fp2_second_projection`/`test_fp3_cogen`、`Slow、~28s）。

## 2. 鍵となった機構

- **MKAV（束縛時刻認識の部分入力）**：L1051 の無条件 `'S` タグ（束縛時刻の静的コミット）が fp2 の真因
  だった。`MKAV(BT,Src,Ic)` で `BT='S→('C.(('S.Src).('D.('var.Ic))))`、`BT='D→('D.('var.Ic))`。
  自己適用下では BT が動的化し条件が残余化される（必要だが不十分だった）。
- **PAT-READ-ITER（深さ一般の読みパターン残余化）＝fp2 を通した決め手**。`PAT-READ-AV` は深さ1で、
  ネスト cons を `PAT-READ-LEAF-AV2` の葉 else (`('S.(tl P))`) で**静的リテラル化**していた（マクロは再帰
  不可なので反復ワークリストで深さ一般化、AV-LIFT の begin/end マーカ流儀）。`ASSEMBLE-FP1` がネスト出力
  パターンを持つため fp2 で露呈した。
- **ストアサイズ N＝fp3 の決め手**：comp3 は spec_av(223 変数)を特殊化するのに AV-INIT の N(=`FpN`)=50 固定
  → AUX が index~223 まで歩いて 50 スロット店を溢れ `cons U Vl<=Vl`(Vl=nil) で落ちる（症状 `cons 10 1 vs nil`）。
  **真因は残余化バグではなくストアサイズ不足**。`FpN 50→256`・swap-via-temp の `TmpT 100→250`(特殊化対象の
  変数 index より上)で解決。動的算定ツール `specsize`（下記）。

## 3. 検証基準の落とし穴（重要）

- **`run_via_ri`（ri.rwhile 経由実行）は残余の判定に使えない**。ri.rwhile 自身にバグがあるため。
  - **bug1（修正済）**：ri.rwhile の `'cond` が入口テスト値と出口表明値を**ビット一致**で比較していた
    （`Arg ^= V`）。R-WHILE は**真偽一致**のみ要求。involutive な `CANON` マクロで真偽正規化して修正。
  - **bug2（本質的）**：可逆自己クリア `X ^= X` は**非可逆**（v→nil、逆も nil→nil）。ri.rwhile は
    `X^=X` を逆解釈できない。spec_av の残余は自己クリアを含むため run_via_ri で落ちる。
- **正しい判定＝直接評価**：`data2program`（`Program2DataRwhile`）＋ツール `d2p` で残余を AST に復号して
  `EvalRwhile.evalProgram` する。`comp == B`（byte 一致）で射影成立を判定。

## 4. 可逆性の理論（spec_av を可逆にすると何が起きるか）

- **spec_av は非可逆**：`X ^= X`（self-clear, X∈e 違反）で中間情報を不可逆消去している。前方実行専用なら
  クリーンに `(prog,src) → residual` を出せるが、これは**非可逆だからこそ**可能。
- **非単射ゆえ入力は消せない**：`spec : (prog,src) → residual` は非単射（residual から prog/src を復元
  できない＝逆特殊化は不可能）。非単射関数の可逆実現は入力を区別する情報を必ず保持する（Landauer/Bennett）。
  ⇒ **可逆版は必ず入力（or 同等のゴミ）を抱える**。「可逆かつ入力を捨てた clean 出力」は原理的に不可能。
- **整合**：可逆自己解釈器 `ri.rwhile` は出力を `(P . result)` にしてプログラムを保持しているからこそ可逆。

## 5. dead-path ゴミ埋め込み（可逆版プロトタイプ `spec_av_rev.rwhile`）

アイデア（横山先生）：**捨てる情報を残余の「実行されない枝」に封入**し、出力をペアでなく単一プログラムに保つ。
- 実装：`CLEAR(X)` マクロ本体を `X^=X` → `GARB <= cons X GARB`（ゴミスタックへ push）に変更。main の
  `EMBED-GARB` が GARB を残余の **dead 定数真分岐 else**（`if (nil.nil) then body else 0^=GARB fi (nil.nil)`）
  に埋め込む。`CLEAR` をマクロ化してあったため 1 マクロ差し替え + embed で済んだ。
- 検証（`test_rev_spec_dead_garbage`, `reversible-spec` 群）：
  1. `[spec_av_rev]((ri_min.('S.'swap)))` が **store クリーンで実行**（不可逆消去なし＝可逆実行）；
  2. `[comp](('a.'b))=('swap.('b.'a))`（dead 枝無視、direct eval も ri.rwhile も）；
  3. **決定的：`[INV-spec_av_rev](comp) == 入力`**（自分の出力から入力を全復元＝真の全単射）。
- 位置づけ：Bennett のゴミを別出力にせず **dead code に再配置**したもの。情報量は減らない（非単射）。

## 6. ゴミ最小化

- 計測（fp1 ri_min）：comp = 1739 nodes（B=103）。dead ゴミ 1517 nodes のうち **1 値が 1055 nodes
  ＝末尾 `CLEAR(Vl)`（AV 店全体, N=256）**。
- **lever1（支配的）：N-sizing**＝`specsize spec_av_rev.rwhile <subject>` で `FpN` を被特殊化プログラムの
  変数数に。ri_min(FpN=13)で 1055 店が潰れ comp ~755 nodes。
- **lever2（easy 部分・実施）：静的 delocalization**＝CLEAR(X) を、X が**生存変数のコピー**のとき
  `X ^= <src>`（再計算で打ち消し）に。CBoth/CBothS/CVT/NewV に適用、round-trip 維持。小さい(-12)。
- **lever2 hard 部分（未・研究規模）**：boolean flag（`f ^= =? X c`）は**分岐内で operand 消費**のため
  打ち消せず（operand 保存/並べ替え要）。runtime skip-if-nil は**両枝 X=nil 収束で出口表明不能**＝不可逆。
  真の消去は AV 代数(AV-HD/TL/UNCONS/EQ)の uncompute 規律可逆書き換え＋Vl の store-reversal。
- **合算（deloc + N-sizing）：1739→755 nodes（-57%）、`[comp]` 正答維持**。

- **ゴミ下界の実機テーブル（`./measure_proj garbage`, #4, 2026-06-22）**：証明済み下界
  `|ゴミ|≥|fiber|`（Agda `RWhileGarbageBound.garbage-injective-on-fiber`）を有限領域上で実機確認。
  深さ2の木38個を領域とし、非単射源 S を fiber に分類。

  | source | #fibers | maxfib | LB(bits) | S 単射 | 入力保存 g=x | lossy g=nil |
  |---|---:|---:|---:|---|---|---|
  | hd（cdr 破棄） | 6 | 7 | 3 | false | inj(OK) | NONINJ |
  | tl（car 破棄） | 6 | 7 | 3 | false | inj(OK) | NONINJ |
  | atomize（cons 潰し） | 3 | 36 | 6 | false | inj(OK) | NONINJ |
  | const-nil（最大非単射） | 1 | 38 | 6 | false | inj(OK) | NONINJ |

  - **下界**：最大 fiber に対し可逆シミュレーションは `⌈log₂ maxfib⌉` ビット以上のゴミを要する（LB 列）。
  - **達成可能性（`Achievable`）**：入力保存 g=x は全源で resid=(S x, x) が単射＝普遍的な可逆化（下界に一致）。
  - **必要性（`Witness`）**：lossy g=nil は S が単射のときのみ可逆＝maxfib>1（非単射）では必ず非単射に崩れる
    ＝ゴミは**必要**。`const-nil` は領域全体が1 fiber＝入力全体の保持が強制される最大非単射の証人。
  - 非可逆な源は R-WHILE プログラムとして直接書けない（`all_cleared` 違反）ため、S は「可逆化に
    ゴミを払うべき数学的関数」をモデル化したもの。理論（Agda）⇔実機を接続。

## 7. 成果物マップ

| ファイル | 役割 | タグ |
|---|---|---|
| `examples/spec_av.rwhile` | 正本（forward, fp1/2/3 green） | `spec_av-fp123-working` |
| `examples/spec_av_clean.rwhile` | 可読化（forward, spec_av と byte 等価, ゲート付き） | — |
| `examples/spec_av_rev.rwhile` | 可逆版（dead-path ゴミ埋め込み） | `spec_av_rev-prototype` |

- ツール：`src/d2p.ml`（`make d2p`：残余の復号/直接評価）、`src/specsize.ml`（`make specsize`：N を
  subject の変数数から動的算定）。
- テスト群：`second-projection`(fp2/fp3)、`reversible-spec`(可逆版 round-trip)、`refactor-gate`
  (spec_av_clean ≡ spec_av)。
- 関連 Agda（`proofs/agda/`）：`RWhileRevProj2BT`(束縛時刻の真因)、`RWhileRevProj2Self`(目標形)。

## 9. 最適化スペシャライザに向けて（案1 Phase 1：意味保存の残余簡約器）

2026-06-20。「本物の fp2＝生成コンパイラ comp2 が解釈を上回る（comp2 < |spec_av|）」を目指す研究の初手。

- **生成物の可逆性（実機裏付け）**：`measure_proj` で fp1 残余 B の round-trip を確認＝
  `[B](('a.'b))=('swap.('b.'a))`、`[INV-B](それ)=('a.'b)`、**round-trips: true**。
  生成された残余は**可逆プログラム**で、その構文的逆（`InvRwhile.invProgram`）が undo する（論文の
  「生成プログラムは可逆」主張の実行可能な裏付け）。
- **実行コスト（Jones 最適性の次元、#13）**：`EvalRwhile` に加算的ステップカウンタ（`eval_steps`/`reset_steps`/
  `get_steps`、evalCom 1回=1ステップ）。`measure_proj` で実測：`[B](('a.'b))=5 steps` 対
  `[ri_min]((swap.('a.'b)))=8 steps`（残余 **0.62×**）。⇒ fp1 残余は**サイズ（0.63×）だけでなく実行ステップでも
  高速**（静的ディスパッチが特殊化時に解決済）。サイズ偏重でなく速度でも特殊化が効いている実証。
  - **Jones 最適性テーブル（`./measure_proj jones`, 2026-06-22）**：複数の (インタプリタ, プログラム) 対で
    残余 vs 解釈の実行ステップ比と、残余中の CLoop 数（`loops`）を実測。`loops=0`＝解釈の制御（ループ）が
    特殊化時に完全展開され、残余が**直線（コンパイル済み）コード**であることを示す。

    | interp | program | \|resid\| | loops | resid | interp | ratio |
    |---|---|---:|---:|---:|---:|---:|
    | ri_min | swap | 103 | 0 | 5 | 8 | **0.62×** |
    | ri_min | id | 63 | 0 | 5 | 5 | 1.00× |
    | ri_seq | [swap] | 153 | 0 | 13 | 18 | 0.72× |
    | ri_seq | [swap;swap] | 1243 | 0 | 23 | 29 | 0.79× |
    | ri_seq | [swap;id;swap] | 1281 | 0 | 29 | 37 | 0.78× |
    | ri_seq | [swap*4] | 3423 | 0 | 43 | 51 | 0.84× |
    | ri_seq | [id*6] | 303 | 0 | 43 | 55 | 0.78× |
    | ri_perm | [ab] | 329 | 0 | 17 | 22 | 0.77× |
    | ri_perm | [bc] | 317 | 0 | 19 | 24 | 0.79× |
    | ri_perm | [ab;bc] | 543 | 0 | 31 | 39 | 0.79× |
    | ri_perm | [ab;bc;ab]=rev | 689 | 0 | 41 | 54 | 0.76× |

  - **これは Jones の基準ではない（2026-08-09 の訂正と続報、`./measure_proj jones-self`）**：上表は
    「残余 対 インタプリタ」＝特殊化の**利得**であって、Jones 最適性（自己インタプリタ sint に対し
    `[spec](sint,p)` が p 同等以上）ではない。ri_min/ri_seq/ri_perm の対象言語は R-WHILE ではないので
    「p を直接走らせる」が定義できなかった。**`ri_fp3.rwhile`（R-WHILE の自己インタプリタ）の fp1 残余が
    正しく走るようになった（2026-08-08）ので、いま初めて測れる。**
    可逆射影は**プログラム保存**インタプリタを要求する（残余は元プログラムも出力する義務がある）ため、
    公平な下敷きは p ではなく **p⁺＝同じ義務を果たす p の最小の拡張**（`Simp.program_preserving`：
    p の本体＋自分の符号を定数で置く 1 命令＋出力と対にする 1 命令）で、基準は **`残余 ≤ p⁺`**。
    測定（7 被験、詳細表は `RWHILE_S.md`「判明したこと 3」）：
    **work（比較で調べた値ノード）では 7 例すべて `残余 ≤ p⁺`＝可逆版 Jones 最適性が成立**、
    **steps（命令ノード）では成立しない**（`id` の 0.6× を除き 1.4〜5.0×）。
    解釈オーバヘッド自体は自己解釈の 1/10〜1/30 まで落ちている。**コピー伝播が効かせている**ので、
    主張は (spec_av, `Simp.copyprop_program`) の対についてのもの。回帰はテスト群 `jones-self`（5 件）。

    解釈オーバヘッド（静的ディスパッチ＋op 列ループ）が残余では除去され、**全例で残余 ≤ 解釈ステップ**
    （`id` 単体は no-op で最適化余地ゼロ＝honest な 1.00×）。**インタプリタの loops（ri_seq=2, ri_perm=2）は
    残余では全て 0**＝op 列ループが完全に展開され直線コードに「コンパイル」された証拠。出力一致（正当性）も
    各行で検査済（MISMATCH なし）。

  - **キラー例：可逆パーミュテーション・バイトコード（`examples/ri_perm.rwhile`, #2）**：swap/id を超える
    非自明な可逆対象言語＝三つ組 $[a,b,c]$ 上の転置 op `{'ab,'bc,'id}`（$S_3$ を生成）の列を解釈する
    可逆インタプリタ。固定プログラムへの第1射影は**op 列を1本の直線可逆置換へ「コンパイル」**する
    （上表 ri_perm 行：loops=0・解釈より高速・出力一致）。例 `[ab;bc;ab]` は三つ組の反転に等しい。
    残余は可逆プログラムであり、その構文的逆（`InvRwhile.invProgram`＝逆順の op 列）が undo する。
    ＝「可逆バイトコードを直線可逆コードへコンパイルする」古典 PE の動機例を可逆領域で実機実証。
    （注：spec_av は一部の相殺プログラム（例 `[bc;bc]`＝恒等）で残余の可逆性衝突を起こす既知の限界がある＝
    `analysis_store_bti.md`/HANDOFF の online-AV 由来。`ri_perm` 自体は直接実行では全プログラムで可逆・正当。）
- **ベースライン（`src/measure_proj.ml`, `make measure_proj`）**：`|spec_av|=817,701`、`|ri_min|=163`、
  fp1 残余 swap=103（**0.63×ri_min＝fp1 は既に最適化**）/id=63、**comp2=`[spec_av]((spec_av.ri_min))`=812,515
  （0.994×|spec_av|）＝自明自己適用**（生成コンパイラが spec_av をほぼ凍結、Futamura 利得なし）。
- **レバー1：意味保存・可逆性保存の残余簡約器 `src/Simp.ml`**。2変換のみ：(1) 閉じた（変数無し）式を
  実評価器 `evalExp []` で定数畳み込み（構成上正しい）、(2) **dead 可逆分岐除去**＝
  `if E then C else D fi F` で E・F が定数同真偽なら生き枝へ（`真→C`/`偽→D`）。捨てる枝は前方も逆方向も
  実行されず、定数表明は常に充足＝意味・可逆性保存。
- **結果（実測）**：comp2 を **812,515→597,961 nodes（73.6%＝−26.4%）**、ratio **0.994×→0.731×|spec_av|**。
  正当性：`[comp2_simp](('S.swap)) == B`（fp1 残余と byte 一致, `measure_proj full` で確認）。
  ＝**comp2 は自己適用で生じた定数 dead 分岐を実際に抱えており**、簡約で除去できる。
- **限界と次手**：comp2 の本体（spec_av の解釈機構）は op 入力に依存し**動的**＝定数畳み込みでは消えない。
  comp2 < 0.5× 級の真の Futamura 利得には**束縛時刻改善（BTI）**が要る（spec_av を、静的プログラム構造への
  ディスパッチが自己適用で静的展開されるよう注釈/二段階化）。Phase 2＝BTI、Phase 3＝オンライン展開。

- **Phase 2b-1 診断（`measure_proj full` の breakdown）**＝「なぜ縮まないか」を定量化：
  comp2 の構成子ヒストグラム `CSeq=1533 CAss=758 CRep=1120 CCond=219 CLoop=125`。
  **(i) Simp 前後でヒストグラムが完全に同一**（CCond=219 不変）なのに −26%＝**削減は全て式の定数畳み込み**で、
  **dead 可逆分岐は0個除去**（comp2 のディスパッチは op 依存で動的、両側定数の cond が無い）。
  **(ii) bulk は 125 個の CLoop（動的ストア index 歩行＝AUX/LOOKUP/UPDATE）**に集中（ループ本体ノードが支配的。
  proxy はネスト重複で過大計上だが定性的に明白）。Simp はループに触れない。
  ⇒ **post-hoc 簡約は天井（~0.73×|spec_av|）。comp2 ≪ |spec_av| には Phase 2b（ストア index の静的化＝
  変数 index が静的なとき `from..until` 歩行を特殊化時に静的アンロール）が必須**。これが本研究の本丸。

- **Phase 2b-2 設計＋決定的診断（`analysis_store_bti.md`）**：`measure_proj looptest` で
  `[spec_av]((ri_seq.('S.('swap.('id.('swap.nil))))))` の残余が **CLoop=0 CCond=0**（静的命令リスト上の
  ループ完全展開・静的分岐解決済）と実測。⇒ **spec_av のループ展開機構は正しく動作**＝comp2 の 125 CLoop は
  ループ機構不備ではなく**純粋に index J（内側プログラムポインタ Cd 由来）が動的**であることが原因と確定。
  **修正は「index/Cd を静的に保つ」(partially-static 環境 or BT 維持) に一点集中**でよい（ループ特殊化は不変）。
  真因の本質は online 値運搬 AV vs offline BT 分離（HANDOFF/§2）。実装は spec_av_bti.rwhile で fp1 ゲート保護下。

- **Phase 2c：選択肢2（本番改造を回避し、最適化スペシャライザの本質を Agda で機械検証）** 2026-06-21。
  本番 spec_av の online→offline-AV 再設計（高リスク・大規模・「必要だが不十分」既証）を回避し、HANDOFF の
  選択肢2（小コア/関係モデルを正として意味保存翻訳で橋渡し）を進めた。実 spec_av の2大オーバヘッド＝
  **op-list 走査（fold）とタグ分岐（case）**の最適化除去を、`--safe` で機械検証（全41モジュール緑）：
  - `RWhileH2HierRec.agda`：構造再帰子 `cata` 入りの大ステップ関係 `_·_⇓_`。再帰プログラム例 `mirrorP`
    （関係レベル可逆性 `mirrorP-reversible`）、走る残余を生成する再帰スペシャライザ `reify`（定数族 H1
    `reify-spec-correct`）と入力依存残余 `prependSpec`（`prepend-spec-correct`）＝quoted-construction-under-recursion。
  - `RWhileH2HierRecSelf.agda`：`RWhileRevProj2Self` の最適化性（**解釈系除去・runtime 入力使用・over-static なし**）
    を関係モデルへ持ち上げ。op-list を直接 `ap`-チェイン残余へ畳み込む `compileOps`（合成 `g∘f=ap(quo g)f`）が
    任意入力で `foldOps` 一致（`compileOps-correct`、op-list 上の真の再帰）。
  - `RWhileH2HierDispatch.agda`：実 spec_av の `=? Tag 'op` 機構。実行時分岐インタプリタ `int`（`PDisp` ノード）を
    静的 op に特殊化すると残余から `PDisp` が消える（`dispatch-eliminated`/`spec-correct`、`int-has-dispatch` で非自明）。
  - `RWhileOptRev.agda`：**最適化∧可逆性**。最適化（解釈系除去）op-list 残余はそれ自身可逆で、逆は invList
    （逆 op を逆順）で構文的に与えられる（`foldOps-invert`、Bool トグル対合で witness）。
  - すべて `RWhileMain.agda`（キャップストーン）に再輸出。**含意**：comp2 を本番で縮める BTA は研究規模だが、
    「最適化スペシャライザ＝解釈系を消した可逆残余が存在し正しい」という #1 の本質は、実 spec_av に構造的に近い
    再帰可能関係モデルで機械検証済み。本番化（offline-AV）は将来研究、橋渡し定理が次の足場。

## 8. 未解決・今後

- ゴミ最小化の hard 集合（AV 代数の uncompute 規律可逆書換、Vl の store-reversal）。
- `N` の真の動的化（spec_av 内部で Prog の変数数から算定。現状は固定 or `specsize` で外部生成）。
- ri.rwhile bug2（自己クリア非可逆）の扱い＝spec_av_rev のように残余から self-clear を排すれば run_via_ri 可。
- 先行研究：古典 PE の cogen は Mix/Similix/C-mix で達成済（いずれも非可逆）。**可逆領域**の先行 PE
  （Mogensen Janus PE 2011、Glück–Normann 2024、可逆フローチャート PE 2024）は **fp1＋反転射影どまりで
  自己適用 fp2/fp3 は無い**＝本研究（自己適用可能な可逆 PE による fp2/fp3・可逆 cogen）が中核的新規性。
  詳細な位置づけ・出典・公表前の確認事項は **`RELATED_WORK.md`** を参照。

## 8. 【達成】spec_av_rev の自己適用 fp2/fp3 が GREEN（2026-07-06, commit `2ce7cc6`）

上記「中核的新規性・未達」だった**可逆 PE の自己適用**を達成。`reversible-spec` 群に
`test_fp2_rev_second_projection`／`test_fp3_rev_cogen` を追加し、全 [OK]：
- **fp2-rev**：`comp_rev = [spec_av_rev]((spec_av_rev.('S.ri_min)))`＝**可逆コンパイラ**、
  `[comp_rev](('S.op)) == B_rev`（fp1-rev 残余）かつ compiled op が正答。
- **fp3-rev**：`comp3_rev = [spec_av_rev]((spec_av_rev.('S.spec_av_rev)))`＝**可逆 cogen**、
  `[[comp3_rev]('S.ri_min)](('S.op)) == B_rev`。
- fp1 可逆性 round-trip も維持（[OK]）。

**原因と修正**：lever2 delocalization の `NewV ^= VRE`（uncompute-by-recompute, `NewV==VRE` 前提）が
自己適用で不可逆化（静的変数更新の VAVx 分岐が NewV を変化させ、末尾 clear 時に `NewV=('S.nil) ≠
VRE=(nil.(nil.nil))`）。→ `CLEAR(NewV)`（無条件可逆・GARB push、spec_av_clean と一致）に revert。
他3 deloc（CBoth/CBothS/CVT）は set→(if 非改変)→clear で同一 source ゆえ自己適用でも可逆＝保持。

**ビルド注意**：test-suite は `eval $(opam env) && make test-suite` が必要（binary は別 opam スイッチ製に
なりがち＝ミスマッチ）。`.rwhile` はデータで実行時読込なので `make` 不要。実行は
`./test-suite test reversible-spec`（各 fp2-rev/fp3-rev は自己適用で ~11分/より長い）。

## 10. `'error <= '41` — 動的制御の壁（2026-08-09、Jones 最適性のループ拡張から）

**目的だったこと**：`./measure_proj jones-self`（可逆版 Jones 最適性、基準は
`残余 ≤ p⁺`）の被験 7 本がすべて直線プログラムだったので、**ループ込みに広げる**。
引き継ぎには「ループ被験は fp1-via-ri_fp3 が未対応で測れない」とあった。

**結論を先に**：その記述は**誤り**だった。ループは通る。通らないのは
**実行時データで分岐する制御**であり、**ループが無くても通らない**。

### 10.1 できたこと（表に載った）

`examples/loop_static2.rwhile` / `loop_static3.rwhile` を追加。3 変数
（ri_fp3 の V0/V1/V2 制約）で、**静的制御のループ**（カウンタ V1 対リテラル）＋
**動的な本体**（`V0 <= cons V0 nil`）。spec_av は展開しきり、残余に `CLoop` は残らない。

| 被験 | ループ p/残余 | \|残余\| | steps p⁺ | steps 残余 | Jr(steps) | work p⁺ | work 残余 | Jr(work) |
|---|:---:|---:|---:|---:|---:|---:|---:|---:|
| `loop_static2` | 1/0 | 121 | 10 | **1** | 0.1x | 104 | **95** | 0.91x |
| `loop_static3` | 1/0 | 131 | 12 | **1** | 0.1x | 118 | **101** | 0.86x |
| （8 反復・恒久化せず） | 1/0 | 181 | 22 | **1** | 0.0x | 218 | **131** | 0.60x |

- **ループ被験は両指標で `残余 ≤ p⁺` が成立する唯一の被験群**。直線プログラムでは
  steps が 1.4〜5.0x で不成立（`RWHILE_S.md` 判明したこと 3）。
  ⇒ **steps の不成立は段取りの固定費**であって、特殊化器が総じて劣るのではない。
- 反復を 2→3→8 と増やしても **steps 残余は 1 のまま**、残余の大きさは
  **反復あたり 10 ノード**の線形。展開の per-iteration オーバヘッドは定数。
- 残余は**測定に使った入力専用ではない**（3 種類の入力で p⁺ と一致し、構文的逆が
  往復する）。テスト `jones-self` 群に 2 件追加して固定。
- 任意の被験を試すには `JONES_EXTRA=<名前,...> ./measure_proj jones-self`。

### 10.2 壁の正体（どの関数のどの行で、何が破れるか）

**症状**：`Failure "Pattern matching failed: '41 and 'error are not equal (in inv_evalPat)"`。
これは spec_av が `'error <= '41` を実行し、対応するクリアで整合しないことによる。

**発生箇所は 1 か所だけ**：`examples/spec_av.rwhile` の `SPEC-STEP-AV`、
タグ `'lcheck` のハンドラの「出口テストが静的でない」枝（`'41` はこのファイルに
1 回しか現れない）。すなわち破れる不変条件は

> `'lcheck` に到達したループは、その出口テスト F が**静的に評価できる**

である。`'lcheck` は `'loop` ハンドラが**静的展開**を始めるときに積む継続なので、
この不変条件は「展開を始めたら最後まで制御は静的なまま」を要求している。

**なぜ破れるか（fp1-via-ri_fp3、被験 = reverse）**：

1. ri_fp3 の主ループ `from (=? Cd' nil) loop STEP-FP3(Cd,Cd') until (=? Cd nil)` は
   ループ入口で entry・exit とも静的（`Cd'` は nil、`Cd` は静的なコード）なので
   **展開が始まる**。
2. 被験のループの出口テスト `=? Y nil` は動的なので、ri_fp3 の `'l3E` ハンドラの
   `if Flag then … else …`（Flag = 出口テストの真理値）が**動的な条件分岐**になる。
3. spec_av は動的 cond を残余化するとき `DYNAMICIZE-ALL(Vl, RCode)` を呼び、
   **ストア全体を動的化**する。ri_fp3 の**コードスタック `Cd` はストアの一員**。
4. 以後、1 の主ループの出口 `=? Cd nil` は**動的**。次の `'lcheck` で `'41`。

**ループは本質ではない**という証拠：`examples/dyncond3.rwhile`（ループ無し、
動的入力で分岐するだけの 2 変数プログラム）も **同じ '41 で落ちる**。
逆に、静的制御のループ（10.1）は通る。⇒ 分けているのは**動的制御**である。

**ri_fp3 の限界ではないという証拠**：ri_fp3 は reverse を**正しく自己解釈する**
（`[ri_fp3](p2d reverse, d) = (p2d reverse . [reverse](d))`、テストで固定）。

**ri_fp3 固有でもない**という証拠：インタプリタを挟まない**直接の fp1**
（`[spec_av]((reverse.('S.'c)))`）も同じ '41 で落ちる。reverse の入口では
`=? Y nil` は Y が部分静的な cons なので**静的に false**＝展開が始まり、
静的な先頭を消費した次の反復で動的になるため。

**対照（spec_av は動的分岐一般が苦手なのではない）**：直接の被験に含まれる動的
cond は正しく残余化される（`./measure_proj dyncond`、`fp_dyncond_bug` の残余
105 ノードが `'one`/`'two` を正しく出し分ける）。経路が無いのは
**展開を始めたあとに現れる動的テスト**だけである。

### 10.3 効かない修正（実測で棄却）

- **ストア動的化の精度を上げる（selective dynamicize＝`spec_av_bti`）**。
  `FP3PROBE_SPEC=spec_av_bti ./fp3probe ri_fp3 dyncond3 reverse` は**同じ '41**。
  過剰近似の問題ではない：ri_fp3 の `'l3E` の動的分岐は**実際に `Cd` を書く**
  （else 枝が `Cd <= cons DD (cons (cons 'l4E C') Cd)`）ので、どんなに正確に
  解析しても `Cd` は動的化される。`analysis_store_bti.md` が comp2 について
  出した結論（「over-approx は '41 の主因ではなかった」）と一致する。
- **展開回数に上限を入れて超過したら動的化**（`plan_fp1_stage_c.md` の案 1）。
  停止性は得るが、上限に達した時点の状態から残余ループを出す方法が無いので
  '41 が別のエラーに変わるだけ。

### 10.4 直すのに何が要るか（規模の見積り）

Agda 側には既に設計図がある（`RWhileLoopBTA.agda`／`RWhileLoopBTARev.agda`、
`AGDA_CORRESPONDENCE.md`）。要点は 2 つ：

- **`unrollable` は entry と exit の両方が静的**であること（現在の実装は entry しか
  見ていない）。動的 exit は**常に残余化を強制**（`exit-dynamic-forces-residual`）。
- 残余化するとき **entry テストを定数に畳んではならない**（`constEntry-no-iter`）。
  可逆ループは戻り辺で entry が false であることを要求するので、定数 true を置くと
  **反復できない＝非可逆**になる。制御スロットを動的化してから entry テストを
  **再特殊化**し、実テストとして残す必要がある。

**それでも reverse は通らない。** 上の規則は `'loop` ハンドラ（＝ループに**入る前**）
の判定であり、reverse も ri_fp3 の主ループも**入口では両方静的**だからである。
入口で判定できないのは、制御が動的になるかどうかが**本体を 1 回回してみないと
分からない**ため（束縛時刻の不動点）。したがって必要なのは次のどちらか：

1. **オフライン BTA**（`RWhileOfflineBTA1`–`9` に設計図がある）。ループごとに
   束縛時刻の不動点を先に求め、動的と判定したループは最初から残余化する。
   規模：spec_av の前段に別プログラムが 1 本要る（現在の spec_av は完全オンライン）。
   自己適用（fp2/fp3）への影響が未知で、そこが本研究の中核なので**最大のリスク**。
2. **投機的展開＋巻き戻し**。展開を始め、動的 exit に当たったら
   **ループ入口まで逆実行して**残余化経路へ入り直す。**spec_av は R-WHILE で
   書かれた可逆プログラムなので、`INV-SPEC-STEP-AV` は自動で存在し、
   ワークリストの履歴 `Cd'` も保持されている**——巻き戻しに必要な材料は既にある。
   これは古典 PE の「一般化のために投機的な仕事を捨てる」に相当するが、
   可逆言語では**捨てる＝逆に走らせる**なので、この設定でこそ自然に書ける
   （論文の主張になりうる論点）。
   規模：`'loop` に入口マーカーを積む＋内側の巻き戻しループ＋`RCode` の整合
   （逆実行が emit 済みの残余も自動で取り消す）。spec_av 側 50〜100 行。
   自己適用を壊していないかの確認に comp2（`./measure_proj full`、数分）が要る。

**やらなかった理由**：どちらも 67KB の可逆プログラムへの構造変更で、fp2/fp3 の
回帰リスクが高く、1 セッションで安全に入れられる規模ではない。上の測定
（10.1）と壁の局在（10.2）を先に固定した。

### 10.5 固定したテスト

- `jones-self` 群（7 件）：`loop_static2`/`loop_static3` を表に追加し、
  「p にループがある・残余にはループが無い・両指標で p⁺ 以下」と
  「残余は測定に使っていない入力でも p⁺ と一致し、逆が往復する」を固定。
- `jones-self-open` 群（3 件、新設）：**期待される失敗**として
  (a) ri_fp3 は reverse を正しく自己解釈する、
  (b) fp1-via-ri_fp3 の reverse と **ループ無しの dyncond3** が同じ '41 で落ちる、
  (c) 直接 fp1 の reverse も同じ '41 で落ちる／直接の動的 cond は残余化できる、
  を固定した。**どれかが raise しなくなったら、特殊化器が動的制御の経路を得た
  ということなので、表を測り直すこと。**

**測り方**：`cd src && make measure_proj && ./measure_proj jones-self`、
`JONES_EXTRA=<名前,...>` で被験を足せる。`FP3PROBE_SPEC=<spec 名>` で
`./fp3probe` の特殊化器を差し替えられる。
