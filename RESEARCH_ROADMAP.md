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
  - **★2026-07-10 実機ベースライン再確認（(a) 着手）**：現行 `spec_av_bti.rwhile` は既に BT 対応
    MKAV（:1107、Agda `mkAV` に対応）＋selective＋loop-BTA を搭載。それでも実測は
    `[comp2]('S.swap) == B : false`（comp2=10691 nodes/0.005×、CLoop 4）。誤出力 39 nodes は
    `var2 <= cons 'swap var2`＝`('val.'swap)` の**値埋め込み**（AV-LIFT が over-static な出力スロットを
    lift）。一方 **fp1 gate PASS**（swap=103/id=63・意味・可逆性）かつ **`dyncond` 健全**
    （`[comp]('x)='one`/`[comp](nil)='two`）＝**バグは自己適用特有**（spec_av が自分の
    MKAV/ASSEMBLE/dispatch を特殊化するときだけ発症）。⇒ BT-MKAV は必要条件だが不十分。残る凍結は
    ASSEMBLE-FP1（:270）の `AV-LIFT(AsAV)`／MKAV then 枝 `('S.Src)` が OUTER 残余化される経路にあり、
    生の Src に束縛時刻情報が無いため一発編集は困難（fp1 は `('S.Src)` が必須）。**正しい修正＝
    Agda 設計図（RWhileOfflineBTA1-5）の offline 二段化を本番へ写す大規模作業**（複数専任セッション級）。
    検証道具は `measure_proj gate <spec>`（fp1 高速）／`dyncond <spec>`（動的cond 高速）／
    `comp2-loops <spec>`（comp2 正しさ＋CLoop、数分）。

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

- **★2026-08-09：最適性の一部を実測で閉じた（Jones 最適性、`./measure_proj jones-self`）。**
  Jones の基準は**自己インタプリタ** sint に対する `[spec](sint,p) ≤ p` であり、これまでの
  `measure_proj jones` の表（残余 対 インタプリタ）は特殊化の**利得**であって基準ではなかった。
  ri_min/ri_seq/ri_perm の対象言語は R-WHILE でないので基準を書くことすらできなかったが、
  **`ri_fp3.rwhile`（R-WHILE 自己インタプリタ）の fp1 残余が正しく走るようになった（2026-08-08）**
  ので測定できるようになった。
  可逆射影は**プログラム保存**インタプリタを要求する＝残余は元プログラムも出力する義務があるので、
  比較対象は p ではなく **p⁺＝同じ義務を果たす p の最小の拡張**（`Simp.program_preserving`）とし、
  基準を **`残余 ≤ p⁺`（可逆版 Jones 最適性）**と定めた（p⁺ が正しい下敷きであることは
  「3 者が同じ値を返す」「p⁺ の逆が往復する」で検査、仮定していない）。
  **結果：work 指標（比較で調べた値ノード）では 7 被験すべてで成立、steps 指標（命令ノード）では
  不成立**（`id` の 0.6× 以外は p⁺ の 1.4〜5.0×）。解釈のオーバヘッドは自己解釈の 1/10〜1/30 まで
  落ちており、コピー伝播（`./ri -copyprop`）が効かせている。表と読みは `RWHILE_S.md`
  「判明したこと 3」、回帰はテスト群 `jones-self`（5 件）。
- **★2026-08-09（同日、続き）：上の「残り (i)」は誤りだった。壁はループではなく動的制御。**
  ループ被験 `loop_static2/3` は fp1-via-ri_fp3 を通り、`ri_fp3` は `reverse` を正しく
  自己解釈する。決め手は**ループを含まない**動的分岐だけの `dyncond3.rwhile` が同じ
  `'error <= '41` で落ちること。破綻箇所は `examples/spec_av.rwhile` の `'lcheck` ハンドラ
  1 か所で、破れる不変条件は**「展開を始めたループは脱出条件が静的なままであり続ける」**。
  選択的動的化（`spec_av_bti`）では解けない（`'l3E` の else 枝が実際に `Cd` を書くため、
  解析精度の問題ではない）。詳細は `FINDINGS_reversible_projections.md` §10。
  **測定結果**：ループ被験は **steps・work の両指標で `残余 ≤ p⁺` が成立する唯一の例**
  （`loop_static2` 0.1×／0.91×、`loop_static3` 0.1×／0.86×）。反復を 2→3→8 と増やしても
  `st_res` は 1 のままで残余は +10 ノード/反復で伸びるので、**直線被験の steps 側の不成立
  （1.4〜5.0×）は固定の段取りコストであって一般的な劣位ではない**と言える。
  回帰はテスト群 `jones-self`（+2）と `jones-self-open`（3 件、壁を期待される失敗として pin）。
- **★2026-08-09（同日、続き）：p⁺ の定義側を Agda で機械検証した（`--safe`・postulate ゼロ）。**
  `RWhileJonesRev`／`RWhileProgPres`／`RWhileProgPresRev`／`RWhileProgPresMin`／
  `RWhileJonesRevCE` の 5 モジュール。到達点は
  (1) p⁺ の可逆性（`pp-rev`：逆も同じコスト `k+8` で往復）、
  (2) 意味論が仕様どおり（`pp-sem`）、
  (4) 古典版 ⇒ 可逆版は証明、逆は反例で不成立。
  **(3) の「p⁺ は義務を果たす最小のプログラム」は一般には偽で、反証を機械検証した**
  （`RWhileJonesRevCE.p⁺-not-minimal`）。義務 `PP q p` は外延的に関数を固定するが、
  コストは関数から決まらないため。代わりに「**p の拡張の中での**最小性」を証明した
  （下界 `+3`、p⁺ は `+8`、差は常に加法定数）。詳細は `AGDA_CORRESPONDENCE.md`。
  → **和文で「最小の義務」と書くと反証と衝突する。「義務を満たす最小の拡張」と書き分けること。**
  **残り**：(ii) 代数的性質（合成則・cogen の不動点性＝第4射影の退化）は未着手、
  (iii) steps 側の 1.4〜5.0× を縮める＝残余のムーブを減らす作業は①と同じ土俵、
  (iv) 動的制御の壁を越える手（オフライン BTA か、投機的展開＋巻き戻し）の選択。
  **後者が論文向き**：`spec_av` 自身が可逆 R-WHILE プログラムなので `INV-SPEC-STEP-AV` と
  履歴 `Cd'` が既にあり、「投機的な仕事を捨てる」が**逆向き実行そのもの**になる（古典 PE には
  タダでできない）。どちらを採るにせよ comp2（`./measure_proj full`）で fp2/fp3 の自己適用を
  ゲートすること。
  (v) `-work` 指標に対応するコストモデルが Agda に無い（`RWhileTime` の ℕ は `-steps` 側）。
  測定と証明を同じコストモデルに載せるのが次の費用対効果の最大点。

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

- **stage4 `RWhileOfflineBTA4.agda`**（commit 0667847）：実際の二段 comp2（fp2 コンパイラ）。
  三束縛時刻（s1=stage1 静的 / s2=stage2 ソース=stage1 では記号的 / d=実行時）を二穴残余
  `Code2`（kS=ソース穴, kD=実行時穴）＋stage1 `AV2` で表現。`spec1-sound`（comp は全体として
  正しいコンパイラ）、`compile`＋`compile-sound`＋**`fp2-eq`（COMPILE→RUN＝直接評価＝Futamura
  fp2 等式、target は s2 非依存）**、`spec1-keeps-source-symbolic`（正しい comp は s2 を記号的に
  保つ＝非自明）、`spec1bug-wrong-on-source`（stage1 で s2 凍結は unsound）、`gain`（stage1 静的部分は
  完全畳込）。

- **stage5 `RWhileOfflineBTA5.agda`**（commit acdcc23）：三段 cogen（fp3）。インタプリタ s1 も
  cogen 構築時は記号的＝三入力（s1/s2/d）を三穴残余 `Code3`（j1/j2/jd）＋stage0 `AV3` で表現
  （stage4 の `evalE2`/`Exp2` を再利用）。`gen-sound`（cogen は全体として正しい）、`generate`
  （j1=int 具体化）／`compile`（j2=s2）／**`fp3-eq`（GENERATE→COMPILE→run＝直接評価＝Futamura
  fp3 等式）**、`gen-keeps-int-symbolic`（正しい cogen は int を記号的に保つ＝真の生成器）、
  `genbug-wrong-on-int`（int 凍結は unsound）、`gain`（定数/構造部分は stage0 で畳込）。

**⇒ offline BTA 設計図が stage1-5 で完成**（fp1 バグ診断→正しい挙動/利得→fp2 二段等式→fp3
三段等式、全 --safe 公理ゼロ、`check.sh` PASS=57）。over-static fp2/fp3 バグ＝束縛時刻 congruence
違反であり、修正＝各段のソース/インタプリタ位置を凍結せず**穴として残余化（BT 駆動）**すること、を
機械検証で確立。

- **stage6 `RWhileOfflineBTA6.agda`**（commit 262949b）：実機症状↔修正パターンの接続。本番
  AV-LIFT（:149 `lift(S v)=cVal v`）＋MKAV then 枝（:1111 `C(S src)(D cVar)`）を忠実モデル化し、
  静的 car は `cVal src` に lift＝定数＝観測された `('val.'swap)`（`prodThen-car-lift/const`）、
  静的 AV は runtime 依存 source を追えない（`prodThen-car-unsound`）。修正パターン `fixThen`
  （BT 駆動 mkAV）は **BT='S で本番と byte 同一＝fp1 無退行**（`fix-agrees-on-fp1`）かつ BT='D で
  D ホール＝runtime 追従（`fixThen-car-tracks`）。CAVEAT：どのスロットが誤って静的かの特定は
  live trace 要（修正の『形と fp1 安全性』を証明）。
- **stage7 `RWhileOfflineBTA7.agda`**（commit 87a8304）：ディスパッチ保存で stage6 の CAVEAT を
  閉じた。opcode ディスパッチ（`if x2='swap then…else…`）を二段モデルに追加し、式言語に eEq/eIf、
  AV 特殊化器に avEq2/avIf2（本番 AV-EQ:224 と 'cond ハンドラ対応：静的テスト→分岐解決／動的
  テスト→残余化 kIf）を搭載・健全性証明。`spec1-sound` が dispatch 込みで成立＝正しいコンパイラ
  （source 記号的）は全 opcode で正しく **実際にディスパッチ**（`comp-swap`=(d.d) ≠ `comp-id`=d）。
  `spec1bug`（opcode 凍結）は `compbug-ignores-opcode`（常に else 枝＝opcode 無視）＋`compbug-wrong`
  （swap で誤り）＝**:1111 型 over-static がディスパッチを潰す**ことを証明（実機 `('val.'swap)`
  埋め込み＝ディスパッチ喪失の因果を裏付け）。
- **`RWhileMain` 再エクスポート**（commit 262949b/87a8304）：stage1-7 の主要定理を capstone へ公開
  （機械検証を『主張する貢献』へ昇格）。

**★2026-07-10 live-trace 根本原因を特定（`TRACE_comp2_root_cause.md`）**：多層シンボリック解析で
`[comp2]('S.swap)==B:false` の根本原因を確定。誤出力（39n）は ri_min の **echo（`In<=cons Op X`）
のみ**で、`if =? Op 'swap` の **then 枝（swap ボディ）が欠落**。原因＝OUTER が spec_av の
**online worklist（agenda `Cd`）機構を自己適用下で residualize できない**：'cond の動的 `AnnT` 下で
`Cd <= cons C Cd`（制御 agenda への push, :963）＋その後の worklist ループを忠実に residualize する
必要があるが、「次に走らせるコードを条件付きで変える」を online スペシャライザは表現できない。
⇒ **局所パッチ不能**（`cons 'S` 凍結面の個別 BT 化では agenda 機構が直らない）。誤出力の `('val.'swap)`
は echo の Op（静的正しい）由来＝症状であってバグ源でない（真のバグは**欠落**）。正しい修正＝Agda
`RWhileH2Worklist*`（四要素・機械検証済）の**実機化**＝spec_av の agenda を offline 化（複数専任
セッション級）。BT-MKAV/selective/loop-BTA は**値**の束縛時刻を直したが**制御 agenda** は未対応＝
「必要だが不十分」の正体。

- **stage8 `RWhileOfflineBTA8.agda`**（commit ecf094b）：live-trace 根本原因（agenda 機構）を受けた
  **agenda offline 化の設計規則**を証明。dispatch 付き最小コマンド言語（SPEC-CMD-AV の agenda 抽象）で、
  `seq-flatten-ok`（無条件 seq は agenda に flatten 可＝`Cd<=cons C Cd` が seq で正しい理由）、
  `specOff-sound`/`specOff-keeps-branches`（**動的条件分岐は両枝を specialize した残余ノードに残す**
  ＝agenda に片枝 push しない＝健全＋両枝保存＝修正）、`specBug-riM`/`specBug-wrong`（片枝のみ残すと
  riM が echo のみに潰れ unsound＝comp2 の 39n 症状）。⇒ **実機修正の設計規則が確定**：SPEC-CMD-AV の
  'cond で、動的テスト時は agenda push でなく両枝を sub-residual として specialize し `cond` 残余ノードに。

- **stage9 `RWhileOfflineBTA9.agda`**（commit d1fb206）：**可逆性/情報消失チェック**（ユーザー指摘）。
  stage1-8 は forward soundness のみ証明していたが、R-WHILE は可逆言語で論文の核＝可逆スペシャライザの
  意味は**単射**（情報消失なし）。(A) 残余の可逆性 `rexec-exec`（前進後に後進で store 復元）＋
  `swapV-invol`。(B) スペシャライザの単射性：`specOff-id`/`specOff-injective`（正しい offline spec は
  全枝保存＝制御構造の恒等＝単射＝情報保存）、`specBug-collapses`/`specBug-not-injective`（分岐落とし
  バグは異なる2ソースを同一残余に潰す＝非単射＝情報破壊）。⇒ **comp2 の then 枝欠落は soundness バグ
  でなく可逆性違反**（枝プログラムを破壊）。実機 fp1 も `gate` で `reversible=true` 確認済。

**次の一手（未着手）**：(a-cont) stage8 の設計規則＋stage9 の可逆性制約に沿って本番 SPEC-CMD-AV の
'cond 動的経路（:972-993）を「両枝を specialize して残余 cond に、**情報消失なし＝単射・可逆**」へ
改造（agenda に依存しない per-branch spec）→ `gate`（reversible 含む）/`dyncond`/`comp2-loops` で検証。
または論文 mechanization ドキュメントへ stage1-9＋root-cause を反映。
