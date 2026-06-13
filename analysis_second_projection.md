# 第2可逆二村射影の実装：現状と詰まりの所在

作成日: 2026-06-14
対象: `examples/spec.rwhile`, `examples/ri.rwhile`, `examples/ri_fp3.rwhile`
関連: 修論 `2024_okubo/thesis/chap4.tex`（可逆二村射影）, `2024_okubo/report/futamura_TY.tex`

このメモは、修論 chap4 の `\todo{■実際に構築できる？}`（第3射影節の末尾、可逆射影が
実際に R-WHILE 上で構築できるかという問い）に対する、実装側からの現状回答である。

---

## 0. 理論（紙）と実装（実行デモ）の切り分け

**理論としての第2射影は易しい。** `futamura_TY.tex:172` / `chap4.tex:157` (eq:rev_proj2) で

```
comp'' = ⟦rspec⟧^L̄ (rspec . rint)        実装語:  comp = [spec]((spec . ri))
```

が与えられ、導出は第1射影 (eq:rev_proj1) を一段持ち上げるだけの代数的帰結。
要旨でも「第1・第2・第3射影について同様の等式を満たすことを示した」と述べている。

**大変なのは実行可能なデモの方**であり、第2射影以前の段階で詰まっている。以下に所在を示す。

---

## 1. 詰まり①：第1射影が現状 red（本物の `ri.rwhile` 経由）

```
$ ./test-suite test first-projection
3 failures! in 1.978s. 3 tests run.        # fp1_id / fp1_swap / fp1_reverse
```

エラー（`_build/_tests/.../first-projection.000.output`）:

```
error in update: var=Vl cur=(... ((nil.nil).(('ass.(('var.nil).('val.nil))).nil)) ...) new=(...)
[failure] error in update
  Raised at EvalRwhile.rupdate (EvalRwhile.ml:73)
```

- 場所: `EvalRwhile.ml:73`（`rupdate` = 可逆 XOR 代入）。`vx<>VNil && vy<>VNil && vx<>vy`
  のとき失敗する。
- 意味: spec の残余化経路で、部分ストア `Vl` のあるスロットに doNothing 命令
  `('ass.(('var.nil).('val.nil)))` が**残ったまま**になっており、次の XOR 代入が
  「nil でも同値でもない既存値」に当たって整合性が壊れる。
- これは `analysis_spec_reverse_fix.md` の問題1〜4（write変数初期化・クリーンアップ・
  PAT-WRITE-LEAF・ループ再入）と同根。

**対照（動いているもの）:**
- `spec-partial`（`[[spec]((swap.'a))]('b) = ('b.'a)`）→ green
- `rint`（自己解釈 `[rint]((rint.(id.'a)))`）→ green

つまり **spec を小さなプログラムに当てる第1射影は動くが、本物の `ri.rwhile`
（100変数の配列ストアを持つ自己解釈系）に当てると壊れる。**

---

## 2. 詰まり②：自己適用の壁（第2射影の本質的困難）

第2射影 `[spec]((spec . ri))` は **spec を spec で特殊化**する。
ところが spec は100要素の配列ストア `Vl` を**動的インデックス**の
`LOOKUP(Vl,J,X)` / `UPDATE(Vl,J,X)`（`spec.rwhile:24-39`）で操作する。

- インデックス `J` が動的だと、束縛時解析は「どの変数スロットか」を決定できない。
- 結果、ストア全体が dynamic に潰れ、特殊化が起きず**自明な（恒等に近い）残余**になる。

この壁は既に認識されており、その回避策が `ri_fp3.rwhile`（冒頭コメント参照）である：

> Like ri.rwhile but uses named variables V0, V1, V2 instead of a Vl array.
> This allows spec.rwhile to track each variable statically when the program
> code is known at specialization time.

すなわち**配列を名前付き変数に置き換えてインデックスを静的化**する方針。
しかし `ri_fp3` は ri 側の回避にすぎない。**spec 自身が配列ストアを使う**ため、
spec を入力プログラムとして与えると同じ壁に当たる。

→ **結論: 現在の spec は self-applicable ではない。これが第2射影の核心障害。**
（古典的にも mix の自己適用化は BTA フレンドリな書き換えを要した — Jones/Gomard/Sestoft。）

---

## 3. 詰まり③：`'partial` モードが ri 専用ハック

`spec.rwhile:682-762` の partial 処理は ri の構文形に決め打ちされている：

- `Cmd` の seq を左から剥がして最初の `'rep` を探す（`spec.rwhile:700-708`）
- read変数 Y に `Y ^= s`、`Z <= I'` という残余命令を手で生成（`:725-732`）

これは「read変数が `(prog . data)` を受け、最初のループが reverse 様」という
ri 固有の形に合わせたもの。spec を入力に与えても正しく発火しない。

根本は、**一般の partially-static 構造値**（read 変数が `(static . dynamic)` の
ように部分的に静的な木を持てる表現）が存在しないこと。第2射影では spec の read 変数
`(P . S)` のうち P=ri を静的・S を動的にしたいが、現状は「全部静的（normal モード）」
か「ri 専用 partial ハック」の二択しかない。

---

## 4. 規模の実測

```
$ ./ri -p2d examples/spec.rwhile | wc -c   →  2117431   (≈2.1 MB)
$ ./ri -p2d examples/ri.rwhile   | wc -c   →   498985   (≈0.5 MB)
```

`[spec]((spec.ri))` の素朴実行は、上記②③の論理的障害に加え、この規模でも頓挫する。

---

## 4.5. Stage 0 着手記録（2026-06-14）— spec.rwhile を3点修正、ただし fp1 はまだ green でない

第1射影（`[spec]((ri . ('partial . src)))`）を green に戻す作業に着手し、spec.rwhile の
バグを3点修正した。結果、**spec はクラッシュせず完走する**ようになったが、生成される
残余が正しくないため fp1 はまだ通っていない。判明した本質的限界も併記する。

### 修正したバグ（いずれも regression なし: spec-partial / spec-macros は通過）

1. **最終 Vl クリーンアップのクラッシュ**（`spec.rwhile` 末尾）
   - 旧: `Vl ^= (固定 all-(nil.nil) リテラル)` で一括クリア。これは「全スロットが
     `(nil.nil)`」を前提とし、解釈対象（ri）が残した静的スロットがあると
     `error in update`（`EvalRwhile.rupdate`, `EvalRwhile.ml:73`）で落ちる。
   - 新: `Vl ^= Vl`（self-XOR）。rupdate は vx=vy を nil に写すので、内容に依らず
     Vl を nil へ畳める。

2. **動的テスト cond の shell 再構成漏れ**（`spec.rwhile` SPEC-STEP の 'cond 動的分岐）
   - 旧: `RCode <= cons (cons 'cond Arg) RCode` が CRep で `Arg` を消費し、shell(Cd')
     には marker `('condB.nil)` だけが残る → 末尾 `Cd' ^= Cmd` で Cd'≠Cmd となり失敗。
   - 新: `CDcopy ^= Arg` で複製を作り残余には複製を使用、`Arg` を温存（'ass / 'rep の
     動的分岐と同じ方式）。

3. **`'condB` → `'cond` の fixup 追加**（SPEC-STEP 末尾 `Cd' <= cons (cons Tag Arg) Cd'` の直前）
   - `fi =? Tag 'condB` アサーションのため動的分岐内では Tag='condB を保つ必要がある。
     そこで l2B/l4B と同様、push 直前の fixup で「Tag='condB かつ Arg≠nil（=動的）」の
     ときだけ `'condB`→`'cond` に変換。静的 cond（Arg=nil）は condCleanS が処理するため変換しない。

### 残る本質的限界（fp1 が green にならない理由）

- 修正後、`[spec]((ri . ('partial . id)))` は完走し約 **990KB** の残余を生成するが、
  これは ri の p2d（約 499KB）の約2倍で、**loop 104・cond 301・rep 1047** 個を含む
  ＝ **ri 全体がほぼ未特殊化のまま残余化**されている。さらにこの残余を ri で実行すると
  `cons V1 V2 <= nil`（`inv_evalPat.PCons`）で落ちる（残余が不正）。
- 原因は診断②そのもの: ri.rwhile は配列ストア `Vl` を**動的インデックス**で操作するため、
  spec は変数の静的追跡ができず、ほぼ全コマンドを dynamic 残余化する。だから残余は
  「ほぼ ri のコピー」になり、特殊化の効果が出ない。
- 注意: 残余中の `('val.'seqB)` 等は **ri.rwhile 自身が seq 処理に 'seqB/'seqE を使う**
  ための正当なデータであり、spec マーカーの漏れではない（当初の誤診を訂正）。
- したがって **fp1 の正しい対象は配列版 ri.rwhile ではなく、名前付き変数版
  `ri_fp3.rwhile`**（V0/V1/V2、まさに特殊化可能にするために作られた）。ただし現状の
  `'partial` モードは ri.rwhile の構文形に決め打ち（seq を剥がして最初の 'rep を探す）の
  ため、`ri_fp3.rwhile` に対しては seq-peel が nil に当たって失敗する（別バグ）。

### Stage 0 続き（2026-06-14）— ri_fp3 への切替を試行、より深い限界が判明

ユーザー判断で「fp1 の対象を ri_fp3.rwhile に切替＋'partial 一般化」を選択し、以下を実施。

1. **ri_fp3.rwhile の prelude を書き換え**（最初のコマンドを入力 rep にする）
   - 旧: `V1^=V1; V2^=V2; cons Prog Data <= V0;`（先頭2つが no-op ass）
   - 新: `cons V1 V2 <= V0; Prog^=V1; V1^=V1; Data^=V2; V2^=V2;`
   - 効果: 変数番号 V0/V1/V2=0/1/2 を保持しつつ先頭を rep 化。素の解釈系としての
     等価性は確認（`[ri_fp3]((id.'a)) = (id.'a)`）。これで現行 peel が ri_fp3 でも発火し
     **spec が完走**するようになった（以前は seq-peel が nil に当たって失敗）。

2. **判明した、より深い限界**
   - `[spec]((ri_fp3 . ('partial . id)))` は完走するが残余は約 **714KB**（ri.rwhile の
     990KB よりやや小さい程度）で、ri_fp3 本体がほぼ未特殊化のまま残余化されている。
     実行すると `error in update: var=V2`（プログラム断片が名前付きスロット V2 に代入される）
     で失敗。
   - peel は「プログラム保持変数 Y(=FCYi) に runtime で `Y^=s` を出しつつ static 追跡」する
     設計。ri.rwhile は出力 (prog.result) 再構成が同じ Y を読むので整合するが、ri_fp3 で
     Y(=V1) を Prog に移すと spec が静的実行して残余化せず runtime とずれる。`Y^=s`（cmd1）を
     外しても、今度は別のプログラム断片が V2 に乗る別エラーになり、いずれにせよ green に
     ならない（cmd1 削除は共有 peel ロジックを壊しうるため最終的に revert）。
   - **本質**: ri_fp3 にしても残余が ~ 解釈系全体のままなのは、spec のコアが ri_fp3 の
     名前付きディスパッチ（`if =? J nil then X^=V0 else …`）やループを**静的に解決できて
     いない**ため。fp1 を green にするには peel の小細工ではなく **spec コアの特殊化品質
     （静的ディスパッチ解決・ループ展開）の改善**が要る。これは複数セッション規模。

3. **この作業で保持した変更**
   - `examples/spec.rwhile`: §4.5 の3バグ修正のみ（クラッシュ除去・動的 cond 整合）。回帰なし。
   - `examples/ri_fp3.rwhile`: prelude 書き換え（先頭 rep 化、素の解釈系として等価）。
   - committed の first-projection テストは ri.rwhile のまま（ri_fp3 でも green に
     ならないため切替えていない）。fp1 系は依然 red。

### Stage 0 の結論（改訂）

「第1射影を直す」= **配列版 ri.rwhile を特殊化する**のは、診断②により本質的に筋が悪い
（残余＝ほぼ ri のコピー）。正しい Stage 0 は **fp1 の対象を `ri_fp3.rwhile` に切り替え、
`'partial` モードを ri_fp3 の構造（名前付き V0/V1/V2、入力 `(prog.data)`）に合わせて
一般化する**こと。spec.rwhile の3修正（上記）はその前提として有効で、保持してよい。

### 再現方法

```
cd src && make ri        # opam の extlib が必要: opam install extlib
./ri -p2d ../examples/ri.rwhile  > /tmp/ri.data
# spec((ri.('partial.id))) の素朴実行は TestSuite の first-projection 群で確認:
make test-suite && ./test-suite test first-projection
```

---

## 5. 段階プラン（実行デモを構築するなら）

| Stage | 内容 | 検証 |
|------|------|------|
| 0（必須前提） | 第1射影の `Vl` update バグ修正（doNothing 残留の解消） | `test first-projection` が green |
| 1 | spec を self-applicable に書き換え（動的インデックス配列ストアの排除） | spec を spec で特殊化しても dynamic 全潰しにならない |
| 2 | 一般 partially-static 構造値を導入し `'partial` の ri 専用ハックを置換 | fp1 が `ri_fp3` 経由でも通る |
| 3 | `comp=[spec]((spec.ri))` を実行、`[comp](src)=[spec]((ri.src))` を検証 | id/swap の最小例 |

Stage 1 の設計分岐：
- (A) spec を名前付き/固定本数変数で全面書き直す（`ri_fp3` と同方針、正攻法・大改修）
- (B) 配列ストアのままオフライン束縛時解析を足し、インデックス静的時に LOOKUP/UPDATE を
  静的解決（一般的だが重い）

---

## 6. chap4 `\todo{■実際に構築できる？}` への回答（暫定）

- **紙の上では構築済み**（eq:rev_proj2 の代数的帰結、要旨で主張済み）。
- **R-WHILE 上の実行デモは未構築**で、第2射影以前に第1射影が本物の ri 経由で red。
- 主障害は (i) 第1射影の Vl 整合性バグ、(ii) spec が動的インデックス配列ストアを
  使い self-applicable でないこと、(iii) partially-static 構造値の不在。
- 歴史的にも非可逆 mix の self-application 化は大仕事だったため、その結果（BTA・
  名前付き化）を可逆設定に移植するのが現実的な道筋。
