# comp2 over-static — live-trace 根本原因（2026-07-10）

`(a)` の専任 live-trace 作業の成果。`[comp2]('S.swap) == B : false` の根本原因を、実機ベースライン
＋本番マクロの多層シンボリック解析＋生成コード実物の byte-level 検証＋実行時トレース計装（新規、
`RWHILE_TRACE_VAR` 環境変数）で特定した。結論：**局所パッチ不能。spec_av の online worklist
（agenda）機構が自己適用不能で、offline 再設計（RWhileH2Worklist の実機化）が必要。具体的な
バグ地点＝self-application の内側でシミュレートされる「RCode」相当の変数の束縛時刻追跡が
静的nilに誤解決し、comp2 の生成コードに自己参照が欠けた不健全な残余（`295<=cons(...)nil`）が
埋め込まれる（outer の実変数 RCode 自体は正しく単調蓄積することを実行時トレースで確認済み、
後述「追記」節）。**

## 症状（実測）

- `comp2 = [spec_av]((spec_av . ('S.ri_min)))` = 10691 nodes（loop は trivial 化済み 0.005×）。
- `[comp2]('S.swap)` = 39 nodes = `var2 <= cons 'swap var2`（＝ri_min の**echo** `In <= cons Op X` のみ）。
- 正しい `B_swap` = 103 nodes = **swap ボディ**（`cons A B <= X; X <= cons B A`）＋echo。
- ⇒ **comp2 は echo を残し、`if =? Op 'swap` の then 枝（swap ボディ）を落とした。**
- fp1 gate PASS、`dyncond` 健全（動的 cond＋自己クリア `D^=D` は spec_av が正しく特殊化）。
  ＝バグは**自己適用特有**。

## 多層トレース（なぜ then 枝が落ちるか）

`comp2` は「subject=ri_min を焼き込んだ spec_av、(bt.src) 入力待ち」。OUTER は spec_av のコードを、
`prog=('S.ri_min)`（ri_min 静的・(bt.src) 動的）で走らせる。ri_min の `if =? Op 'swap` を
SPEC-CMD-AV の 'cond ハンドラ（`spec_av_bti.rwhile:954-994`）が処理する：

1. `SPEC-EXP-AV(=? Op 'swap)` → `AV-EQ(Op-AV, 'swap-AV)`。
   Op-AV は ri_min の `cons Op X <= In` 由来で、In=(bt.src) は **OUTER から見て動的** → Op-AV 動的。
2. `AV-EQ(動的, 静的)` → else 枝 → `('D.('eq...))`。∴ **テスト AV は動的**、`TT='D`。
3. `AnnT ^= =? TT 'S` → `AnnT=FALSE` → **動的 cond 経路（:972-993）** に入る：
   `COLLECT-REFS`＋`SELECTIVE-DYNAMICIZE`＋`RCode <= cons ('cond . (LE.C.D.F)) RCode`。
4. ここで **C（then=swap ボディ）と D（else）は ri_min 由来＝OUTER から見て静的**。動的 cond の
   residualize は両枝を comp2 に埋め込むはずだが、**その先の再帰処理が本番の worklist（agenda `Cd`）
   機構に依存**する。comp2-runtime で `Op` が判明したとき、埋め込まれた 'cond を**再度 SPEC-CMD-AV
   で処理して静的 dispatch を解決し swap ボディを specialize** する必要がある（comp2 は
   「ri_min 用スペシャライザ」だから）。

## 根本原因

comp2 が正しく動くには、OUTER が spec_av の **`if AnnT then [静的 dispatch=agenda push] else
[動的 dispatch] fi` と、その後の worklist ループ（agenda `Cd` を回す `from … until =? Cd nil`）を
忠実に residualize** せねばならない。`AnnT` は OUTER から動的（comp2 の未来の入力に依存）ゆえ、
OUTER は**両枝と worklist ループごと residualize** する必要がある。

- 静的 dispatch 枝（:959-971）は `Cd <= cons C Cd`（taken 枝を**制御 agenda に push**）＋
  `D ^= D`（untaken 枝を自己クリア）。**agenda `Cd` は通常の値変数でなく INNER の制御フロー worklist**。
  動的 `AnnT` の下でこれを residualize＝「次に走らせるコードを条件付きで変える」を residualize する
  ことになり、**online worklist スペシャライザでは ill-defined**。
- ⇒ OUTER は spec_av の agenda スタックマシンを忠実に residualize できず、**then 枝（swap ボディ）の
  specialize が comp2 に載らない**。echo（`In <= cons Op X`）は agenda を経ない直接の書きなので残る。

これは長年の「online 値運搬 AV vs offline 二段 BT」不整合（[[research-direction-core-language]]、
FINDINGS §8、Agda 設計図 RWhileOfflineBTA1-7）の**制御フロー版**：値だけでなく **agenda（制御）も
自己適用下で記号化**せねばならない。BT-MKAV／selective／loop-BTA は**値**の束縛時刻を直したが、
**制御 agenda の residualize** は未対応 ＝「必要だが不十分」の正体。

## なぜ局所パッチ不能か

- `cons 'S <x>` 凍結面（AV-HD:59 / AV-TL:82 / AV-PAIRP:109,116 / AV-CONS:137 / AV-UNCONS:200-205 /
  AV-EQ:234 / SPEC-EXP-AV 'val:524 / MKAV:1111 …）を個別に BT 化しても、**agenda 機構自体**が
  自己適用不能なので then 枝は載らない。
- 誤出力の `('val.'swap)` は AV-LIFT of `('S.'swap)` で、これは ri_min の echo `cons Op X` の Op（静的
  正しい）由来＝**症状であってバグ源でない**（echo は正しい）。真のバグは**欠落**（swap ボディ）。

## 正しい修正（大規模）

Agda の `RWhileH2Worklist*`（worklist＋fuel＋AV 全代数＋partial-static store の四要素、機械検証済み）
の**実機化**：spec_av の agenda `Cd` を **offline 化**し、動的 `AnnT` 下でも agenda 上の（静的）
プログラム片を記号的に保って residualize、comp2-runtime で再 dispatch できるようにする。これは
online→offline の worklist 再設計＝複数専任セッション級。Agda 側は設計・健全性・利得・dispatch
保存まで証明済み（RWhileOfflineBTA1-7 + H2Worklist）、残るは実機の agenda 再設計の工学。

## 追記（2026-07-10 続）：生成コード実物の byte-level 検証＝具体的なバグ地点を確認

上記は構造解析（症状から機構を逆算）だったが、`/tmp/comp2_resid.rwhile`（`comp2-loops` が
ダンプする実際の生成プログラム、54行・10691ノード）を直接読み、**具体的な verified な証拠**を得た。

### 確認できたこと（直接観察）

comp2 の実行時コード（抜粋、変数番号は comp2 自身のもの）：

```
(* MKAV が動的化された分岐として生の埋め込みで残っている（正しい挙動） *)
if 26 then 28 ^= 'S; 25 <= cons 'C (cons (cons 'S 29) (cons 'D (cons 'var 27)))
else 28 ^= 'D; 29 ^= 29; 25 <= cons 'D (cons 'var 27) fi 26;
...
(* AV-LIFT も生で埋め込まれ、25 を "7" へ変換（正しい挙動） *)
...
(* AV-INIT の 256 スロット unroll、位置#2 に "11"（=25 の未クリア値）が直接埋め込まれている *)
1 <= cons ('S.nil) (cons ('S.nil) (cons 11 (...256個の('S.nil)...)));
...
(* ★ここが具体的なバグ地点 ★ *)
(6 ^= 0;
(295 <= cons (cons 'rep (cons (cons 'var 6) 7)) nil;      (* ← "nil" になっている！ *)
(from =? 3 nil do 0 ^= nil loop cons 23 295 <= 295;
 ...MAKE-SEQ...
until =? 295 nil;
...
5 <= cons ('var.(nil.(nil.nil))) (cons 3 (cons 'var 2));  (* ← 3 = AsBody = "materialize" だけ *)
write 5
```

**具体的な発見**：`ASSEMBLE-FP1` の最初のコマンドは本来
`RCode <= cons (cons 'rep (...)) RCode`（既存の `RCode` の**先頭に**追加）のはずだが、
生成された comp2 のコードでは

```
295 <= cons (cons 'rep (cons (cons 'var 6) 7)) nil
```

と、**末尾が変数 `RCode`（=295）ではなくリテラル `nil` に固定されている**。これは自己適用の
メタ・スペシャライザが「subject 側の `RCode` 変数は（この時点で）静的に `nil`」と**誤って**
束縛時刻解析した、という**直接証拠**である。

この結果、続く `MAKE-SEQ` は「`RCode`=nilから始めて1個だけ pop する」動作になり（実際 dump
は295から1項目だけpopしてループ終了）、**最終出力 `AsBody`（変数`3`）＝ "materialize J'" の
1コマンドのみ**になる。ri_min 本体（swap ディスパッチの `if/then/else` や X の書換え）を処理して
`RCode` に蓄積されていたはずの残余コマンド列は、**このRCode初期化の瞬間に silently discard**
される。誤出力 `('val.'swap)`（＝MKAVの計算結果、変数`7`/`11`/`25`経由）は**正しく計算されては
いるが、discard された `RCode` とは別の変数（"1"）に束縛されたまま最終組立てで一切参照されず、
孤立して捨てられている**（誤出力の主張「値埋め込みがバグ」はこの意味で不正確：値は正しく計算
されているが、組み立て段で使われていない）。

### 意義と限界

- **確定した事実**：`RCode` という subject 変数自体の束縛時刻追跡が、ASSEMBLE-FP1 到達時点で
  `nil`（静的・空）に collapse している。これは上記の「agenda/制御フローの online residualize
  不能」という抽象診断を、**具体的な1箇所のバグ地点として確認**するものである。
- **未解明（本ターンの範囲外）**：なぜこの collapse が起きるか（`SPEC-CMD-AV(FpBody)` の内側で
  ri_min 本体を処理する再帰的な自己適用の中で、`RCode` の束縛時刻がどの時点で・どの機構により
  `nil` に落ちるか）の完全解明には、OCaml 側のトレース計装（`EvalRwhile` に中間状態ダンプを追加）
  か、さらに深い手動シミュレーションが必要。自己参照が2重（spec_av が spec_av 自身の
  `SPEC-CMD-AV`/`ASSEMBLE-FP1` を、ri_min 本体特殊化のために評価する）になっており、変数名の
  多重の意味的役割（同じ "Vl"/"Cd"/"RCode" が「specializer 自身の変数」と「被特殊化対象=spec_av
  自身の変数」の両方を指す）を手作業で追うのは非常に誤りやすい。
- **この発見の位置づけ**：Stage-8（agenda 設計規則）の診断を**否定しない**——「動的テスト下で
  片枝のみ agenda に push するのは unsound」という規則は依然正しい。今回の発見は、その規則が
  効いてくる**具体的な症状の1つ**（`RCode` 自体の追跡崩壊）を実データで確認したもの。真の修正
  （agenda の offline 化）は変わらず大規模作業。

## 追記（2026-07-12）：実行時トレースで「outer RCode collapse」仮説を否定、真の局在を確定

上記「追記」節の byte-level 読解に基づき、**実際にどこで束縛時刻追跡が壊れるかを実行時トレース
で検証**した。`EvalRwhile.ml` に環境変数 `RWHILE_TRACE_VAR`（カンマ区切りの変数名）でオンオフ
できる非破壊トレースフックを追加（`CAss`/`CRep` の書込み時に `(step, 変数名, サイズ, 形状)` を
stderr へ出力、デフォルト OFF・既存動作に影響なし。commit 予定）。

`RWHILE_TRACE_VAR=RCode ./measure_proj comp2-loops examples/spec_av_bti.rwhile` で
**spec_av_bti 自身のネイティブ変数 `RCode`**（comp2 構築中、ただ1回だけ実行される、実際の
R-WHILE 変数）を追跡した結果：

```
[trace step=5866]   RCode := size=79    (comp2 構築開始直後)
[trace step=8823]   RCode := size=184
[trace step=1169525] RCode := size=252
...（単調増加、リセットなし）...
[trace step=2460853] RCode := size=6001
[trace step=2461138] RCode := size=0    (comp2 構築完了後の通常の終了時クリア = RCode^=RCode)
(dumped residual to /tmp/comp2_resid.rwhile)
```

**結論：outer（spec_av_bti 自身のネイティブ実行での）`RCode` は 79→6001 まで単調に増加し、
`ASSEMBLE-FP1` 到達時に collapse などしていない。前回の byte-level 読解による「outer RCode が
nil に collapse する」という解釈は誤り（訂正）。**

真の局在：comp2（生成されたプログラム自身）の中に現れる「`295<=cons(...)nil; ...MAKE-SEQ...`」
という断片（前節参照）は、**outer の `RCode`（6001 まで育つ実変数）とは別物**——これは
`SPEC-CMD-AV(FpBody)` が **spec_av_bti 自身のソース全体（FpBody = spec_av_bti の macro展開後の
全コマンド、その中には spec_av_bti 自身の `ASSEMBLE-FP1(FpI,FpJ,Out)` 呼び出しも含まれる）を
データとして辿る**過程で、**そのデータの中に現れる「RCode」という変数名（= subject レベルで
シミュレートされる、もう1つの「RCode」）** の束縛時刻を追跡した結果、embed された残余コードで
ある。この **subject レベルの「RCode」**（Vl の特定スロットに track される、outer の実変数
とは別のスロット）が、ある時点で静的 `nil` と誤追跡され、その結果 comp2 の生成コードに
`295<=cons(...)nil`（本来 `295<=cons(...)295` であるべき自己参照が `nil` に固定）という
不健全な残余が埋め込まれる。

**この2つの独立な検証（① byte-level のコード読解、② 実行時トレース）が収束して同じ結論を
指す**：outer の会計（RCode の実行時蓄積）は完全に正しく機能しており、バグは **self-application
の内側でシミュレートされる「RCode」相当の変数の束縛時刻追跡**にある。これは stage-8 の
agenda 診断（「動的テスト下で片枝のみ agenda に push するのは unsound」）と整合する、より
具体的な症状確認である。

**この先（未着手・要さらなる計装）**：subject レベルの「RCode」がどこで静的 nil と誤追跡される
かを特定するには、`UPDATE(Vl,idx,newAV)` 呼び出し（`AUX`/`LOOKUP`/`UPDATE` マクロの内部ループ）
を、対象スロット番号（subject の "RCode" に対応する Vl 内インデックス）でフィルタして追跡する
計装が必要——これは現状の「変数名一致」トレースでは捕捉できない（Vl は1つの大きな値であり、
その内部スロットへの book-keeping は "Vl" という1つの変数への書込みとして観測されるのみで、
どのスロット番号が更新されたかは別途デコードが必要）。次の一手として、UPDATE マクロの
展開箇所（AUX ループ）にスロット番号＋新AVをダンプする、より踏み込んだ計装が考えられる。

## 検証道具（このトレースで使用）

- `measure_proj gate <spec>`（fp1 高速）／`dyncond <spec>`（動的 cond 高速）／
  `comp2-loops <spec>`（comp2 正しさ＋CLoop、数分）。
- 本番該当箇所：`spec_av_bti.rwhile:954-994`（'cond ハンドラ、`:963` の `Cd <= cons C Cd` が
  agenda push）、`:509-536`（SPEC-EXP-AV/AV-EQ）、`:877` SPEC-STEP-AV（`cons (cons Tag Arg) Cd <= Cd`
  で agenda から命令 pop）、`:1090` SPEC-CMD-AV（worklist ループ本体）。
