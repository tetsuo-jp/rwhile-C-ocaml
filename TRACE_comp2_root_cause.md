# comp2 over-static — live-trace 根本原因（2026-07-10）

`(a)` の専任 live-trace 作業の成果。`[comp2]('S.swap) == B : false` の根本原因を、実機ベースライン
＋本番マクロの多層シンボリック解析で特定した。結論：**局所パッチ不能。spec_av の online
worklist（agenda）機構が自己適用不能で、offline 再設計（RWhileH2Worklist の実機化）が必要。**

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

## 検証道具（このトレースで使用）

- `measure_proj gate <spec>`（fp1 高速）／`dyncond <spec>`（動的 cond 高速）／
  `comp2-loops <spec>`（comp2 正しさ＋CLoop、数分）。
- 本番該当箇所：`spec_av_bti.rwhile:954-994`（'cond ハンドラ、`:963` の `Cd <= cons C Cd` が
  agenda push）、`:509-536`（SPEC-EXP-AV/AV-EQ）、`:877` SPEC-STEP-AV（`cons (cons Tag Arg) Cd <= Cd`
  で agenda から命令 pop）、`:1090` SPEC-CMD-AV（worklist ループ本体）。
