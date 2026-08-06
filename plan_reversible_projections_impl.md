# 実装計画：可逆射影（第1〜第3）の実行デモと論文 §5/§6 の裏づけ

作成日: 2026-06-14
出所: 論文側セッション（`~/dev/overleaf/2025_Reversible_Projection_IEICE_D/`）で立案・ユーザ承認済みの計画を本リポジトリへ引き継ぐもの。
関連: 本リポジトリ `analysis_second_projection.md`（採用・本計画の診断基盤）, `analysis_spec_reverse_fix.md`（棄却）, `FUTAMURA.md`。

---

## Context（なぜやるか）

論文 `~/dev/overleaf/2025_Reversible_Projection_IEICE_D/paper123.tex` の §5（R-WHILE による具体化）は
現在 rspec の**存在証明**にとどまり、§6（ゴミの解析）は |src| に対する**オーダ見積り**のみ。
査読で唯一弱い「有効性」を、**実際に動く第1〜第3可逆射影＋ゴミの実測値**で裏づけたい。

本リポジトリの本日付診断 `analysis_second_projection.md` の結論を前提にする：
- 第1射影は配列版 `ri.rwhile` 経由で **red**。配列版を直しても残余は「ほぼ ri のコピー」で筋が悪い。
- 名前付き変数版 `ri_fp3.rwhile` に切替えても、**spec コアが静的ディスパッチ・ループを解決できず**残余が肥大。
- bounded patch では解けず、**spec コアの設計変更**が必要。
  （旧 `analysis_spec_reverse_fix.md` の配列版5点パッチはこの方針により**棄却**。追わない。）

**ユーザ決定**：到達目標は**第3射影まで完遂**。spec 改修方式は**一般 partially-static 値の導入**（推奨A）。

## ゴール

第1〜第3可逆射影をすべて R-WHILE 上で実行し、test-suite で green にし、各段のゴミを実測。
その結果で論文 §5/§6 を「存在」から「動く実装＋実測」に更新する。

```
1st: comp_src = [spec]((ri_fp3 . src))     ;  [comp_src](in)         = (src . [src](in))
2nd: comp     = [spec]((spec . ri_fp3))    ;  [comp](src)            = comp_src
3rd: cogen    = [spec]((spec . spec))      ;  [[cogen](ri_fp3)](src) = comp_src
```

## アーキテクチャ決定（採用A：一般 partially-static 値）

現状の `examples/spec.rwhile` はストア項を **('S.value) 全静的 / ('D.nil) 全動的の二択**でしか
タグ付けできず、かつ配列ストア `Vl` を**動的インデックス** `LOOKUP/UPDATE`（`spec.rwhile:24-40` の AUX 走査）
で操作するため：
- (i) read 変数 `(P.S)` を P=静的・S=動的に分けられず（ri 専用 peel ハック `spec.rwhile:682-762` で誤魔化している）、
- (ii) spec を入力に与えると束縛時に index が決まらずストア全潰し＝**自己適用不能**。

採用方針は2点セット：
1. **partially-static 構造値**：ストア項が `(static . dynamic)` のように**部分的に静的な木**を持てる表現にし、
   式評価（SPEC-EXP）・コマンド残余化をその上で再定義。これにより ri 専用 peel を撤去。
2. **BTA フレンドリ化**：spec 内の動的インデックス配列ストアを**名前付き/固定本数スロット**に置き換え、
   プログラムが静的に既知のとき変数スロットを静的追跡できるようにする（`ri_fp3` が `ri` に施したのと同方針を spec 自身に）。

この2点が第2射影（spec の自己適用）の本質的前提であり、第1射影 green（ri_fp3 経由）にも必要。

## 段階プラン（各段に「完了の定義＝テスト」）

### Stage A：ゴミ計測の足場（独立・先行着手可・低リスク）
- `src/AbsRwhile.ml` の `valT` に対し **`count_nodes : valT -> int`**（必要なら符号列長も）を追加。
  自然な置き場は `src/PrintRwhile.ml`（出力整形と同居）。
- `src/Main.ml` に **`-stats` フラグ**：結果に加えノード数/サイズを出力。
- `src/TestSuite.ml` にサイズ表明ヘルパ（`assert_size_at_most` 等）。
- 現在 green のデモ（`spec-partial`＝`[spec]((swap.'a))`、`rint` 自己解釈）のゴミを実測・記録。
- **完了の定義**：`-stats` で任意プログラムの出力サイズが出る／既存75テスト green 維持。
- 価値：spec コア改修の成否に関わらず、論文 §6 に載せる実数の一部がこの段で得られる。

### Stage B：spec コア改修（採用A）— 最難関・複数セッション
- partially-static 値表現を導入し、SPEC-EXP/コマンド残余化を再定義（`examples/spec.rwhile`）。
- 動的インデックス配列ストアを名前付き/固定スロットへ。ri 専用 'partial peel を撤去。
- **完了の定義**：spec を spec で特殊化しても全潰しにならない（残余が入力 spec の素朴コピーで
  なくなる＝サイズが有意に縮む or 構造的に特殊化が観測できる、を `-stats` で確認）。
- 回帰防止：`spec-partial` / `spec-macros` / `rint` 各テストを緑のまま維持。

### Stage C：第1射影 green（ri_fp3 経由）
- 新コアで `comp_src = [spec]((ri_fp3 . src))` が**適切に特殊化された**残余を出す。
- `src/TestSuite.ml` の `first-projection` 群の対象を **ri.rwhile → ri_fp3.rwhile** に切替
  （`check_first_projection` の `ri.rwhile` 参照、現 `TestSuite.ml:752-767` 付近）。
- **完了の定義**：`./test-suite test first-projection` が green（id/swap/reverse）。
  かつ残余サイズ << ri_fp3 の p2d サイズ（特殊化が効いている証拠を `-stats` で記録）。

### Stage D：第2射影
- `comp = [spec]((spec . ri_fp3))` を実行し、`[comp](src) = [spec]((ri_fp3 . src)) = comp_src` を検証。
- `examples/` に必要な `.p_val`（`(spec . ri_fp3)` 形）を追加、`TestSuite.ml` に `second-projection` 群を新設
  （`check_first_projection` のパターンを一段持ち上げる）。
- **完了の定義**：id/swap の最小例で `second-projection` green、ゴミ実測。

### Stage E：第3射影
- `cogen = [spec]((spec . spec))` を実行し、`[[cogen](ri_fp3)](src) = comp_src` を検証。
- `TestSuite.ml` に `third-projection` 群を新設。
- **完了の定義**：最小例で green。第1→第2→第3でゴミ（保持される符号列）が累積する様子を実測し表化。

### Stage F：論文更新（実装完了後・論文側セッションが担当）
`~/dev/overleaf/2025_Reversible_Projection_IEICE_D/paper123.tex`：
- **§5（具体化）**：rspec の「存在」記述に、R-WHILE 上で第1〜第3射影が**実行できた**ことと
  入出力例／コード断片を追加。模式（現 §5.4「具体的コードは紙幅で省略」）を実例で置換。
- **§6（ゴミ）**：オーダ見積りに**実測値の表**（各射影の残余サイズ・出力ゴミ・累積）を併記。
- 再現アーティファクトとしてリポジトリ（コミットハッシュ）に言及。
- ※ この段は本リポジトリではなく論文側で実施。実測結果（サイズ表・入出力例）を渡すこと。

## critical files（本リポジトリ）

| 役割 | パス |
|---|---|
| 特殊化器（改修の主対象） | `examples/spec.rwhile` |
| 名前付き変数版インタプリタ | `examples/ri_fp3.rwhile` |
| 配列版インタプリタ（参照のみ） | `examples/ri.rwhile` |
| 評価エンジン（rupdate 等） | `src/EvalRwhile.ml` |
| 値型 valT | `src/AbsRwhile.ml` |
| 出力整形（count_nodes 追加先） | `src/PrintRwhile.ml` |
| CLI（-stats 追加先） | `src/Main.ml` |
| テスト | `src/TestSuite.ml` |
| プログラム→データ符号化 | `src/Program2DataRwhile.ml` |
| 診断（必読） | `analysis_second_projection.md`（採用）, `analysis_spec_reverse_fix.md`（棄却）, `FUTAMURA.md` |

## 検証（build / run / test）

```sh
cd src
make ri                       # opam install extlib が前提
./ri ../examples/<prog>.rwhile ../examples/<data>.val          # 実行
./ri -p2d ../examples/<prog>.rwhile | wc -c                    # 規模測定（暫定）
./ri -stats ../examples/<prog>.rwhile ../examples/<data>.val   # Stage A 後：ゴミ計測
make test-suite && ./test-suite                                # 全75テスト
./test-suite test first-projection                             # 段階別
```

## リスク・注記
- Stage B（partially-static 値）が研究エンジニアリングの核で、複数セッション規模。古典的 mix の
  self-application 化（Jones/Gomard/Sestoft）の可逆版移植にあたり、設計の試行錯誤を要する。
- コミット前は gitleaks（PreToolUse フックで自動検出）。push はユーザ承認後。
- 論文の機械検証（`2025_Reversible_Projection_IEICE_D/formal/`）はこの実装とは独立。
  系 cor:gmin（g-最小ゴミ、GlYo22 依存）は紙の証明のままとする（既決）。
