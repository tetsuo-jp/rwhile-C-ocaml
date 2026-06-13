# 二村射影と spec.rwhile の現状

## 三つの二村射影とは

**二村射影**（Futamura Projections）は、部分評価器（specializer）を用いた
プログラム変換の理論的枠組みです。R-WHILE インタプリタ `ri.rwhile` と
部分評価器 `spec.rwhile` によって以下の三段階の射影が成立するかが問題です。

### 第1射影（コンパイル）

```
spec(ri, src) = compiled_target
```

インタプリタ `ri` をソースプログラム `src` に関して特殊化すると、
`src` をコンパイルしたターゲットプログラムが得られる。

### 第2射影（コンパイラ生成）

```
spec(spec, ri) = compiler
```

部分評価器 `spec` 自身をインタプリタ `ri` に関して特殊化すると、
`ri` が解釈する言語のコンパイラが得られる。

### 第3射影（コンパイラ生成器の生成）

```
spec(spec, spec) = cogen
```

部分評価器を自分自身に適用すると、
任意のインタプリタからコンパイラを自動生成する「コンパイラ生成器」が得られる。

## 現状の結論

`examples/spec.rwhile` は、少なくとも現在のテストで確認している範囲では
**基本的な第1二村射影の挙動を満たしています**。

具体的には、Alcotest の `spec` カテゴリで次の 4 点を確認済みです。

1. `spec(id, nil)` が実行できる
2. 出力が `(P . (P_res . S))` の形を持つ
3. `spec(id, nil)` が生成した残余プログラムを `ri.rwhile` で `nil` に適用すると `nil` を返す
4. `spec(swap, ('a . 'b))` が生成した残余プログラムを `ri.rwhile` で `nil` に適用すると `('b . 'a)` を返す

したがって、以前の「`spec.rwhile` が広く実行時エラーで失敗している」という分析は、
現在の実装状態には当てはまりません。

---

## 何が検証済みか

### 第1射影

```
spec(ri, src) = compiled_target
```

厳密に一般の場合まで証明したわけではありませんが、少なくとも現在のテストでは
`id` と `swap` について、生成された残余プログラムが元プログラムと同じ意味を持つことを確認しています。

### spec の出力形式

`spec.rwhile` の出力は、現在のテストでは

```
(P . (P_res . S))
```

の形を取ることを前提にしており、その構造は実際に確認されています。

---

## まだ未検証のこと

### 第2射影

```
spec(spec, ri) = compiler
```

現状のテストスイートには、第2射影を直接確認するテストはありません。
したがって、**未検証**です。

### 第3射影

```
spec(spec, spec) = cogen
```

現状のテストスイートには、第3射影を直接確認するテストもありません。
したがって、**未検証**です。

---

## 今後の確認項目

1. `spec(ri, src)` をより多くの `src` で検証する
2. `spec(spec, ri)` の残余プログラムがコンパイラとして振る舞うかをテストする
3. `spec(spec, spec)` の結果が cogen として機能するかをテストする
4. `spec_ext.rwhile` についても同等のテストを追加する

---

## まとめ

| 射影 | 状態 |
|------|------|
| 第1射影 spec(ri, src) = compiled | 部分的に確認済み（`id`, `swap` の基本テストは通過） |
| 第2射影 spec(spec, ri) = compiler | 未検証 |
| 第3射影 spec(spec, spec) = cogen | 未検証 |

---

## 追記（2026-06-14）: 実行デモの現状と第2射影の詰まり

修論 `2024_okubo/thesis/chap4.tex`（可逆二村射影）を参照して第2可逆射影
`comp = [spec]((spec . ri))`（eq:rev_proj2 `comp'' = ⟦rspec⟧(rspec.rint)`）の
実装デモ可否を確認した結果、**第2射影以前に第1射影が本物の `ri.rwhile` 経由で
現在 red** であることが判明した。詳細な診断と段階プランは
[`analysis_second_projection.md`](analysis_second_projection.md) に分離。要点のみ：

- **詰まり①**: `./test-suite test first-projection`（fp1_id/swap/reverse）が
  3件とも `error in update: var=Vl`（`EvalRwhile.rupdate`, `EvalRwhile.ml:73`）で失敗。
  spec の残余化経路で `Vl` のスロットに doNothing 命令が残り XOR 整合性が壊れる
  （`analysis_spec_reverse_fix.md` の問題1〜4と同根）。
  対照: `spec-partial`(swap) と `rint`(rint-on-rint) は green。
  → spec を小プログラムに当てる第1射影は動くが、本物の `ri.rwhile` に当てると壊れる。

- **詰まり②（第2射影の本質的困難）**: 第2射影は spec を spec で特殊化するが、
  spec は100変数の配列ストア `Vl` を**動的インデックス** `LOOKUP/UPDATE`
  （`spec.rwhile:24-39`）で操作するため、self-applicable でない。インデックスが
  動的だと束縛時解析がどの変数か決められず全 dynamic 化 → 自明な残余になる。
  この壁の回避策として ri 側は `ri_fp3.rwhile`（V0/V1/V2 の名前付き変数版）が
  作られているが、spec 自身の配列ストアは未対応。

- **詰まり③**: `'partial` モード（`spec.rwhile:682-762`）が ri の構文形に決め打ちの
  ハックで、一般の partially-static 構造値（read 変数が `(static . dynamic)` を持つ）
  が無い。第2射影では spec の入力 `(P . S)` の P=ri を静的・S を動的にしたいが、
  「全部静的」か「ri 専用 partial」の二択しかない。

- **理論的には**第2射影は eq:rev_proj1 を一段持ち上げる代数的帰結であり易しい。
  難しいのは R-WHILE 上の実行デモ。段階プラン（Stage 0: 第1射影修正 → Stage 1:
  self-applicable な spec → Stage 2: partially-static 構造値 → Stage 3: デモと検証）は
  `analysis_second_projection.md` を参照。

- 規模実測: `spec` の p2d = 2.1MB, `ri` の p2d = 0.5MB。

---

*更新日: 2026-03-19（初版）/ 2026-06-14（実行デモ現状を追記）*
*対象ファイル: examples/spec.rwhile, examples/spec_ext.rwhile, examples/ri.rwhile, examples/ri_fp3.rwhile*
