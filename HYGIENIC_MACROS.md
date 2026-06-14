# 衛生的マクロ展開ガイド（`-hygienic-macros`）

R-WHILE のマクロ展開に関する仕様と、衛生化を前提にプログラムを書く際の指針。

## 背景：2つのセマンティクス

| モード | 起動 | 内部ローカルの扱い |
|---|---|---|
| 非衛生（既定） | （フラグなし） | 内部ローカルを **α変換しない**。マクロ間でローカル名を共有して通信できる |
| 衛生（オプトイン） | `./ri -hygienic-macros ...` | 各展開ごとに内部ローカルを `name-N` に **α変換**する |

- **内部ローカル** = マクロ本体に現れる変数のうち、仮引数でないもの。
- 既定（OFF）の挙動は従来と byte 同一。`spec.rwhile` / `ri.rwhile` / `spec_av.rwhile` など中核プログラムは OFF を前提に書かれており、ON では壊れる。

## なぜ既定が OFF なのか

中核プログラムは「マクロ間でローカル名を共有して通信する」イディオムに依存している：

- `AUX` は引数 `X` を使わず、ローカル `Y` に結果を書き、`LOOKUP` が自分のローカル `Y` として読む。
- `AUX` / `INV-AUX` がスクラッチ `JJ` / `Vr` を共有する。
- `spec.rwhile` / `ri.rwhile` はストア `Vl` を多数のマクロで**自由参照**（グローバル変数として共有）する。

「意図しない名前衝突バグ」と「意図的な名前共有」は構造的に同一（外側ローカル名＝callee ローカル名）なので、展開器では区別できない。よって自動衛生化は必然的に後者を壊す。だからオプトインにした。

## 衛生化を前提に書くための鉄則

**マクロ境界をまたいで共有する値は、必ず引数（パラメータ）で受け渡す。**

1. **共有スクラッチは引数に昇格する。**
   マクロと、その逆 `INV-` や別マクロとの間で受け渡す変数（前者が残し後者が消費する作業領域）は、すべて仮引数にする。暗黙のローカル共有に頼らない。

2. **グローバル状態（ストア等）も引数で通す。**
   `Vl` のような共有ストアを自由参照しない。それを触る全マクロのシグネチャと全呼び出し位置に引数として通す。

3. **真のローカルだけをローカルにしてよい。**
   そのマクロ呼び出し内で生成・消費が完結し、開始時 nil・終了時 nil になる変数（例：ループ内で `cons U Vl <= Vl; Rev <= cons U Rev` のように毎周設定・消費される `U`）は、α変換されても問題ない。

4. **`INV-` ペアは引数を完全一致させる。**
   `M(...)` と `INV-M(...)` は同じ実引数で呼ぶ。衛生モードでは呼び出し側のローカルが一貫して改名され引数経由で正しく束縛されるので、これで逆変換が成立する。

## 例：捕捉依存 → 衛生クリーンへの書き換え

`examples/lookup_hygienic.rwhile` 参照（`lookup.rwhile` の衛生クリーン版）。

変更点：`AUX` の暗黙共有ローカル `Y, T, Vr, JJ` を引数 `Elem, Rest, Rev, Cnt` に昇格。`U`（毎周完結）はローカルのまま。

```
macro LOOKUP(Vl,J,X)
  AUX(Vl,J,Elem,Rest,Rev,Cnt);
  X ^= Elem;
  INV-AUX(Vl,J,Elem,Rest,Rev,Cnt)

macro AUX(Vl,J,Elem,Rest,Rev,Cnt)
  from (=? Cnt nil) loop
    cons U Vl <= Vl;
    Rev <= cons U Rev;
    Cnt <= cons nil Cnt
  until (=? Cnt J);
  cons Elem Rest <= Vl
```

結果：`-hygienic-macros` の ON / OFF 両方で正しく動作（後方互換）。元の `lookup.rwhile` は ON で
`Assertion =? JJ-2 J is not true`（`INV-AUX` の改名された `JJ-2` が `AUX` のスクラッチと不一致）で破綻する。

## 動作確認

```bash
cd src && make
./ri -exp /path/to/prog.rwhile               # 展開結果を確認（ON時は name-N 改名が見える）
./ri -hygienic-macros prog.rwhile data.val   # 衛生モードで評価
make run-tests                               # テスト群（hygienic-macros グループ3件を含む）
```

## 中核プログラムの現状

`spec.rwhile` / `ri.rwhile` / `spec_av.rwhile` は `Vl` をグローバル自由参照しており、衛生化には
全マクロへの `Vl` 通しと全自由変数の監査を要する大規模改修になる。現時点では未対応のまま
（これらは `-hygienic-macros` を **付けずに** 実行すること）。

参考実装：
- フラグ本体：`src/MacroRwhile.ml`（`hygienic` ref, `expansionSubst`）, `src/Subst.ml`（`varsCom`）, `src/Main.ml`
- 変数収集：`Subst.varsCom` / `varsExp` / `varsPat`
