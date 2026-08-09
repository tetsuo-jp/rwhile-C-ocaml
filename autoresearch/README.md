# autoresearch — 「洗い出し → 解く → 検証機で確かめる」を無人で回す

`yokoyama-lab/periodic-tm/autoresearch` の harness が原型。**違いは問題が固定されて
いないこと**。あちらは定理 9.6 を人が指定するが、ここは残課題の洗い出しも機械が行う。

## なぜこの形か

素朴に「残課題を挙げて解いて」と LLM に頼むと、**もっともらしい課題が無限に出て
ループが空回りする**。そこで洗い出しは**決定的な列挙器**（`enumerate.py`）が行い、
LLM の仕事は「候補から 1 件選び、受入判定をコマンドとして書く」ことだけに絞る。

**設計の要は 4 つ。どれを外してもループは意味を失う。**

1. **受入判定を着手前にコマンドとして確定する**（`accept_cmd`）
2. **そのコマンドが着手前に FAIL することを harness が確認する。**
   通ってしまう課題は課題ではないので、その場で却下する。
   ——これが無いと「既に通っているもの」を課題と称して「解決した」と報告する経路が開く
3. **合否は Claude の申告と無関係に harness が判定する**（受入 + 常設ゲート + プローブ）
4. **却下・完了は台帳に載せ、二度と提案させない**（`ledger.py`）

## ファイル

| | |
|---|---|
| `metrics.sh` | 「動いたら気づきたい数」を JSON で出す。**測るだけ、判定しない** |
| `baseline.json` | その基準値。取り直すのは人間（`./metrics.sh > baseline.json`） |
| `enumerate.py` | 信号 → 候補（JSONL）。**LLM を呼ばない** |
| `ledger.py` / `ledger.json` | 採否台帳。重複提案の防止と「枯れた」の判定 |
| `prompt-select.md` | 候補から 1 件選び `accept_cmd` を書かせるプロンプト（解かせない） |
| `prompt-solve.md` | 解かせるプロンプト |
| `nightly.sh` | 上を 1 周させる本体 |
| `reports/YYYY-MM-DD.md` | 朝に読むレポート（チェックリスト付き） |

## 信号（`enumerate.py`）

増やすときは **「exit code か数で判定できるか」を先に確かめる**こと。文言を拾う
信号は偽陽性を生む（下の棄却例を見よ）。

- `skip-test` 走っていない検査（SKIP は「異常なし」と区別がつかない）
- `open-pin` 期待される失敗として固定された穴（`OPEN` / `KNOWN BUG`）
- `agda-postulate` 証明の穴
- `agda-unchecked` 一度も型検査されていないモジュール（`.agdai` が無い）
- `metric-regress` `baseline.json` からの退行（fp2・テスト数・SKIP 数・Jr(work)・Agda の穴）
- `roadmap-open` ロードマップの未完項目（**優先度は低い**。文言なので機械判定が弱い）

### 棄却した信号（2026-08-09、実際に偽陽性を出したもの）

- **`--safe` プラグマの有無**：`check.sh` は全モジュールに `agda --safe` を
  コマンドラインで渡すので、プラグマが無くても検査は `--safe` で走っている
- **「残り」「要る」を含む行**：完了済みの進捗行（★）まで拾う
- **`was a KNOWN BUG`**：過去形＝**直った印**。候補にしてはいけない

## 使い方

```bash
./nightly.sh            # 本番（systemd から起動される）
SMOKE=1 ./nightly.sh    # haiku・少ターンで配管を全通し（LLM は呼ぶ）
DRY=1 ./nightly.sh      # LLM を一切呼ばず、ゲートと台帳の配管だけ試す
./enumerate.py          # 候補だけ見る
./ledger.py list        # 台帳
```

## 定常運転（systemd, 既定では**入れていない**）

```bash
cp systemd/autoresearch-rwhile.{service,timer} ~/.config/systemd/user/
systemctl --user daemon-reload
systemctl --user enable --now autoresearch-rwhile.timer   # 有効化は人の判断で
systemctl --user disable --now autoresearch-rwhile.timer  # 止め方
```

worktree は `../rwhile-C-ocaml-autoresearch`（ブランチ `autoresearch/nightly`）。
**日中に本体を触るときは main 側で**。worktree には手を入れない（夜間ジョブと衝突する）。

## 朝の手順

1. `reports/YYYY-MM-DD.md` を読む
2. **受入コマンドが課題を本当に表しているかを見る**（緩い judge を書いていないか）。
   ここが人間の最重要チェック。4 条件が緑でも、判定が緩ければ意味がない
3. 採用するなら `autoresearch/nightly` を merge、駄目なら reset
4. **論文の主張の格上げは人間だけが行う**

## 既知の弱点

- **Goodhart 化**：受入コマンドを自分で書くので、通しやすい judge に流れる。
  対策は掟 2（事前 FAIL の強制）と「既存ゲートに合成する」制約だが、**完全ではない**
- **変異注入の設計が全部を決める**。いまは Agda の `1 ≡ 2` プローブのみ。
  主張の数値をずらす変異（`4 <= k` → `5 <= k`、`k+8` → `k+7`）の方が検出力が高い
- **重い課題は 1 晩で終わらない**。「複数専任セッション級」の項目はループに入れず
  人間の判断に残す（`prompt-select.md` で除外している）
