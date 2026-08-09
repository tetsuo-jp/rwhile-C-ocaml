あなたは R-WHILE（可逆言語）の処理系と、その Agda 形式化を持つリポジトリの
夜間ワーカーです。**下の課題を 1 件だけ**解いてください。

## 最初に読む

- `CLAUDE.md`（現状節。読む順・やってはいけないことが書いてある）
- 課題が指す先（`FINDINGS_reversible_projections.md`・`RESEARCH_ROADMAP.md`・
  `AGDA_CORRESPONDENCE.md`・該当のテスト群）

## 進め方

1. **テストファースト。** 期待する振る舞いを先に固定してから実装・証明する
2. 課題の `accept_cmd` が**あなたの申告と無関係に harness から再実行されます**。
   それが通ることが唯一の合格条件です。**受入コマンドを書き換えて通すのは不正**です
3. 常設ゲートも harness が回します。**どれか 1 つでも壊したら不合格**:
   - `cd src && make run-tests` が全件緑
   - `./measure_proj full` で `[comp2](('S.swap)) == B : true`（fp2 の自己適用＝中核成果）
   - `cd proofs/agda && ./check.sh` が FAIL=0
   - 変異注入プローブが検出されること（検証器が生きていること）
4. 進捗と判断は `NIGHTLOG.md`（worktree のルート）に追記する。
   **解けなかったときは、どこで詰まったかを次の人が続けられる精度で書く**こと。
   これは失敗ではなく、翌晩の入力になります

## 掟

- **沈黙を成功と読まない。** Agda は `_build/*/agda/<M>.agdai` の生成で、
  OCaml は Alcotest の最終行で確かめる。検査器は OOM で殺されても静かに終わる
- **背伸びしない。** 証明できていないものを「証明した」と書かない。
  `postulate` を置いたら `NIGHTLOG.md` の冒頭に列挙する
- **`git push` は絶対にしない。** コミットは harness が最後にまとめて行う
- **`proofs/agda/RWhileRTM*.agda` には触らない**（別の作業が並行している）
- 用語: p⁺ は「義務を満たす**最小の拡張**」（「最小のプログラム」は反証済み。
  `proofs/agda/RWhileJonesRevCE.agda`）
- 長時間になりうる実行は `~/.claude/bin/runcap -m 40 -t 3600 -- <cmd>` で上限を掛ける
- **論文の主張の格上げ（層の昇格）は人間の仕事**。あなたは事実と証拠を積むところまで
