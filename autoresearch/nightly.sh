#!/usr/bin/env bash
# nightly.sh — 「洗い出し → 解く → 検証機で確かめる」を無人で 1 周する。
#
# periodic-tm/autoresearch/nightly.sh が原型。違いは **問題が固定されていない**
# こと: enumerate.py が信号から候補を出し、LLM が 1 件選んで受入判定を
# コマンドとして書き、harness がそれを独立に回す。
#
#   ./nightly.sh          本番
#   SMOKE=1 ./nightly.sh  haiku・少ターン。配管の全通し（LLM は呼ぶ）
#   DRY=1   ./nightly.sh  LLM を一切呼ばない。ゲートと台帳の配管だけ試す
#
# 設計の要（これを外すとループは空回りする）:
#   1. 受入判定は着手前に「コマンド」として確定する
#   2. そのコマンドが着手前に FAIL することを harness が確認する
#      （通ってしまう課題は課題ではない。捨てる）
#   3. 合否は Claude の申告と無関係に harness が判定する
#   4. 却下・完了は台帳に載せ、二度と提案させない
set -u

REPO="/home/a/dev/github.com/tetsuo-jp/rwhile-C-ocaml"
WT="/home/a/dev/github.com/tetsuo-jp/rwhile-C-ocaml-autoresearch"
BRANCH="autoresearch/nightly"
AR="$REPO/autoresearch"
REPORTS="$AR/reports"
WORKLOG_PY="/home/a/dev/notion/worklog.py"
WORKLOG_VENV="/home/a/dev/notion/.venv/bin/python"

MODEL="${MODEL:-claude-fable-5}"
MAX_TURNS="${MAX_TURNS:-400}"
CLAUDE_TIMEOUT="${CLAUDE_TIMEOUT:-14400}"   # 4h（systemd 側 RuntimeMaxSec=5h）
SMOKE="${SMOKE:-0}"
DRY="${DRY:-0}"
if [ "$SMOKE" = "1" ]; then
  MODEL="claude-haiku-4-5"; MAX_TURNS=6; CLAUDE_TIMEOUT=900
fi

DATE="$(date +%F)"
mkdir -p "$REPORTS"
REPORT="$REPORTS/$DATE.md"
SEL_LOG="$REPORTS/$DATE-select.log"
SOLVE_LOG="$REPORTS/$DATE-solve.log"
TASK="$REPORTS/$DATE-task.json"

LOCK="/tmp/autoresearch-rwhile.lock"
exec 9>"$LOCK"
flock -n 9 || { echo "既に走っている ($LOCK)"; exit 1; }

note() { printf '%s\n' "$*" >>"$REPORT"; }
worklog() {
  [ -x "$WORKLOG_VENV" ] || return 0
  "$WORKLOG_VENV" "$WORKLOG_PY" add --project "$REPO" \
    --title "夜間 autoresearch: rwhile-C-ocaml（$DATE）" --kind "研究" \
    --request "夜間の無人ループ（洗い出し→解く→検証）" \
    --work "harness=autoresearch/nightly.sh model=$MODEL task=$TASK" \
    --result "$1" >/dev/null 2>&1 || true
}
fail_out() { note ""; note "**中止**: $1"; worklog "中止: $1"; echo "中止: $1"; exit 1; }

: >"$REPORT"
note "# 夜間 autoresearch レポート $DATE"
note ""
note "- model: \`$MODEL\`  max-turns: $MAX_TURNS  timeout: ${CLAUDE_TIMEOUT}s  SMOKE=$SMOKE DRY=$DRY"

# ── 0. worktree を整える ─────────────────────────────
if [ ! -d "$WT" ]; then
  git -C "$REPO" worktree add -B "$BRANCH" "$WT" >/dev/null 2>&1 \
    || fail_out "worktree を作れなかった: $WT"
  note "- worktree を新設: $WT ($BRANCH)"
fi
if [ -n "$(git -C "$WT" status --porcelain)" ]; then
  git -C "$WT" add -A
  git -C "$WT" -c core.hooksPath=/dev/null commit -m "autoresearch: 前回の未コミット分を退避 ($DATE)" >/dev/null
  note "- 前夜の未コミット分を退避コミットした"
fi
CUR="$(git -C "$REPO" rev-parse --abbrev-ref HEAD)"
if git -C "$WT" merge --no-edit "$CUR" >/dev/null 2>&1; then
  note "- $CUR をマージ: $(git -C "$WT" rev-parse --short HEAD)"
else
  git -C "$WT" merge --abort >/dev/null 2>&1
  note "- ⚠ $CUR のマージが衝突。前夜の状態のまま続行（朝に手で解消）"
fi
REV_BEFORE="$(git -C "$WT" rev-parse --short HEAD)"

# ── 0.5. worktree を実行可能にする ───────────────────
# 新しい worktree にはビルド成果物も Agda のキャッシュも無い。Agda は内容ハッシュで
# 判定するので、本体の _build をコピーすれば 121 モジュールの再検査を払わずに済む。
if [ ! -d "$WT/proofs/agda/_build" ] && [ -d "$REPO/proofs/agda/_build" ]; then
  cp -a "$REPO/proofs/agda/_build" "$WT/proofs/agda/_build"
  note "- Agda の _build を本体からコピー（内容ハッシュ判定なので安全）"
fi
if ! (cd "$WT/src" && timeout 1800 make ri measure_proj specsize >/dev/null 2>&1); then
  fail_out "worktree のビルドが失敗（ri / measure_proj）"
fi
note "- ✓ worktree のビルド（ri・measure_proj・specsize）"

# ── 1. ベースライン: 常設ゲートが最初から緑か ────────
gate() {  # gate <名前> <ディレクトリ> <コマンド...>
  local name="$1" dir="$2"; shift 2
  local out rc
  out="$( (cd "$dir" && timeout 3600 "$@" 2>&1) )"; rc=$?
  printf '%s' "$out" | tail -3 >>"$REPORT.gate.$name"
  return $rc
}
if ! gate tests "$WT/src" make run-tests; then
  note "- ✗ ベースラインのテストが落ちている。夜間 run 中止"
  fail_out "ベースラインの make run-tests が失敗"
fi
note "- ✓ ベースライン make run-tests 通過"
comp2="$( (cd "$WT/src" && timeout 1800 ./measure_proj full 2>&1) | grep -c "\[comp2\]((.S.swap)) == B : true" || true)"
[ "$comp2" -ge 1 ] || fail_out "ベースラインで fp2 が壊れている（[comp2] != B）"
note "- ✓ ベースライン fp2（[comp2](('S.swap)) == B : true）"

# ── 2. 変異注入: 検証器が本当に落とすか ──────────────
probe_agda() {
  cat >"$WT/proofs/agda/ProbeFalse.agda" <<'EOF'
{-# OPTIONS --safe #-}
module ProbeFalse where
open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
probe : 1 ≡ 2
probe = refl
EOF
  (cd "$WT/proofs/agda" && timeout 600 agda --safe ProbeFalse.agda) >/dev/null 2>&1
  local rc=$?
  rm -f "$WT/proofs/agda/ProbeFalse.agda"
  return $rc
}
if probe_agda; then
  note "- ✗ Agda の変異注入が素通り（偽の証明が通った）。中止"
  fail_out "Agda の変異注入プローブが検出されなかった"
fi
note "- ✓ Agda の変異注入を検出（型検査器は生きている）"

# ── 3. 洗い出し（決定的）＋ 課題の選定（LLM その1） ──
CANDS="$REPORTS/$DATE-candidates.jsonl"
[ -x "$WT/autoresearch/enumerate.py" ] \
  || fail_out "worktree に autoresearch/enumerate.py が無い（本体でコミットして worktree にマージすること）"
(cd "$WT" && timeout 2400 ./autoresearch/enumerate.py >"$CANDS") 2>>"$REPORT.enum" || true
n_cand="$(grep -c . "$CANDS" 2>/dev/null || true)"
[ -n "$n_cand" ] || n_cand=0   # grep -c は 0 件のとき非ゼロ終了する。|| echo 0 だと "0\n0" になる
note "- 候補 $n_cand 件（\`$CANDS\`）"
if [ "$n_cand" -eq 0 ]; then
  note "- 候補ゼロ＝**枯れた**。人間に次のテーマを求めること"
  worklog "候補ゼロ（枯れた）。次のテーマは人間が決める"
  exit 0
fi

if [ "$DRY" = "1" ]; then
  # 配管試験用の既定課題: 先頭候補を、必ず失敗する受入コマンドで包む
  head -1 "$CANDS" | python3 -c '
import json,sys
c = json.loads(sys.stdin.read())
print(json.dumps({"id": c["id"], "title": c["title"],
                  "why": "DRY run",
                  "accept_cmd": "test -f /nonexistent-acceptance-probe"}, ensure_ascii=False))' >"$TASK"
  note "- DRY: LLM を呼ばず既定課題を使う"
else
  sel_prompt="$(cat "$AR/prompt-select.md")
$(printf '\n## 候補（JSONL）\n')
$(cat "$CANDS")"
  (cd "$WT" && timeout 1800 claude -p "$sel_prompt" --model "$MODEL" --max-turns 8 \
      --permission-mode acceptEdits) >"$SEL_LOG" 2>&1
  # 最後の JSON オブジェクトを取り出す
  python3 - "$SEL_LOG" "$TASK" <<'EOF' || true
import json, re, sys
txt = open(sys.argv[1], errors="replace").read()
best = None
for m in re.finditer(r"\{[^{}]*\"accept_cmd\"[^{}]*\}", txt, re.S):
    try:
        best = json.loads(m.group(0))
    except Exception:
        pass
if best:
    json.dump(best, open(sys.argv[2], "w"), ensure_ascii=False)
EOF
fi
[ -s "$TASK" ] || fail_out "課題の選定に失敗（$SEL_LOG を見ること）"
ACCEPT="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["accept_cmd"])' "$TASK")"
TITLE="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["title"])' "$TASK")"
TID="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("id",""))' "$TASK")"
note "- 課題: **$TITLE**"
note "- 受入コマンド: \`$ACCEPT\`"

# ── 4. 受入コマンドが「着手前に失敗する」ことの確認 ──
(cd "$WT" && timeout 1800 bash -c "$ACCEPT") >"$REPORTS/$DATE-accept-before.log" 2>&1
before_rc=$?
if [ $before_rc -eq 0 ]; then
  note "- ✗ 受入コマンドが**着手前から通っている**。課題として成立しない。中止"
  python3 "$AR/ledger.py" mark --id "$TID" --status rejected \
    --note "受入コマンドが着手前から通る: $ACCEPT" >/dev/null 2>&1 || true
  fail_out "受入コマンドが着手前に成功した（赤を先に見せていない）"
fi
note "- ✓ 受入コマンドは着手前に失敗する (rc=$before_rc)＝解くべき課題である"

# ── 5. 解く（LLM その2） ─────────────────────────────
if [ "$DRY" = "1" ]; then
  note "- DRY: 解くフェーズは省略"
  claude_rc=0
else
  solve_prompt="$(cat "$AR/prompt-solve.md")
$(printf '\n## 今夜の課題\n')
$(cat "$TASK")"
  note "- Claude 開始: $(date +%H:%M:%S)"
  (cd "$WT" && timeout "$CLAUDE_TIMEOUT" claude -p "$solve_prompt" \
      --model "$MODEL" --max-turns "$MAX_TURNS" \
      --permission-mode acceptEdits) >"$SOLVE_LOG" 2>&1
  claude_rc=$?
  note "- Claude 終了: $(date +%H:%M:%S) (rc=$claude_rc; 124=時間上限)"
fi

# ── 6. 事後検証（申告とは independently 判定する） ───
(cd "$WT" && timeout 1800 bash -c "$ACCEPT") >"$REPORTS/$DATE-accept-after.log" 2>&1
after_rc=$?
if [ $after_rc -eq 0 ]; then note "- ✓ 受入コマンドが通った"; else note "- ✗ 受入コマンドは通らなかった (rc=$after_rc)"; fi

gate tests_post "$WT/src" make run-tests; tests_rc=$?
if [ $tests_rc -eq 0 ]; then note "- ✓ 事後 make run-tests 通過"; else note "- ✗ 事後 make run-tests 失敗 (rc=$tests_rc)"; fi
comp2_post="$( (cd "$WT/src" && timeout 1800 ./measure_proj full 2>&1) | grep -c "\[comp2\]((.S.swap)) == B : true" || true)"
if [ "$comp2_post" -ge 1 ]; then note "- ✓ 事後 fp2 維持"; else note "- ✗ 事後 fp2 が壊れた（中核成果の退行）"; fi
agda_out="$( (cd "$WT/proofs/agda" && timeout 3600 ./check.sh 2>&1) | tail -1 )"
note "- Agda: $agda_out"
if probe_agda; then note "- ✗ 事後の変異注入が素通り。今夜の緑は信用しないこと"; probe_ok=0
else note "- ✓ 事後の変異注入も検出"; probe_ok=1; fi

# ── 7. 台帳・差分・ダイジェスト ──────────────────────
if [ -n "$(git -C "$WT" status --porcelain)" ]; then
  git -C "$WT" add -A
  git -C "$WT" -c core.hooksPath=/dev/null commit -m "autoresearch: $DATE $TITLE (accept_rc=$after_rc)" >/dev/null
fi
REV_AFTER="$(git -C "$WT" rev-parse --short HEAD)"

if [ $after_rc -eq 0 ] && [ $tests_rc -eq 0 ] && [ "$comp2_post" -ge 1 ] && [ "$probe_ok" = "1" ]; then
  status="done"; verdict="緑: 受入通過・テスト緑・fp2 維持・プローブ生存。差分 $REV_BEFORE→$REV_AFTER"
else
  status="deferred"; verdict="要レビュー: accept=$after_rc tests=$tests_rc fp2=$comp2_post probe=$probe_ok"
fi
python3 "$AR/ledger.py" mark --id "$TID" --status "$status" --note "$DATE $TITLE / $verdict" >/dev/null 2>&1 || true

note ""
note "## 差分 ($REV_BEFORE → $REV_AFTER)"
note '```'
git -C "$WT" diff --stat "$REV_BEFORE" "$REV_AFTER" >>"$REPORT" 2>&1
note '```'
note ""
note "## 朝のチェックリスト"
note "- [ ] 受入コマンドは**課題を本当に表しているか**（緩い judge を書いていないか）"
note "- [ ] 4 条件（受入・テスト・fp2・プローブ）が緑か"
note "- [ ] 採用するなら $BRANCH を merge、駄目なら reset"
note "- [ ] 論文の主張の格上げは**人間だけ**が行う"
worklog "$verdict"
echo "$verdict"
