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

# パスはスクリプトの位置から導く。機械ごとにホームが違う（owari=/home/a、
# s3=/home/tetsuo）ので、絶対パスを焼き込むと移設のたびに黙って壊れる。
AR="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$AR/.." && pwd)"
WT="${AUTORESEARCH_WT:-${REPO}-autoresearch}"
BRANCH="autoresearch/nightly"
REPORTS="$AR/reports"
WORKLOG_PY="$HOME/dev/notion/worklog.py"
WORKLOG_VENV="$HOME/dev/notion/.venv/bin/python"

# 既定は Opus 5（~/.claude/rules/performance.md:「既定は Opus 5。Fable 5 はユーザーが
# 明示的に求めたときだけ使う」）。2026-08-10 の初回 run は fable-5 を指定していたため
# "Fable 5 requires usage credits" で選定が 3 回とも即死し、解くフェーズが一度も
# 走らなかった。ゲートは全部緑だったので systemd 的には成功に見えた。
MODEL="${MODEL:-claude-opus-5}"
MAX_TURNS="${MAX_TURNS:-400}"
CLAUDE_TIMEOUT="${CLAUDE_TIMEOUT:-14400}"   # 4h（systemd 側 RuntimeMaxSec=5h）
SMOKE="${SMOKE:-0}"
DRY="${DRY:-0}"
if [ "$SMOKE" = "1" ]; then
  MODEL="claude-haiku-4-5"; MAX_TURNS=6; CLAUDE_TIMEOUT=900
fi

# systemd --user は対話シェルの PATH を持たない。brew・opam・claude の場所を
# 自力で足す（unit の Environment だけでは switch 名が機械ごとに違って書けない）。
# 実測 2026-08-09: これが無いと ocamlfind も claude も見つからず rc=127 で黙って死ぬ。
eval "$(opam env 2>/dev/null)" || true
for d in "$HOME/.local/bin" /home/linuxbrew/.linuxbrew/bin; do
  case ":$PATH:" in *":$d:"*) ;; *) [ -d "$d" ] && PATH="$d:$PATH" ;; esac
done
export PATH
for c in claude agda make git python3; do
  command -v "$c" >/dev/null || { echo "必須コマンドが無い: $c (PATH=$PATH)" >&2; exit 1; }
done

DATE="$(date +%F)"
mkdir -p "$REPORTS"
REPORT="$REPORTS/$DATE.md"
SEL_LOG="$REPORTS/$DATE-select.log"
SOLVE_LOG="$REPORTS/$DATE-solve.log"
TASK="$REPORTS/$DATE-task.json"

LOCK="/tmp/autoresearch-rwhile-$(id -u).lock"
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
agda_base="$( (cd "$WT/proofs/agda" && timeout 3600 ./check.sh 2>&1) | tail -1 )"
case "$agda_base" in
  *"FAIL=0"*) note "- ✓ ベースライン Agda: $agda_base" ;;
  *) note "- ✗ ベースライン Agda が緑でない: $agda_base"; fail_out "ベースラインの Agda 検査が失敗" ;;
esac

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

ATTEMPTS="${ATTEMPTS:-3}"
attempt=0
task_ok=0
while [ "$attempt" -lt "$ATTEMPTS" ]; do
  attempt=$((attempt + 1))
  if [ "$DRY" = "1" ]; then
    head -1 "$CANDS" | python3 -c '
import json,sys
c = json.loads(sys.stdin.read())
print(json.dumps({"id": c["id"], "title": c["title"], "why": "DRY run",
                  "accept_cmd": "test -f /nonexistent-acceptance-probe"}, ensure_ascii=False))' >"$TASK"
    note "- DRY: LLM を呼ばず既定課題を使う"
  else
    sel_prompt="$(cat "$AR/prompt-select.md")
$(printf '\n## 候補（JSONL）\n')
$(cat "$CANDS")"
    # 選定に 8 ターンは足りない（2026-08-09 実測: haiku がファイルを読み回って上限に達し、
    # JSON を出さないまま終わった）。選定は 1 ターンあたりが安いので厚めに取る。
    (cd "$WT" && timeout 1800 claude -p "$sel_prompt" --model "$MODEL" --max-turns "${SELECT_TURNS:-30}" \
        --permission-mode acceptEdits) >"$SEL_LOG.$attempt" 2>&1
    python3 "$AR/extract_task.py" "$SEL_LOG.$attempt" "$TASK" || true
  fi
  if [ ! -s "$TASK" ]; then
    # モデルが使えない・認証が切れている類は「選定の失敗」ではないので、
    # 3 回繰り返しても同じ結果にしかならない。理由を出して即座に止める。
    if grep -qiE "usage credits|/usage-credits|not authenticated|please run .?login|invalid api key|rate limit" \
         "$SEL_LOG.$attempt" 2>/dev/null; then
      note "- ✗ **モデルが使えない**（選定の失敗ではない）。$MODEL の手当てが要る:"
      printf '    %s\n' "$(head -2 "$SEL_LOG.$attempt")" >>"$REPORT"
      worklog "モデル不在で中止: $MODEL（$SEL_LOG.$attempt）"
      note ""
      note "**中止**: モデル $MODEL が使えないため、選定も解くフェーズも走っていない"
      exit 1
    fi
    note "- ✗ 試行 $attempt: 課題の選定に失敗（$SEL_LOG.$attempt）"
    continue
  fi
  ACCEPT="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["accept_cmd"])' "$TASK")"
  TITLE="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["title"])' "$TASK")"
  TID="$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1])).get("id",""))' "$TASK")"
  note "- 試行 $attempt の課題: **$TITLE**"
  note "  受入コマンド: \`$ACCEPT\`"

  # 受入コマンドが「そもそも通り得る」かの静的検査。
  # 事前 FAIL 検査は「いま落ちる」しか見ないので、壊れたコマンドも通してしまう。
  val_out="$(python3 "$AR/validate_accept.py" "$TASK" "$WT" 2>&1)"; val_rc=$?
  if [ $val_rc -ne 0 ]; then
    note "  ✗ 受入コマンドが不正:"
    printf '%s\n' "$val_out" | sed 's/^/    /' >>"$REPORT"
    python3 "$AR/ledger.py" mark --id "$TID" --status rejected --date "$DATE" \
      --note "受入コマンドが不正: $val_out" >/dev/null 2>&1 || true
    grep -v "\"id\": \"$TID\"" "$CANDS" >"$CANDS.tmp" && mv "$CANDS.tmp" "$CANDS"
    : >"$TASK"
    continue
  fi
  note "  ✓ 受入コマンドの静的検査を通過"

  # 受入コマンドが「着手前に失敗する」ことの確認（この掟が全体を支えている）
  (cd "$WT" && timeout 1800 bash -c "$ACCEPT") >"$REPORTS/$DATE-accept-before.log" 2>&1
  before_rc=$?
  if [ $before_rc -ne 0 ]; then
    note "  ✓ 着手前に失敗する (rc=$before_rc)＝解くべき課題である"
    task_ok=1
    break
  fi
  note "  ✗ **着手前から通っている**。課題として成立しないので却下し、次の候補へ"
  python3 "$AR/ledger.py" mark --id "$TID" --status rejected --date "$DATE" \
    --note "受入コマンドが着手前から通る: $ACCEPT" >/dev/null 2>&1 || true
  grep -v "\"id\": \"$TID\"" "$CANDS" >"$CANDS.tmp" && mv "$CANDS.tmp" "$CANDS"
  : >"$TASK"
done
if [ "$task_ok" -ne 1 ]; then
  note ""
  note "- $ATTEMPTS 回とも課題を確定できなかった。今夜は解かない"
  worklog "課題を確定できず（$ATTEMPTS 回とも事前 FAIL 検査で却下 or 選定失敗）"
  exit 0
fi

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

# 受入の変異検査（2026-08-10、指揮者セッションの指摘）。
#
# `creates` 課題では事前 FAIL 検査が空回りする。受入コマンドが
# `./test-suite test <新設群>` なら、着手前は「群が無い」ので必ず落ち、着手後は
# 「群を作った」だけで通りうる。**バグを直さなくても「前は落ちて後は通る」を満たせる。**
# テストを書く人・通す人・採点する人が同一になっている。
#
# そこで **実装側の変更だけを退避して受入コマンドを再実行**する。ここで通ってしまったら、
# そのテストは実装を検査していない＝受入不成立とする。Agda ゲートの変異注入と同じ発想。
mutation_rc=0
if [ $after_rc -eq 0 ]; then
  # 退避するのは **既存ファイルの変更（M）だけ**。新規追加（A/untracked）は退避しない。
  # 理由: テストの入力資産（examples/*.rwhile の最小再現など）は新規追加で入るので、
  # これを退避すると **テストが走れなくなって rc≠0 になり、「✓ 検査している」と誤判定**する。
  # 実装の修正は既存ファイルの変更として入る（ri.rwhile, spec_av.rwhile, src/*.ml）。
  impl_files="$(git -C "$WT" diff --name-only --diff-filter=M HEAD -- . ':(exclude)src/TestSuite.ml' 2>/dev/null || true)"
  if [ -n "$impl_files" ]; then
    # shellcheck disable=SC2086
    if git -C "$WT" stash push -q -m accept-mutation -- $impl_files 2>/dev/null; then
      (cd "$WT" && timeout 1800 bash -c "$ACCEPT") >"$REPORTS/$DATE-accept-mutated.log" 2>&1
      mut_rc=$?
      git -C "$WT" stash pop -q 2>/dev/null || note "- ⚠ stash pop に失敗。worktree を手で確認すること"
      if [ $mut_rc -eq 0 ]; then
        note "- ✗ **変異検査で受入が通ってしまった**（実装を戻しても緑）。"
        note "  そのテストは実装を検査していない。受入は不成立とする"
        mutation_rc=1
      elif grep -q '\[FAIL\]' "$REPORTS/$DATE-accept-mutated.log" 2>/dev/null; then
        # rc≠0 には「テストが走って落ちた」と「そもそも走れなかった」の 2 通りがある。
        # Alcotest の [FAIL] が出ていれば前者＝実装を検査している。
        note "- ✓ 変異検査: 実装を戻すと群が**実行されて失敗**する (rc=$mut_rc, [FAIL] 検出)"
      else
        note "- ⚠ **変異検査は判定不能**: 実装を戻すと rc=$mut_rc だが [FAIL] が出ていない。"
        note "  テストが落ちたのか、そもそも走れなかったのかが区別できない。受入は不成立とする"
        mutation_rc=1
      fi
      # 戻したあとに緑へ復帰することも確かめる（stash pop の失敗や副作用で木が
      # 壊れたまま「緑だった」と報告する経路を塞ぐ）。
      (cd "$WT" && timeout 1800 bash -c "$ACCEPT") >"$REPORTS/$DATE-accept-restored.log" 2>&1
      restored_rc=$?
      if [ $restored_rc -ne 0 ]; then
        note "- ✗ **stash を戻したあと受入が緑に復帰しない** (rc=$restored_rc)。木が壊れている"
        mutation_rc=1
      fi
    else
      note "- ⚠ 変異検査を実施できなかった（stash 失敗）。judge は参考値として読むこと"
    fi
  else
    note "- ✗ **実装側の変更（既存ファイルの修正）がゼロ**。受入は不成立とする"
    mutation_rc=1
  fi
fi

# `creates` の検算。宣言しただけで作られていなければ受入は不成立とする。
# これが無いと `creates` は「静的検査を黙らせる呪文」になり、綴り間違いを宣言して
# 素通りできてしまう（指揮者セッションの指摘、2026-08-10）。
creates_rc=0
CREATES="$(python3 -c 'import json,sys
d=json.load(open(sys.argv[1])); c=d.get("creates") or []
print(" ".join([c] if isinstance(c,str) else c))' "$TASK" 2>/dev/null || true)"
if [ -n "$CREATES" ]; then
  for g in $CREATES; do
    if grep -qE "^[[:space:]]*\"$g\",[[:space:]]*\[" "$WT/src/TestSuite.ml" 2>/dev/null; then
      note "- ✓ 宣言どおり群 '$g' が作られている"
    else
      note "- ✗ **creates に挙げた群 '$g' が存在しない**（宣言が果たされていない）"
      creates_rc=1
    fi
  done
fi

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

# 「run は成功したが本題は 1 行も進んでいない」を機械が判定する。
# 今夜これを人が2回見つけた（モデル不在の空振り／静的検査が正しく弾いた空振り）。
# どちらも systemd 的には成功で、レポート本文を開くまで分からなかった。
if [ "$REV_BEFORE" = "$REV_AFTER" ]; then
  note "- ⚠ **差分ゼロ: run は完了したが本題は 1 行も進んでいない**"
  progressed=0
else
  progressed=1
fi

if [ $after_rc -eq 0 ] && [ $tests_rc -eq 0 ] && [ "$comp2_post" -ge 1 ] && [ "$probe_ok" = "1" ] \
   && [ "$creates_rc" -eq 0 ] && [ "$progressed" -eq 1 ] && [ "$mutation_rc" -eq 0 ]; then
  status="done"; verdict="緑: 受入通過・テスト緑・fp2 維持・プローブ生存。差分 $REV_BEFORE→$REV_AFTER"
else
  status="deferred"; verdict="要レビュー: accept=$after_rc tests=$tests_rc fp2=$comp2_post probe=$probe_ok creates=$creates_rc 差分=$progressed 変異=$mutation_rc"
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
