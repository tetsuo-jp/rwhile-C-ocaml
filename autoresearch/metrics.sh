#!/usr/bin/env bash
# metrics.sh — このリポジトリの「動いたら気づきたい数」を JSON 1 個にまとめる。
#
# 退行の検出はここが正本。enumerate.sh が baseline.json と突き合わせ、差が出た
# ものを残課題の候補にする。**測るだけ。判定はしない。**
#
#   ./metrics.sh            現在値を stdout へ（JSON）
#   ./metrics.sh > baseline.json    基準を取り直す（人がやること）
#
# 速さの方針: 5 分以内。Agda の全検査（5.5 分）はここに入れない——
# nightly.sh がゲートとして別に回すので、二重には払わない。
set -u
cd "$(dirname "$0")/.." || exit 1
REPO="$PWD"

j_str() { printf '"%s"' "$(printf '%s' "$1" | sed 's/\\/\\\\/g; s/"/\\"/g')"; }

# ── テスト総数（Alcotest の最終行から） ──────────────
tests_line="$( (cd "$REPO/src" && timeout 900 make run-tests 2>&1 | tail -3) || true)"
tests_n="$(printf '%s' "$tests_line" | sed -n 's/.*Test Successful in [0-9.]*s\. \([0-9]*\) tests run\..*/\1/p')"
tests_ok=true
[ -n "$tests_n" ] || { tests_n=0; tests_ok=false; }

# SKIP の数（= 走っていない検査。増えたら残課題） ────
skip_n="$( (cd "$REPO/src" && ./test-suite 2>&1 | grep -c '\[SKIP\]') || true)"
[ -n "$skip_n" ] || skip_n=0

# ── fp2 の自己適用（中核成果。false になったら最優先） ─
full_out="$( (cd "$REPO/src" && timeout 1800 ./measure_proj full 2>&1) || true)"
comp2_b="$(printf '%s' "$full_out" | sed -n "s/.*\[comp2\](('S.swap)) == B : \([a-z]*\).*/\1/p" | head -1)"
comp2_ratio="$(printf '%s' "$full_out" | sed -n 's/.*comp2 (+copyprop) = [0-9]* nodes .*ratio \([0-9.]*\) x.*/\1/p' | head -1)"
spec_av_n="$(printf '%s' "$full_out" | sed -n 's/^|spec_av| (program-as-data) = \([0-9]*\) nodes.*/\1/p' | head -1)"
[ -n "$comp2_b" ] || comp2_b="unknown"
[ -n "$comp2_ratio" ] || comp2_ratio="0"
[ -n "$spec_av_n" ] || spec_av_n="0"

# ── 可逆版 Jones 最適性の比（work 指標） ─────────────
# jones-self / dyncontrol の各行を "被験:Jr" で並べる。
jones_out="$( (cd "$REPO/src" && timeout 600 ./measure_proj jones-self 2>&1) || true)"
jones_json="$(printf '%s' "$jones_out" | awk '
  /^  [a-z_0-9]+ +[0-9]/ { printf "%s{\"subject\":\"%s\",\"jr_work\":%s}", (n++?",":""), $1, substr($(NF-1),1,length($(NF-1))-1) }
  END { }')"
dyn_out="$( (cd "$REPO/src" && timeout 900 ./measure_proj dyncontrol 2>&1) || true)"
dyn_json="$(printf '%s' "$dyn_out" | awk '
  /^  [a-z_0-9]+ +[0-9]/ { printf "%s{\"subject\":\"%s\",\"jr_work\":%s}", (n++?",":""), $1, substr($(NF-1),1,length($(NF-1))-1) }
  END { }')"

# ── Agda: 穴の数（検査そのものは nightly.sh のゲート） ─
postulate_n="$(grep -rlE '^[[:space:]]*postulate' "$REPO"/proofs/agda/RWhile*.agda 2>/dev/null | wc -l | tr -d ' ')"
unsafe_n="$(for f in "$REPO"/proofs/agda/RWhile*.agda; do head -1 "$f" | grep -q -- '--safe' || echo "$f"; done | wc -l | tr -d ' ')"
agda_mods="$(find "$REPO/proofs/agda" -maxdepth 1 -name 'RWhile*.agda' | wc -l | tr -d ' ')"
# 一度も検査されていないモジュール（.agdai が無い）
build_dir="$(find "$REPO/proofs/agda/_build" -maxdepth 2 -type d -name agda 2>/dev/null | head -1)"
unchecked_n=0
if [ -n "$build_dir" ]; then
  for f in "$REPO"/proofs/agda/RWhile*.agda; do
    b="$(basename "$f" .agda)"
    [ -f "$build_dir/$b.agdai" ] || unchecked_n=$((unchecked_n+1))
  done
fi

cat <<EOF
{
  "generated_by": "autoresearch/metrics.sh",
  "tests": { "total": $tests_n, "ran_clean": $tests_ok, "skipped": $skip_n },
  "fp2": { "comp2_eq_B": $(j_str "$comp2_b"), "comp2_ratio": $comp2_ratio, "spec_av_nodes": $spec_av_n },
  "jones_self": [$jones_json],
  "dyncontrol": [$dyn_json],
  "agda": {
    "modules": $agda_mods,
    "files_with_postulate": $postulate_n,
    "files_without_safe": $unsafe_n,
    "never_checked": $unchecked_n
  }
}
EOF
