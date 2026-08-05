#!/bin/sh
# update-docs.sh - regenerate the NUMBERS in ../../LINEAR_TIME_SI.md.
#
# Every figure in the write-up that can drift (module count, line count,
# check.sh result, the proved constants, the type-checking cost) lives in a
# marked region:
#
#   <!-- METRICS:SUMMARY:BEGIN -->   ... <!-- METRICS:SUMMARY:END -->
#   <!-- METRICS:CONSTANTS:BEGIN --> ... <!-- METRICS:CONSTANTS:END -->
#   <!-- METRICS:BENCH:BEGIN -->     ... <!-- METRICS:BENCH:END -->
#
# and this script rewrites those regions only.  Hand-written prose is never
# touched -- check with `git diff` afterwards.
#
# Usage: cd proofs/agda && ./update-docs.sh [--bench]
#   --bench also re-runs bench.sh (minutes: it re-checks the heavy modules)
set -e
DOC=../../LINEAR_TIME_SI.md
SI_MODULES="RWhileTime.agda RWhileTimeDec.agda RWhileTimeDet.agda RWhileTimeExec.agda \
RWhileTimeInv.agda $(ls RWhileSI*.agda)"

mods=$(echo $SI_MODULES | wc -w)
lines=$(cat $SI_MODULES | wc -l)
pass=$(./check.sh 2>&1 | tail -1)
consts=$(./metrics.sh)
bench=""
# only the SI layer (benching every RWhile*.agda in the repo takes ~30 min)
if [ "$1" = "--bench" ]; then
  bench=$(./bench.sh $(echo $SI_MODULES | sed 's/\.agda//g'))
fi

python3 - "$DOC" "$mods" "$lines" "$pass" "$consts" "$bench" <<'EOF'
import sys, re
doc, mods, lines, pass_, consts, bench = sys.argv[1:7]
s = open(doc).read()

def region(name, body):
    global s
    b, e = f"<!-- METRICS:{name}:BEGIN -->", f"<!-- METRICS:{name}:END -->"
    assert b in s and e in s, f"marker {name} missing"
    i, j = s.index(b) + len(b), s.index(e)
    s = s[:i] + "\n" + body.rstrip() + "\n" + s[j:]

region("SUMMARY",
  f"新規モジュール（`proofs/agda/`、全 {mods} 本・{lines} 行、`./check.sh` は {pass_}）:")
region("CONSTANTS", "```\n" + consts.rstrip() + "\n```")
if bench.strip():
    region("BENCH", "```\n" + bench.rstrip() + "\n```")
open(doc, "w").write(s)
print(f"updated: {mods} modules, {lines} lines, {pass_}")
EOF
