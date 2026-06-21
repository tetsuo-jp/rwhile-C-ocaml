#!/bin/sh
# check.sh - typecheck every RWhile*.agda module under --safe and report PASS/FAIL.
# Usage:  cd proofs/agda && ./check.sh
# Requires: Agda + the `standard-library` (see rwhile-rev.agda-lib).
set -u
cd "$(dirname "$0")"
pass=0; fail=0; failed=""
for m in RWhile*.agda; do
  if agda --safe "$m" >/tmp/agda_check_$$.log 2>&1; then
    pass=$((pass+1))
  else
    fail=$((fail+1)); failed="$failed $m"
    echo "FAIL: $m"; tail -5 /tmp/agda_check_$$.log
  fi
done
rm -f /tmp/agda_check_$$.log
echo "PASS=$pass FAIL=$fail"
[ "$fail" -eq 0 ] || exit 1
