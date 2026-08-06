#!/bin/sh
# check.sh - typecheck RWhile*.agda modules under --safe and report PASS/FAIL.
#
# Usage:  cd proofs/agda && ./check.sh [--si | <module.agda> ...]
#   (no argument)  every RWhile*.agda in this directory
#   --si           only the linear-time self-interpreter layer (27 modules)
#   <module.agda>  just those modules
#
# Agda skips a module whose interface in _build/<version>/agda is still valid
# (it compares a CONTENT hash, not timestamps), so a repeat run only re-checks
# what actually changed -- `--si` narrows the *listing*, not the caching.
#
# Requires: Agda + the `standard-library` (see rwhile-rev.agda-lib).
set -u
cd "$(dirname "$0")"
case "${1:-}" in
  --si) mods="RWhileTime.agda RWhileTimeDec.agda RWhileTimeDet.agda \
RWhileTimeExec.agda RWhileTimeInv.agda RWhileTimeSkip.agda \
RWhileSugar.agda RWhileSurface.agda $(ls RWhileSI*.agda)" ;;
  "")   mods=$(ls RWhile*.agda) ;;
  *)    mods="$*" ;;
esac
pass=0; fail=0; failed=""
for m in $mods; do
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
