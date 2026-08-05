#!/bin/sh
# bench.sh - per-module type-checking cost (peak RSS and wall time).
#
# CAREFUL: Agda 2.7+ keeps interfaces in `_build/<version>/agda/`, and it
# decides whether to re-check from a CONTENT HASH -- so `touch` does not
# invalidate anything, and deleting `*.agdai` next to the source measures
# nothing.  This script removes the interface from `_build` so the module is
# really re-checked (its dependencies still load from their interfaces, so
# what you get is the cost of that module alone).
#
# Usage: cd proofs/agda && ./bench.sh [module ...]      (default: all)
set -e
# the interface directory is _build/<version>/agda, but `agda --version` may
# carry a package suffix (2.8.0-r3) that the directory does not, so glob it
DIR=$(ls -d _build/*/agda 2>/dev/null | head -1)
[ -n "$DIR" ] || DIR=.
mods="$*"
[ -n "$mods" ] || mods=$(ls RWhile*.agda | sed 's/\.agda$//')
printf '%-22s %10s %8s\n' module MB s
for m in $mods; do
  rm -f "$DIR/$m.agdai"
  out=$(/usr/bin/time -f "%M %e" agda --safe "$m.agda" 2>&1 | tail -1)
  set -- $out
  printf '%-22s %10s %8s\n' "$m" "$(( $1 / 1024 ))" "$2"
done
