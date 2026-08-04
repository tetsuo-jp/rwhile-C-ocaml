#!/bin/sh
# metrics.sh - print the self-interpreter's proved cost constants.
#
# Each number is obtained by asking the type checker to normalise the
# expression (the mismatch in `X ≡ 0` reports X's value), so these are the
# constants the PROOFS use, not an estimate.
#
# Usage: cd proofs/agda && ./metrics.sh
set -e
exprs="CC:0 CC:1 lpDStep:0 lpDStep:1 lpAStep:0 lpAStep:1 assStep:0 assStep:1
       condStep:0 condStep:1 condEStep:0 condEStep:1 evalB:0 evalB:1"
printf '%-14s %8s %8s   %s\n' "constant" "M=0" "M=1" "slope"
for f in CC lpDStep lpAStep assStep condStep condEStep evalB; do
  vals=""
  for m in 0 1; do
    cat > _Metric.agda <<EOF
module _Metric where
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open import RWhileSIStep
open import RWhileSIEval using (evalB)
open import RWhileSISim using (CC; SL; CCy)
t : $f $m ≡ 0
t = refl
EOF
    v=$(agda _Metric.agda 2>&1 | grep -oE '^[0-9]+ != 0' | head -1 | cut -d' ' -f1)
    vals="$vals ${v:-0}"
  done
  set -- $vals
  printf '%-14s %8s %8s   %s\n' "$f" "$1" "$2" "$(($2 - $1))"
done
rm -f _Metric.agda _Metric.agdai
