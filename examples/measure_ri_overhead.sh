#!/bin/sh
# measure_ri_overhead.sh -- empirical a-rev: the overhead of the REVERSIBLE
# self-interpreter ri.rwhile.
#
# Reversible-Levin R-track (plan_reversible_levin.md): Levin optimality needs a
# reversible-interpreter overhead constant `a-rev` (the reversible twin of the
# classical a = 73, machine-checked in while-C-ocaml/IntEfficient). Before
# proving it we MEASURE it, exactly as the classical side measured a before
# fixing it in SintCost. For each program p and input x this reports
#
#     a-rev(p,x) = steps( ri , (p2d(p) . x) )  /  steps( p , x )
#
# where `steps` = executed-command count (`./ri -steps`, unit-cost). ri.rwhile is
# program-preserving, so its output is (p2d(p) . [p](x)); we verify [p](x) matches
# the direct run, so the ratio is over a CORRECT self-interpretation.
#
# CAVEAT (do not misread): this is a-rev in R-WHILE's COMMAND-step model, NOT
# directly comparable to the classical a = 73 (node-summed evalT model). It
# measures how many R-WHILE commands the reversible self-interpreter runs per
# command of the subject. A fair 73-vs-a-rev comparison needs the two cost models
# reconciled (future work). What IS meaningful here: the magnitude (hundreds x)
# and that it is roughly constant across non-trivial subjects -- the empirical
# analogue of "a is a per-step constant".
#
# Prereq: build the interpreter first:  eval $(opam env); make -C src ri
# Usage:  sh examples/measure_ri_overhead.sh

cd "$(dirname "$0")/.." || exit 1
RI=./src/ri
[ -x "$RI" ] || { echo "build first: eval \$(opam env); make -C src ri"; exit 1; }

tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT

steps_of () {  # program data -> executed-command count
  "$RI" -steps "$1" "$2" 2>&1 >/dev/null | sed -n 's/.*steps=\([0-9][0-9]*\).*/\1/p'
}

# (program : input) pairs -- subjects with a valid .val input in examples/.
PAIRS="reverse:reverse id4:id4 minus:minus rle:rle0 perm_to_code:perm_to_code piorder:piorder_input05 compare:compare0"

printf '%-16s %10s %10s %9s %s\n' "program" "steps_p" "steps_ri" "a-rev" "note"
printf '%-16s %10s %10s %9s %s\n' "----------------" "-------" "--------" "--------" "----"
n=0; sum=0; fail=0
for pair in $PAIRS; do
  name=${pair%%:*}
  p="examples/$name.rwhile"; x="examples/${pair##*:}.val"
  [ -f "$p" ] && [ -f "$x" ] || { printf '%-16s %10s\n' "$name" "(no file)"; continue; }
  direct=$("$RI" "$p" "$x" 2>/dev/null)
  case "$direct" in Error*|"") printf '%-16s %10s\n' "$name" "(p failed)"; fail=1; continue;; esac
  # build (p2d(p) . x) and run the reversible self-interpreter on it
  printf '(%s . %s)' "$("$RI" -p2d "$p" 2>/dev/null)" "$(cat "$x")" > "$tmp/in.val"
  riout=$("$RI" examples/ri.rwhile "$tmp/in.val" 2>/dev/null)
  case "$riout" in
    *"$direct"*) ok="ok" ;;                       # ri kept (p2d(p) . [p](x))
    *) ok="MISMATCH"; fail=1 ;;
  esac
  sp=$(steps_of "$p" "$x"); sr=$(steps_of examples/ri.rwhile "$tmp/in.val")
  [ -n "$sp" ] && [ -n "$sr" ] && [ "$sp" -gt 0 ] || { printf '%-16s %10s %10s   (no steps)\n' "$name" "${sp:-?}" "${sr:-?}"; fail=1; continue; }
  ratio=$(awk "BEGIN{printf \"%.1f\", $sr/$sp}")
  note="$ok"; [ "$sp" -lt 10 ] && note="$ok, tiny p (fixed-cost dominated)"
  printf '%-16s %10s %10s %9s %s\n' "$name" "$sp" "$sr" "$ratio" "$note"
  # accumulate only the non-trivial subjects for the summary
  if [ "$ok" = "ok" ] && [ "$sp" -ge 10 ]; then
    n=$((n+1)); sum=$(awk "BEGIN{printf \"%.1f\", $sum + $ratio}")
  fi
done

echo
if [ "$n" -gt 0 ]; then
  printf 'a-rev over %d non-trivial subjects (steps_p >= 10): mean %.0fx  (R-WHILE command-step model)\n' \
    "$n" "$(awk "BEGIN{printf \"%.1f\", $sum/$n}")"
  echo 'cf. classical self-interpreter a = 73 (node-summed evalT model; NOT directly comparable -- see header).'
fi
[ "$fail" -eq 0 ] || { echo "some subjects failed"; exit 1; }
