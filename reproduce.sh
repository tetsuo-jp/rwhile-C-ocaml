#!/bin/sh
# reproduce.sh - one-command reproduction of the paper's machine-checkable claims.
#
#   ./reproduce.sh          fast: build, fp1 residual sizes, Agda --safe check
#   ./reproduce.sh full     also comp2 (fp2) size + Simp reduction (slow, minutes)
#
# Reproduces:
#   - the interpreter / specializer build (src/)
#   - fp1 residual sizes (specialisation is effective: residual < interpreter)
#   - [full] comp2 = [spec_av]((spec_av.ri_min)) size and the Simp reduction
#   - all Agda --safe proofs (proofs/agda/)
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
mode="${1:-fast}"

echo "== build (src/) =="
( cd "$HERE/src" && make ri && make measure_proj ) || { echo "build failed"; exit 1; }

echo
echo "== Futamura-projection residual sizes =="
if [ "$mode" = "full" ]; then
  ( cd "$HERE/src" && ./measure_proj full )
else
  ( cd "$HERE/src" && ./measure_proj )
fi

echo
echo "== Agda --safe proofs (proofs/agda/) =="
if command -v agda >/dev/null 2>&1; then
  ( cd "$HERE/proofs/agda" && ./check.sh )
else
  echo "(agda not found; skipping proof check)"
fi

echo
echo "== done =="
