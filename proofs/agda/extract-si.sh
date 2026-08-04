#!/bin/sh
# extract-si.sh - write the VERIFIED self-interpreter out as R-WHILE source.
#
# `RWhileSIShow.showProg` prints a `Cmd` in the implementation's concrete
# syntax; Agda has no IO under --safe, so we let the type checker normalise
# the string and recover it from the error message of a deliberately false
# equation.  The result is a program `src/ri` parses and runs:
#
#   cd proofs/agda && ./extract-si.sh
#   cd ../../src && ./ri -exp   ../proofs/agda/extracted/SI.rwhile
#                   ./ri -steps ../proofs/agda/extracted/SI_run.rwhile <input.val>
#
# SI.rwhile     : read X0 (todo stack); SI; write X1 (done stack)
# SI_run.rwhile : the same, wrapped so that the input is (todo . store) and
#                 the output (done . store) -- 10 extra steps, 5 either side.
set -e
mkdir -p extracted
cat > _ExtractSI.agda <<'EOF'
module _ExtractSI where
open import Data.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileSIShow using (showProg)
open import RWhileSISim using (SI)
t : showProg SI ≡ ""
t = refl
EOF
agda _ExtractSI.agda > _extract.log 2>&1 || true
python3 - <<'EOF'
import re
log = open('_extract.log').read()
m = re.search(r'"((?:[^"\\]|\\.)*)"\s*!=', log, re.S)
assert m, "could not find the normalised string in the type checker's output"
txt = m.group(1).encode().decode('unicode_escape')
open('extracted/SI.rwhile','w').write(txt)
pre  = "X2 ^= tl X0;\nX5 ^= hd X0;\nX0 ^= cons X5 X2;\nX0 ^= X5;\nX5 ^= X0;\n"
post = ";\nX5 ^= X1;\nX1 ^= X5;\nX1 ^= cons X5 X2;\nX5 ^= hd X1;\nX2 ^= tl X1"
body = txt[len("read X0;\n"):txt.rindex(";\nwrite X1")]
open('extracted/SI_run.rwhile','w').write("read X0;\n"+pre+body+post+";\nwrite X1\n")
print("extracted/SI.rwhile:", len(txt), "chars,", txt.count("\n"), "lines")
EOF
rm -f _ExtractSI.agda _ExtractSI.agdai _extract.log
