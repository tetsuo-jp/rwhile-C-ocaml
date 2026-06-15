#!/usr/bin/env bash
# Compile the verified interpreter (Extract.agda) to a native binary via Agda's
# GHC backend, demonstrating the "replace the implementation by extraction"
# route.  The same Agda code that carries the --safe reversibility proofs
# becomes ordinary runnable code.
#
# GHC needs the (boot, but hidden) `text` package exposed, and the linker needs
# libffi on its search path; we locate libffi in the common install dirs.
set -euo pipefail
cd "$(dirname "$0")"

ffi_dir=""
for d in /home/linuxbrew/.linuxbrew/lib /usr/lib/x86_64-linux-gnu /usr/lib /usr/local/lib; do
  if ls "$d"/libffi.so* >/dev/null 2>&1; then ffi_dir="$d"; break; fi
done

flags=(--compile --ghc-flag=-package --ghc-flag=text)
if [ -n "$ffi_dir" ]; then
  rpath_flag="--ghc-flag=-optl-Wl,-rpath,${ffi_dir}"
  flags+=("--ghc-flag=-L${ffi_dir}" "$rpath_flag")
fi

agda "${flags[@]}" Extract.agda
echo "Built ./Extract — run it with: ./Extract"
