# rwhile-C-OCaml

An R-WHILE interpreter in OCaml.

## Requirements

- OCaml
- `ocamlfind`
- `ocamlyacc`
- `extlib`
- `alcotest` (test suite only)
- BNFC — http://bnfc.digitalgrammars.com/ (the parser/pretty-printer files it
  generates are not checked in, so `make` invokes BNFC on a fresh checkout)

## Build

All commands below run from `src/`.

```bash
make
```

This builds the `ri` interpreter.

## Run

```bash
./ri <program.rwhile> <data.val>
./ri -inverse <program.rwhile>
./ri -exp <program.rwhile>
./ri -p2d <program.rwhile>
```

## Language note: symmetric `case`

Besides the core `if/fi` and `from/loop/until`, programs may use a symmetric,
reversible pattern match (always-on sugar, desugared to `if/fi`):

```
case Scrut yields Result of
    InPat1 => Body1 => OutPat1
  | InPat2 => Body2 => OutPat2
  | ...
end
```

Each arm reads `Scrut` into its input pattern, runs its body, and builds
`Result` from its output pattern. The entry test and exit assertion are
synthesised from each pattern's *discriminant*: its top shape (`cons` / `nil` /
`'atom`) or, for a pattern `cons 'tag P`, the head atom (tested by
`=? (hd v) 'tag`). The latter lets a `case` dispatch on a node's tag, e.g.

```
case PP yields PP of
    cons 'var A => ... => cons 'var A
  | cons 'cons C => ... => cons 'cons C
  | Rest => ... => Rest
end
```

For the result to stay reversible the **output** patterns must have
pairwise-disjoint discriminants, and every arm but the last must have a
concrete, disjoint **input** pattern (the last arm may be a variable catch-all).
See `examples/case_swap.rwhile` (top-shape) and `examples/case_tag.rwhile`
(head-atom); `./ri -exp` shows the `if/fi` expansion.

## Tests

```bash
make run-tests
```

The Alcotest suite covers store operations, expression evaluation, inversion,
macro expansion, program-to-data, full-program integration, and the
Futamura-projection / specialization tests for `examples/spec.rwhile` and
`examples/spec_av.rwhile`.

## Example setup on macOS

```bash
brew update
brew install ocaml opam
opam init
opam update
opam install extlib ocamlfind alcotest
cd src
make
make run-tests
```

`make` runs BNFC automatically to (re)generate the parser/pretty-printer files
from `src/Rwhile.cf` — there is no standalone `make bnfc` target; the generated
files are produced through the existing `BNFC_Util.ml` rule.
