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
