# rwhile-C-OCaml

An interpreter for **R-WHILE** — a reversible structured programming language —
written in OCaml, together with a research platform for **reversible Futamura
projections** and their **machine-checked (Agda) metatheory**.

R-WHILE programs compute on binary trees (S-expressions) and are *reversible*:
every program has a syntactic inverse, the store starts and ends all-`nil`, and
assignment is a self-cancelling XOR update. On top of the interpreter this repo
contains a reversible self-interpreter, a reversible partial evaluator
(`spec_av`), the three reversible Futamura projections realised on the machine,
and 33 `--safe` Agda modules proving the core correctness properties.

## What's here

- **Interpreter** (`ri`) — evaluate, invert, macro-expand, and encode programs.
- **Reversible inversion** — `./ri -inverse` prints the inverse program.
- **Self-interpreter** — `examples/ri.rwhile`, a program-preserving reversible
  interpreter for R-WHILE written in R-WHILE.
- **Reversible specializer** — `examples/spec_av.rwhile`, a partial evaluator
  over *annotated values* (static / dynamic / partially-static), used to realise
  the reversible Futamura projections (see [FUTAMURA.md](FUTAMURA.md)).
- **Machine-checked proofs** — `proofs/agda/` (see
  [AGDA_CORRESPONDENCE.md](AGDA_CORRESPONDENCE.md)).

## Requirements

- OCaml + `ocamlfind`, `ocamlyacc`, `extlib`
- `alcotest` (test suite only)
- **BNFC** — http://bnfc.digitalgrammars.com/ — the parser/pretty-printer files
  it generates are **not** checked in, so `make` invokes BNFC on a fresh
  checkout. (For the Agda proofs: Agda + `standard-library`.)

## Build & run

All commands run from `src/`.

```bash
make                 # build the ri interpreter (runs BNFC automatically)
make run-tests       # build and run the Alcotest suite
make install         # copy ri into ../web/
```

```bash
./ri <program.rwhile> <data.val>     # evaluate
./ri -inverse <program.rwhile>       # print the inverted program
./ri -exp <program.rwhile>           # print the macro-expanded program
./ri -p2d <program.rwhile>           # encode a program as an R-WHILE value
./ri -core <program> <data>          # evaluate via the Core IR (src/Core.ml)
./ri -hygienic-macros <program> <data>   # alpha-rename macro-internal locals
./ri -llm-errors <program> <data>        # structured, machine-friendly errors
./ri -simp -copyprop <program> [data]    # optimise: fold constants, drop dead
                                         #   reversible branches, fuse
                                         #   write-once/read-once moves
./ri -steps -work <program> <data>       # cost meters: command nodes executed,
                                         #   and value nodes examined by
                                         #   comparison (the cost -steps misses)
```

Helper tools (also from `src/`):

```bash
make d2p             # build d2p: decode / directly evaluate a program-as-data residual
make specsize        # build specsize: resize spec_av's store (FpN/TmpT) to a subject
```

## Language overview

- **Values** are binary trees: `nil`, atoms `'a`, and cons `(x.y)`.
- **Reversible assignment** `x ^= e` is an XOR update: assigning the current
  value clears it, assigning to `nil` sets it. The store invariant is that all
  variables are `nil` at entry and exit.
- **Pattern replacement** `p <= q` reads `q` into a value and writes it through
  pattern `p`; fully reversible.
- **Conditional** `if e then … else … fi f`: `e` is the entry test, `f` the exit
  assertion (they swap under inversion).
- **Loop** `from e do … loop … until f` with entry/exit reversibility tests.
- **Macros** `macro NAME(args) … end`, auto-inverted as `INV-NAME`. Local-name
  sharing across a macro and its inverse is intentional; `-hygienic-macros` opts
  into per-call-site alpha-renaming. See [HYGIENIC_MACROS.md](HYGIENIC_MACROS.md).
- **Expressions**: `cons`, `hd`, `tl`, `=?`, and `pair? E` (cons test).

### Symmetric `case` (reversible pattern match)

Besides `if/fi` and `from/loop/until`, programs may use a symmetric, reversible
pattern match — always-on sugar, desugared to `if/fi` *before* evaluation,
inversion and program-encoding (so the self-interpreter and `spec_av` need no
change):

```
case Scrut yields Result of
    InPat1 => Body1 => OutPat1
  | InPat2 => Body2 => OutPat2
  | ...
end
```

Each arm reads `Scrut` into its input pattern, runs its body, and builds
`Result` from its output pattern. Entry test and exit assertion are synthesised
from each pattern's *discriminant*: its top shape (`cons` / `nil` / `'atom`) or,
for a pattern `cons 'tag P`, the head atom (`=? (hd v) 'tag`) — so a `case` can
dispatch on a node's tag. For reversibility the **output** patterns must have
pairwise-disjoint discriminants, and every arm but the last must have a
concrete, disjoint **input** pattern (the last may be a variable catch-all). See
`examples/case_swap.rwhile`, `examples/case_tag.rwhile`; `./ri -exp` shows the
`if/fi` expansion.

### Structured sugar

Seven further surface forms are desugared in the same pass, so they too are
invisible to macro expansion, evaluation, inversion and program-encoding:

| Surface form | Expands to |
| --- | --- |
| `skip` | `if 't fi 't` (a no-op that still costs one step) |
| `assert E` | `if E fi 't` — fails at run time when `E` is false |
| `X <-> Y` | `cons X Y <= cons Y X` |
| `local X = E in C delocal X = F end` | `assert (=? X nil); X ^= E; C; X ^= F; assert (=? X nil)` |
| `for X = A to B do C end` | `assert (=? X nil); X ^= A; from =? X A do C loop <X++> until =? X B; X ^= B; assert (=? X nil)` |
| `push X S` | `S <= cons X S` (`X` is left `nil`) |
| `pop X S` | `cons X S <= S` (fails if `S` is not a cons) |

`push` and `pop` are exact inverses with no inversion rule of their own —
inverting a replacement swaps its two patterns, which turns one into the other.
Their two variables must differ. `local`/`delocal` must name the same variable
(checked), and neither the body nor the bounds of a `for` may mention the loop
counter (also checked). Both were silent failure modes: a body that touches the
counter makes the loop's own tests see a changed value and run a different
number of times, and `for I = nil to I` has the trivially-true exit test
`=? I I`, so it ran the body exactly once however it was written.

The two `assert (=? X nil)` guards are load-bearing, not decoration: `X ^= E` is
an XOR update, not a binding, so when `X` already holds `E`'s value it *clears*
`X` instead of setting it — the body would then run with `X = nil` and the
closing assignment would restore the old value, giving a wrong answer with no
error. The exit guard rules out the mirror case, where the body has cleared `X`
and the closing assignment sets it. They also keep the desugaring self-dual:
inverting it yields `local X = F in inv C delocal X = E end`, guards included.

The `for` counter is
loop-**local** — `nil` before and after — so a `for` preserves the store
invariant; `A` and `B` are unary numerals (`nil`, `(nil.nil)`, …), the body runs
at least once, and `B` must be `A` extended by `nil`s or the loop diverges, just
as the underlying `from/until` does. The counter step `<X++>` is the
four-assignment reversible increment used by the verified interpreter
(`proofs/agda/RWhileSIMac.incC`); the scratch variable it needs is named with a
prefix chosen per program, so it cannot collide with an identifier the program
already uses. See `examples/sugar.rwhile` and
`examples/stack_reverse.rwhile`; `./ri -exp` shows the expansion and
`./ri -inverse` the (cost-identical) inverse.

All of these are keywords in lower case, and identifiers must start with an
upper-case letter, so none of them can shadow an existing variable or macro
name.

The surface language (this sugar plus what comes next) is **R-WHILE-S**; the
core stays frozen so the self-interpreter, the specialiser and the Agda
development are untouched. The first optimisation pass of the
R-WHILE-S → R-WHILE compiler is **on by default**: `./ri -p2d` numbers variables
by static access weight rather than first occurrence. A variable's number is a
unary numeral in the encoding, so this halves the encoded program (`spec_av`
817701 → 399565 nodes) and the fp2 compiler with it (812515 → 386681), and makes
the test suite run 3.5× faster (125 s → 36 s) — with fp1, fp2 and fp3 all still
holding. `./ri -p2d -first-occurrence-vars` restores the old numbering. See
[RWHILE_S.md](RWHILE_S.md) for the architecture and for which optimisations
survive compilation and which do not.

## Reversible Futamura projections

For a reversible language the ordinary Futamura projections fail (a reversible
interpreter realising the source directly exists only when the source is
trivial). The fix is a **program-preserving reversible interpreter** `rint`
(it keeps the source program in the output as garbage; a projection recovers the
result) plus a **reversible specializer** `rspec`. This repo realises all three
projections on the machine, with judgement made by *direct evaluation* of the
program-as-data residual (`make d2p`):

- **fp1** `target = [rspec](rint, src)` — runs end-to-end on the minimal
  interpreter; the residual is smaller than the interpreter (specialization
  genuinely fires).
- **fp2** `compiler = [rspec](rspec, rint)` and **fp3**
  `cogen = [rspec](rspec, rspec)` — byte-equal residuals on `ri_min`.

`rspec` (the `spec_av` annotated-value evaluator) is the *trivial* specializer
in the sense of Jones — it embeds and freezes rather than optimising — so the
self-application is near-trivial (comp2 ≈ 1×|rspec|). Building an *optimising*
reversible specializer is open. See [FUTAMURA.md](FUTAMURA.md),
[FINDINGS_reversible_projections.md](FINDINGS_reversible_projections.md) (garbage
minimisation, −57%), and [HANDOFF_fp2.md](HANDOFF_fp2.md).

## Machine-checked proofs (Agda)

`proofs/agda/` contains 33 `--safe` modules (no postulates beyond one `funext`),
modelling the interpreter / inverter / specializer algorithms. Highlights (full
inventory in [proofs/agda/README.md](proofs/agda/README.md) and
[AGDA_CORRESPONDENCE.md](AGDA_CORRESPONDENCE.md)):

- **Inversion is the inverse of execution** — `inv-sound` / `inv-inv` /
  `inv-complete`; reversible XOR-assignment and pattern-replacement reversibility.
- **Surface → Core translation** is meaning-preserving; **hygienic macro
  expansion** is sound; **`case`** desugaring preserves reversibility.
- **Reversible fp1 (mix)** and the **modular fp2/fp3** theorems.
- **AV algebra soundness** and the **real-AV spec-correct (H1)**:
  `⟦spec p s⟧ d ≡ ⟦p⟧ (s·d)`.
- **`program2data` / `data2program` round-trip** (`d2p∘p2d ≡ id`), and a
  **unified value-type fp1** for the real AV specializer.
- **H2's recursive core, non-closure** (`RWhileH2.self-rep`: the symbolic
  evaluator is a genuine data program under a uniform total interpreter), and a
  **full total non-closure hierarchy instance** (`RWhileH2Hier`) where
  fp1/fp2/fp3 hold as proven theorems with real, inspectable residuals.
- **Quantitative garbage lower bound** `|garbage| ≥ |fiber|` (Landauer/Bennett).

Closing the *full* self-application H2 for the looping specializer needs a
fuel-indexed model (totality obstruction under `--safe`); this is documented
future work.

```bash
cd proofs/agda
agda --safe RWhileH2Hier.agda      # (typechecks its dependencies too)
```

## Tests

```bash
make run-tests
```

The Alcotest suite covers store operations, expression evaluation, inversion,
macro expansion, program-to-data, full-program integration, Core-IR equivalence,
and the Futamura-projection / specialization tests for `examples/spec_av.rwhile`
(and the legacy `examples/spec.rwhile`). Run a single group by passing its name
to `./test-suite`; run the whole suite under hygienic macros with
`RWHILE_HYGIENIC=1 ./test-suite`.

## Documentation index

| File | Contents |
|------|----------|
| [CLAUDE.md](CLAUDE.md) | Architecture, build/run, language semantics (developer guide) |
| [FUTAMURA.md](FUTAMURA.md) | The reversible Futamura projections |
| [FINDINGS_reversible_projections.md](FINDINGS_reversible_projections.md) | Empirical results, garbage minimisation |
| [AGDA_CORRESPONDENCE.md](AGDA_CORRESPONDENCE.md) | Agda ↔ implementation map, gaps, status |
| [proofs/agda/README.md](proofs/agda/README.md) | Per-module description of the proofs |
| [HYGIENIC_MACROS.md](HYGIENIC_MACROS.md) | Macro hygiene policy |
| [RELATED_WORK.md](RELATED_WORK.md) | Novelty positioning |

## Example setup on macOS

```bash
brew update
brew install ocaml opam
opam init && opam update
opam install extlib ocamlfind alcotest
cd src
make
make run-tests
```

`make` runs BNFC automatically to (re)generate the parser/pretty-printer files
from `src/Rwhile.cf`; there is no standalone `make bnfc` target.
