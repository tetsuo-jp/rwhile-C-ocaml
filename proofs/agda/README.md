# R-WHILE reversibility — machine-checked proofs (Agda)

A first formalisation of R-WHILE's central correctness property: for a
*reversible* language, "correct" means the syntactic program inversion
`inv` (`src/InvRwhile.ml`) really is the inverse of execution
(`src/EvalRwhile.ml`).

## What is proved

For the core reversible control constructs, modelled exactly as in the
interpreter, with an **abstract** store `S` and abstract tests `S → Bool`
and atomic reversible operations (so the results hold for *any* concrete
store / atoms — in particular R-WHILE's binary-tree value store and the
reversible XOR-update `rupdate`):

| construct        | model                              | inversion (matches `InvRwhile.ml`)        |
|------------------|------------------------------------|-------------------------------------------|
| `CRep` / `CAss`  | atomic relation `A : S → S → Set`  | converse relation `conv A`                |
| `CSeq c d`       | `c ⨾ d`                            | `inv d ⨾ inv c`                           |
| `CCond e c d f`  | `cond e c d f`                     | `cond f (inv c) (inv d) e`                |
| `CLoop e D L f`  | `loop e D L f`                     | `loop f (inv D) (inv L) e`                |

Big-step semantics `_⊢_⇒_` mirrors `EvalRwhile.ml`, including the exit
assertion of the conditional (`f` true after `then`, false after `else`)
and the loop's reversibility assertions (`e` true on entry, `e` false
after each loop body, `f` the exit test).

Theorems (all `--safe`, no postulates / holes / termination pragmas):

- **`inv-sound`**  `c ⊢ s ⇒ t → inv c ⊢ t ⇒ s` — running the inverted
  program backwards undoes the original.
- **`inv-inv`**  `inv (inv c) ≡ c` — inversion is a syntactic involution.
- **`inv-complete`**  `inv c ⊢ t ⇒ s → c ⊢ s ⇒ t` — the converse direction
  (corollary of the two above).

The loop case is the crux: inverting it reverses the whole iteration chain,
done by the accumulator induction `rev-rest`.

## Files (in dependency order)

- `RWhileRev.agda` — core reversibility: atom / seq / cond.
- `RWhileRevFull.agda` — adds the reversible loop `CLoop` (the crux).
- `RWhileValStore.agda` — **step (1)**: instantiate the abstract atom with
  R-WHILE's concrete value trees + the reversible XOR-update `rupdate`;
  prove `rupdate` is a partial involution (`RAss-sym`), hence the concrete
  assignment is reversible.
- `RWhileDet.agda` — **step (2)**: determinism of `_⊢_⇒_` (given
  deterministic atoms, collected by `Det⟨ c ⟩`) and the function-level
  inverse law `inv-cancels` (running `inv c` on c's output returns to start).
- `RWhileDetConcrete.agda` — **step (2), concrete**: `rupdate` is
  deterministic (`RAss-det`, under a `funext` hypothesis), so the concrete
  assignment's inverse cancels (`assign-inv-cancels`).
- `RWhileCRep.agda` — **pattern replacement** `CRep`: models pattern READ
  (`evalPat`) and WRITE (`inv_evalPat`) as independent relations, proves they
  are mutual converses (`read-write`/`write-read`), and concludes
  `inv (CRep q r) = CRep r q` is semantically the inverse (`crep-reversible`).
  Broadens the concrete model from `rupdate` alone to R-WHILE's other atomic
  reversible operation.
- `RWhileCRepDet.agda` — `CRep` in the determinism layer: pattern read/write
  are deterministic (`Read-det`/`Write-det`, under `funext`), hence `CRep` and
  its inverse are deterministic and the function-level inverse law holds for
  pattern replacement (`crep-inv-cancels`).
- `RWhileExec.agda` — **bridge to the implementation**: an EXECUTABLE
  functional interpreter `frun` (the form `evalCom` takes — atoms are partial
  functions, sequencing is Maybe-bind, the conditional checks its exit
  assertion), proved EQUIVALENT to the relational semantics
  (`frun-sound`/`frun-complete`: `frun p s ≡ just t ↔ compile p ⊢ s ⇒ t`).
  Corollary `frun-reversible`: the executable interpreter inherits
  reversibility. This certifies the interpreter *algorithm*, not just an
  abstract relation.
- `RWhileExecConcrete.agda` — removes the last abstraction: `rupdF`, the
  reversible XOR-update as ordinary executable code (`Store → Maybe Store`,
  mirroring `rupdate`), proved equivalent to the relational `RAss`
  (`rupdF-sound` without funext; `rupdF-complete` with funext). So the
  executable assignment `frun (fatom (rupdF x v))` computes exactly the
  reversible, deterministic semantics — no abstract atom left.
- `RWhileIL.agda` — **step (3)**: a reversible Intermediate Language with
  flat (list) sequencing, its own big-step semantics, a translation `trS`
  to R-WHILE proved **semantics-preserving** (`tr-soundS`/`tr-completeS`),
  and **IL reversibility** (`il-revS`). Demonstrates the layered-correctness
  architecture (prove in an efficient IL, transport via a verified
  translation).
- `RWhileCoreExp.agda` — reflects the implementation's Core IR
  expression/pattern NORMALIZATION (`src/Core.ml`: `norm_exp`/`norm_pat`/
  `eval_cexp`) and proves it semantics-preserving: `norm-correct`
  (`evalC σ (norm e) ≡ evalS σ e`) for expressions and `read-norm-correct`
  (`readC σ (normP p) ≡ readS σ p`) for patterns — desugaring list sugar to
  cons-chains keeps meaning. Certifies what the `core-ir` differential tests
  check empirically.

## Checking

```
cd proofs/agda
for f in RWhileRev RWhileRevFull RWhileValStore RWhileCRep RWhileCRepDet RWhileDet RWhileDetConcrete RWhileExec RWhileExecConcrete RWhileIL RWhileFutamura RWhileFutamura2 RWhileFutamura2Inst RWhileRevFutamura RWhileRevProjPaper RWhileRevProjInst RWhileRevProjGen RWhileCoreExp RWhileFp1Residual; do
  agda --safe $f.agda
done
```

Requires Agda + agda-stdlib (the `standard-library` library, as used by
`rev-alg-agda`).  All files are `--safe`: no postulates, holes, `TERMINATING`
pragmas, or `trustMe` (the only assumption is `funext`, taken as an explicit
module hypothesis in `RWhileDetConcrete`).

## Status / further work

Done: reversibility of `inv` (atom/seq/cond/loop); concrete `rupdate`
instantiation; determinism + function-level inverse; a verified flat-IL → R-WHILE
translation with IL reversibility.

## First Futamura projection (verified + extracted)

`RWhileFutamura.agda` (`--safe`) realises the **first Futamura projection** for
the small reversible op-language used in R-WHILE's fp1 (the `ri_seq`/swap
language): `mix` specialises the interpreter `int` to a source op-program,
producing a residual in which the interpretive dispatch is gone, and

```
fp1 : ∀ src p → run (mix src) p ≡ int src p
```

is proved.  `mix-length-≤` shows specialisation shrinks code.
`ExtractFutamura.agda` compiles `mix`/`int`/`run` to a native binary:

```
./build-extract.sh ExtractFutamura && ./ExtractFutamura
#  source program     [swap,id,swap,id]  (len 4)
#  compiled residual  [doSwap,doSwap]    (len 2)  -- dispatch & id removed
#  int src dat       = (nil , (nil.nil))
#  runC (mix src) dat = (nil , (nil.nil))         (equal, by the proved fp1)
```

So the interpreter→compiler transformation (fp1) is machine-checked AND runs
as an extracted native program.

## Futamura hierarchy fp2 / fp3 (modular)

`RWhileFutamura2.agda` (`--safe`) proves the **second and third** Futamura
projections modularly. With one universal type `U` and a specialiser
`spec : U → U → U`, the whole hierarchy follows from two facts:

- **H1** `spec-correct : run (spec p s) d ≡ run p ⟨ s , d ⟩` — the specialiser
  is correct (this is fp1 in general form; realised concretely by `mix` in
  `RWhileFutamura`).
- **H2** `spec-impl : run specP ⟨ p , s ⟩ ≡ spec p s` — the specialiser is
  itself a program `specP` (self-application).

Then `fp2 : run compiler src ≡ target src` and
`fp3 : run cogen p ≡ spec specP p` are each two `trans` steps.

`RWhileFutamura2Inst.agda` gives a **concrete, non-vacuous instance**: a
universal type `U` with a closure constructor `papp` (= `spec p s`) and a
program `mkpapp` (= `specP`) that builds it, so **both H1 and H2 hold by
`refl`** and fp1/fp2/fp3 hold for actual distinct programs (witnessed by
`compiler-is`, `fp2-example`, `fp3-example`). This shows a self-applicable
specialiser *exists* (here via a built-in closure constructor); doing it for
R-WHILE without built-in closures — residualising structurally — is the
engineering still open.

## Reversible Futamura projection

`RWhileRevFutamura.agda` (`--safe`) proves that the first Futamura projection
is *reversible*: specialising a reversible interpreter to a source yields a
reversible compiled program, and the projection commutes with inversion
(`invSrc`/`invComp` = reverse the sequence + invert each step):

- `mix-commute`    : `mix (invSrc src) ≡ invComp (mix src)`  — inversion
  commutes with the projection (compile-then-invert = invert-then-compile).
- `run-rev`        : `run (invComp cs) (run cs p) ≡ p`        — every compiled
  program is reversible.
- `int-rev`        : `int (invSrc src) (int src p) ≡ p`       — the interpreter
  is reversible.
- `reversible-fp1` : `run (mix (invSrc src)) (run (mix src) p) ≡ p` — combining
  the above: compiling the inverse source inverts the compiled program.

## Reversible projections of the IEICE 2025 paper (Okubo–Yokoyama)

A faithful Agda rendering of "2025_Reversible_Projection_IEICE_D" — a fourth
independent check beside the paper's Isabelle/HOL, Rocq and Lean developments.

- `RWhileRevProjPaper.agda` — the three reversible projections from the paper's
  assumptions `def-rint` (the reversible interpreter keeps the program in its
  output) and `def-spec` (the mix equation, with `rspec` itself a program):
  `rev-proj1/2/3` give `snd ∘ ⟦·⟧ ≡ ⟦src⟧_S` for `tgt''`, `comp''`, `cogen'`.
- `RWhileRevProjInst.agda` — a concrete, **executable** instance (closure ctor
  `papp`, specialiser-program `mkpapp`, program-preserving `rintP`); both
  hypotheses hold by `refl`. `ExtractRevProj.agda` compiles it to a native
  binary that **computes and runs the second reversible projection**:
  ```
  ./build-extract.sh ExtractRevProj && ./ExtractRevProj
  #  comp'' = run rspec (rspec.rint)  = papp(rspec,rint)
  #  target = comp''(swap)            = papp(rint,swap)
  #  target((*.(*.*)))                = (swap . ((*.*).*))   (program . result)
  #  snd                              = ((*.*).*) = srcSem swap data ✓
  ```
- `RWhileRevProjGen.agda` — the motivation and generalisations:
  - `proj1-needs-trivial` (paper Thm proj1_fail): a reversible interpreter that
    realises the source directly forces the source semantics to be injective
    (trivial) — so non-trivial sources need the reversible *projection* (rint).
  - general `proj` and arbitrary `srcSem` (covers **non-reversible source**):
    `GeneralRevProjection.rev-proj1/2/3` (`snd` is the special case).
  - **garbage dichotomy**: `garbage-necessary` — a reversible residual
    simulating a non-injective source forces `proj` to discard information;
    `input-preserving-inj` — keeping the input as garbage is always injective,
    so a reversible simulation exists for any source (rint⁺).

## Extraction demo (verified code → native binary)

`Extract.agda` imports the verified `rupdF` and compiles, via Agda's GHC
backend, to a native executable — demonstrating the "replace the
implementation by extraction" route: the *same* Agda code that carries the
`--safe` reversibility proofs is ordinary runnable code.

```
./build-extract.sh      # agda --compile (exposes the `text` pkg, finds libffi)
./Extract
#  V0 initially            = nil
#  V0 after  x ^= (nil.nil) = (nil . nil)
#  V0 after  toggling twice = nil      ← reversibility, at runtime
```

`Extract.agda` uses `--guardedness` (for IO) instead of `--safe`, but it only
*imports* and runs the `--safe`-checked `rupdF`; no proof is weakened.

## Honest scope (what is NOT yet proved)

These are results about an Agda **model** of R-WHILE's core, hand-written to
mirror the OCaml. `RWhileExec` closes part of the gap — it certifies the
interpreter *algorithm* (an executable functional interpreter equivalent to
the proven semantics) — but the *literal* OCaml is still not certified: the
Agda `frun` is hand-written to mirror `evalCom` rather than generated from it
(closing that fully needs extraction, or a verified parser + evaluator). Also
out of scope so far: the expression language
(`cons`/`hd`/`tl`/`=?`/`pair?`), macro expansion, parsing, `p2d`, the
`all_cleared` store invariant, and functional correctness / termination
(we prove *reversibility* and *determinism*, the properties that matter for a
reversible language).

Next: extend the IL with loops; instantiate determinism without `funext` via a
first-order store; and connect the model to the OCaml (extraction, or an
equivalence with a formal model of `eval`/`inv`) so the *implementation* — not
only the model — is certified.
