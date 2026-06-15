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
- `RWhileIL.agda` — **step (3)**: a reversible Intermediate Language with
  flat (list) sequencing, its own big-step semantics, a translation `trS`
  to R-WHILE proved **semantics-preserving** (`tr-soundS`/`tr-completeS`),
  and **IL reversibility** (`il-revS`). Demonstrates the layered-correctness
  architecture (prove in an efficient IL, transport via a verified
  translation).

## Checking

```
cd proofs/agda
for f in RWhileRev RWhileRevFull RWhileValStore RWhileDet RWhileDetConcrete RWhileIL; do
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

Next: extend the IL with loops; instantiate `rupdate` determinism without
`funext` via a first-order store; connect the IL to R-WHILE's pattern
replacement (`CRep`); and (broader plan) use the IL as the efficient layer in
which to prove further properties, transported to R-WHILE by the translation.
