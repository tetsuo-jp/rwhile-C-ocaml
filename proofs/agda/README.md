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

## Files

- `RWhileRev.agda` — core: atom / seq / cond.
- `RWhileRevFull.agda` — adds the reversible loop `CLoop`.

## Checking

```
cd proofs/agda
agda --safe RWhileRevFull.agda
```

Requires Agda + agda-stdlib (the `standard-library` library, as used by
`rev-alg-agda`).

## Scope / next steps

- The atomic step is abstract (a relation + its converse). A natural next
  layer instantiates it with R-WHILE's concrete value trees and `rupdate`,
  proving `rupdate`'s local invertibility, to obtain reversibility for the
  full language with pattern replacement.
- Determinism of `_⊢_⇒_` (given deterministic atoms) would upgrade the
  relational inverse to a function-level inverse `⟦inv c⟧ ∘ ⟦c⟧ = id`.
- This connects to the broader plan (an intermediate language proved
  correct, then a verified IL → R-WHILE translation).
