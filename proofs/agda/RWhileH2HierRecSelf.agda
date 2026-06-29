{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- 選択肢2 (option 2): lift RWhileRevProj2Self's OPTIMISING property — the
-- residual ELIMINATES the interpreter and USES its runtime input (no over-static
-- degeneration) — into the recursion-capable big-step relation of
-- RWhileH2HierRec.
--
-- RWhileRevProj2Self proved fp1/fp2/fp3 (and `compiler-residual-uses-input`)
-- with a hard-coded total `run`; here the same optimising guarantee is shown in
-- the inductive `_·_⇓_` relation, where compilation is GENUINE RECURSION over the
-- source op-list (closer to the real spec_av's structure).
--
-- An op-list interpreter is  foldOps ops d = apply oₙ (… (apply o₁ d)).  Its
-- residual for a STATIC ops is a direct chain of the per-op programs applied to
-- the DYNAMIC input — built by recursion on ops.  Composition g∘f is expressed
-- in the Tm language as  ap (quo g) f  (⇓ap runs g · (f · x)).  The residual
-- contains NO dispatch/fold over ops at runtime (interpreter eliminated) yet,
-- for EVERY runtime input d, computes the interpreter's result (uses its input).
--
-- `--safe`, no postulates/holes.
------------------------------------------------------------------------

module RWhileH2HierRecSelf where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import RWhileH2HierRec
  using (Tm; nv; cn; inp; car; cdr; quo; ap; _·_⇓_; ⇓inp; ⇓quo; ⇓ap; ⇓cn)

------------------------------------------------------------------------
-- Parametrised by an op alphabet, its meta-level action `apply`, a Tm program
-- `opTm` implementing each op, and the proof that `opTm o` computes `apply o` on
-- ANY input (so each op program is itself input-dependent, never baked).

module Core (Op : Set) (apply : Op → Tm → Tm)
            (opTm : Op → Tm)
            (op-runs : ∀ o d → opTm o · d ⇓ apply o d) where

  -- the interpreter's meaning: left-to-right fold of the ops over the data.
  foldOps : List Op → Tm → Tm
  foldOps []       d = d
  foldOps (o ∷ os) d = foldOps os (apply o d)

  -- the COMPILED residual: a direct ap-chain of the op programs (g∘f = ap (quo g) f).
  -- []  ↦ identity program `inp`;  (o ∷ os) ↦ run `compileOps os` after `opTm o`.
  compileOps : List Op → Tm
  compileOps []       = inp
  compileOps (o ∷ os) = ap (quo (compileOps os)) (opTm o)

  -- OPTIMISING correctness (the lift): the residual eliminates the interpreter —
  -- it is a fixed ap-chain with no runtime dispatch over `ops` — yet for EVERY
  -- runtime input d it equals the interpreter's result foldOps ops d.  The proof
  -- recurses on ops (genuine recursion), unlike RevProj2Self's hard-coded run.
  compileOps-correct : ∀ ops d → compileOps ops · d ⇓ foldOps ops d
  compileOps-correct []       d = ⇓inp d
  compileOps-correct (o ∷ os) d =
    ⇓ap (⇓quo (compileOps os) d) (op-runs o d) (compileOps-correct os (apply o d))

------------------------------------------------------------------------
-- Non-vacuous witness: a single total op `dup` (d ↦ cn d d).  The compiled
-- residual of a static op-list runs on a symbolic input and computes the fold —
-- a concrete machine-checked instance of the optimising residual.

module Witness where
  open import Data.Unit using (⊤; tt)

  -- dup as a Tm program: cn inp inp, total (works on every input).
  open Core ⊤ (λ _ d → cn d d) (λ _ → cn inp inp)
            (λ _ d → ⇓cn (⇓inp d) (⇓inp d)) public

  -- compiling [dup, dup] and running on nv yields cn (cn nv nv) (cn nv nv).
  ex : compileOps (tt ∷ tt ∷ []) · nv ⇓ cn (cn nv nv) (cn nv nv)
  ex = compileOps-correct (tt ∷ tt ∷ []) nv

------------------------------------------------------------------------
-- Witness2: a DIFFERENT total op (prepend nv: d ↦ cn nv d) and the OPTIMISING /
-- uses-input property made concrete -- the SAME compiled residual runs correctly
-- on two DISTINCT runtime inputs (the answer is not baked in), and the empty
-- op-list compiles to the identity residual `inp`.

module Witness2 where
  open import Data.Unit using (⊤; tt)

  -- prepend-nv as a Tm program: cn (quo nv) inp, total on every input.
  open Core ⊤ (λ _ d → cn nv d) (λ _ → cn (quo nv) inp)
            (λ _ d → ⇓cn (⇓quo nv d) (⇓inp d)) public

  -- the residual uses its input: one compiled program, two distinct inputs.
  ex-nv : compileOps (tt ∷ []) · nv ⇓ cn nv nv
  ex-nv = compileOps-correct (tt ∷ []) nv
  ex-cn : compileOps (tt ∷ []) · (cn nv nv) ⇓ cn nv (cn nv nv)
  ex-cn = compileOps-correct (tt ∷ []) (cn nv nv)

  -- the empty op-list compiles to the identity residual.
  ex-id : compileOps [] · nv ⇓ nv
  ex-id = compileOps-correct [] nv
