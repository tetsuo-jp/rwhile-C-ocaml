{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Bridge to the implementation: an EXECUTABLE functional interpreter
-- (the form `src/EvalRwhile.ml`'s `evalCom` takes) proved EQUIVALENT to the
-- relational big-step semantics that the reversibility/determinism theorems
-- are about.
--
-- `frun` mirrors evalCom: atoms are partial functions `S → Maybe S`,
-- sequencing is Maybe-bind, the reversible conditional evaluates the test
-- and checks the exit assertion (returning `nothing` on assertion failure,
-- exactly like the interpreter's error).  `compile` turns a functional
-- command into the relational Core command (an atom's relation is its graph).
--
-- Theorem (frun-sound / frun-complete):
--      frun p s ≡ just t   ↔   compile p ⊢ s ⇒ t
-- So the executable interpreter computes EXACTLY the relational semantics —
-- hence it inherits reversibility (RWhileRevFull.inv-sound) and determinism
-- (RWhileDet.det) on its results.
------------------------------------------------------------------------

module RWhileExec where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

import RWhileRevFull

module Exec (S : Set) where
  open RWhileRevFull.Core S

  ----------------------------------------------------------------------
  -- Functional commands (atoms are partial functions) and the executable
  -- interpreter `frun`, mirroring evalCom.

  data FCmd : Set where
    fatom : (S → Maybe S) → FCmd
    fseq  : FCmd → FCmd → FCmd
    fcond : (S → Bool) → FCmd → FCmd → (S → Bool) → FCmd

  frun : FCmd → S → Maybe S
  frun (fatom g)       s = g s
  frun (fseq c d)      s = frun c s >>= frun d
  frun (fcond e c d f) s =
    if e s then (frun c s >>= λ t → if f t then just t else nothing)
           else (frun d s >>= λ t → if f t then nothing else just t)

  ----------------------------------------------------------------------
  -- Compile a functional command to the relational Core command.

  graph : (S → Maybe S) → Rel
  graph g s t = g s ≡ just t

  compile : FCmd → Cmd
  compile (fatom g)       = atom (graph g)
  compile (fseq c d)      = compile c ⨾ compile d
  compile (fcond e c d f) = cond e (compile c) (compile d) f

  ----------------------------------------------------------------------
  -- SOUNDNESS: whatever frun computes is justified by the semantics.

  frun-sound : ∀ p {s t} → frun p s ≡ just t → compile p ⊢ s ⇒ t
  frun-sound (fatom g) h = e-atom h
  frun-sound (fseq c d) {s} h with frun c s in eqc | h
  ... | just m  | h′ = e-seq (frun-sound c eqc) (frun-sound d h′)
  ... | nothing | ()
  frun-sound (fcond e c d f) {s} h with e s in eqe | h
  ... | true  | h′ with frun c s in eqc | h′
  ...   | just m | h″ with f m in eqf | h″
  ...     | true | h‴ = e-then eqe (frun-sound-eq c eqc h‴) (f-eq eqf h‴)
        where
          frun-sound-eq : ∀ c′ {s′ m′ t′} → frun c′ s′ ≡ just m′ → just m′ ≡ just t′
                        → compile c′ ⊢ s′ ⇒ t′
          frun-sound-eq c′ e₁ refl = frun-sound c′ e₁
          f-eq : ∀ {m′ t′} → f m′ ≡ true → just m′ ≡ just t′ → f t′ ≡ true
          f-eq fe refl = fe
  frun-sound (fcond e c d f) {s} h | true  | h′ | just m | h″ | false | ()
  frun-sound (fcond e c d f) {s} h | true  | h′ | nothing | ()
  frun-sound (fcond e c d f) {s} h | false | h′ with frun d s in eqd | h′
  ...   | just m | h″ with f m in eqf | h″
  ...     | false | h‴ = e-else eqe (frun-sound-eq d eqd h‴) (f-eq eqf h‴)
        where
          frun-sound-eq : ∀ d′ {s′ m′ t′} → frun d′ s′ ≡ just m′ → just m′ ≡ just t′
                        → compile d′ ⊢ s′ ⇒ t′
          frun-sound-eq d′ e₁ refl = frun-sound d′ e₁
          f-eq : ∀ {m′ t′} → f m′ ≡ false → just m′ ≡ just t′ → f t′ ≡ false
          f-eq fe refl = fe
  frun-sound (fcond e c d f) {s} h | false | h′ | just m | h″ | true | ()
  frun-sound (fcond e c d f) {s} h | false | h′ | nothing | ()

  ----------------------------------------------------------------------
  -- COMPLETENESS: frun realises every derivation of the semantics.

  frun-complete : ∀ p {s t} → compile p ⊢ s ⇒ t → frun p s ≡ just t
  frun-complete (fatom g) (e-atom h) = h
  frun-complete (fseq c d) (e-seq cs ds)
    rewrite frun-complete c cs = frun-complete d ds
  frun-complete (fcond e c d f) (e-then es cs ft)
    rewrite es | frun-complete c cs | ft = refl
  frun-complete (fcond e c d f) (e-else es ds ft)
    rewrite es | frun-complete d ds | ft = refl

  ----------------------------------------------------------------------
  -- PAYOFF: the executable interpreter inherits reversibility — running the
  -- inverse program on frun's result returns to the start.  (Combine the
  -- soundness bridge with RWhileRevFull's inv-sound.)

  frun-reversible : ∀ p {s t} → frun p s ≡ just t → inv (compile p) ⊢ t ⇒ s
  frun-reversible p h = inv-sound (frun-sound p h)

------------------------------------------------------------------------
-- Worked examples (S = Bool): a concrete reversible toggle, run by frun,
-- justified by the relational semantics and reversed via frun-reversible.
-- Documentation + regression, checked by refl.

module Examples where
  open import Data.Bool using (Bool; true; false; not)
  open RWhileRevFull.Core Bool   -- relational _⊢_⇒_, inv
  open Exec Bool                  -- FCmd, frun, compile, frun-sound, frun-reversible

  -- a reversible toggle atom: negate the boolean state.
  toggle : FCmd
  toggle = fatom (λ b → just (not b))

  -- frun computes the negation, and running it twice is the identity.
  ex-toggle       : frun toggle true ≡ just false
  ex-toggle       = refl
  ex-toggle-twice : frun (fseq toggle toggle) true ≡ just true
  ex-toggle-twice = refl

  -- the executable result is justified by the relational semantics …
  ex-⇒ : compile toggle ⊢ true ⇒ false
  ex-⇒ = frun-sound toggle ex-toggle

  -- … and the inverse program returns to the start (concrete reversibility).
  ex-rev : inv (compile toggle) ⊢ false ⇒ true
  ex-rev = frun-reversible toggle ex-toggle
