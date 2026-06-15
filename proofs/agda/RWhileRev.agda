------------------------------------------------------------------------
-- R-WHILE reversibility, formalised in Agda.
--
-- Claim being proved ("R-WHILE is correct" in the sense that matters for a
-- *reversible* language): the syntactic program inversion `inv`
-- (src/InvRwhile.ml) is semantically the inverse of execution
-- (src/EvalRwhile.ml).  Concretely:
--
--      c ⊢ s ⇒ t   →   inv c ⊢ t ⇒ s          (inv-sound)
--      inv (inv c) ≡ c                          (inv-inv)
--      inv c ⊢ t ⇒ s   →   c ⊢ s ⇒ t           (inv-complete, a corollary)
--
-- The control constructs are modelled EXACTLY as in the interpreter:
--   * atomic reversible step  (CRep p q / CAss x e): an abstract relation
--     `A : S → S → Set`.  Its inverse is the converse relation `conv A`.
--     This captures both `CRep (p,q) ↦ CRep (q,p)` and the self-inverse
--     `CAss` — in each case running the inverted atom backwards is exactly
--     running the original atom's converse.
--   * sequencing      CSeq c d        , inv = CSeq (inv d) (inv c)
--   * reversible if    CCond e c d f   , inv = CCond f (inv c) (inv d) e
--        eval: if e then c, asserting f TRUE  afterwards
--              else    d, asserting f FALSE afterwards
--
-- The store S and the tests S → Bool are abstract, so the theorem holds for
-- ANY concrete store and atomic operations — in particular R-WHILE's
-- binary-tree value store with the reversible XOR-update `rupdate`.
--
-- (The reversible loop CLoop is treated in RWhileRevLoop.agda.)
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module RWhileRev where

open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; subst)

module Core (S : Set) where

  -- An atomic reversible operation is a binary relation on stores.
  Rel : Set₁
  Rel = S → S → Set

  -- The converse relation = the inverse of an atomic step.
  conv : Rel → Rel
  conv A = λ s t → A t s

  ------------------------------------------------------------------------
  -- Syntax (core reversible control)

  data Cmd : Set₁ where
    atom : Rel → Cmd                                  -- CRep / CAss
    _⨾_  : Cmd → Cmd → Cmd                            -- CSeq
    cond : (S → Bool) → Cmd → Cmd → (S → Bool) → Cmd  -- CCond e c d f

  infixr 5 _⨾_

  ------------------------------------------------------------------------
  -- Syntactic inversion (mirrors src/InvRwhile.ml exactly)

  inv : Cmd → Cmd
  inv (atom A)       = atom (conv A)
  inv (c ⨾ d)        = inv d ⨾ inv c
  inv (cond e c d f) = cond f (inv c) (inv d) e

  ------------------------------------------------------------------------
  -- Big-step operational semantics (mirrors src/EvalRwhile.ml).
  --   c ⊢ s ⇒ t  :  running c in store s yields store t.

  infix 3 _⊢_⇒_
  data _⊢_⇒_ : Cmd → S → S → Set₁ where

    e-atom : ∀ {A s t} → A s t → atom A ⊢ s ⇒ t

    e-seq  : ∀ {c d s t u} → c ⊢ s ⇒ t → d ⊢ t ⇒ u → (c ⨾ d) ⊢ s ⇒ u

    -- then-branch: test e holds, run c, the exit assertion f must hold
    e-then : ∀ {e c d f s t}
           → e s ≡ true  → c ⊢ s ⇒ t → f t ≡ true
           → cond e c d f ⊢ s ⇒ t

    -- else-branch: test e fails, run d, the exit assertion f must fail
    e-else : ∀ {e c d f s t}
           → e s ≡ false → d ⊢ s ⇒ t → f t ≡ false
           → cond e c d f ⊢ s ⇒ t

  ------------------------------------------------------------------------
  -- MAIN THEOREM: inversion is sound — inv c computes the inverse relation.

  inv-sound : ∀ {c s t} → c ⊢ s ⇒ t → inv c ⊢ t ⇒ s
  inv-sound (e-atom a)        = e-atom a
  inv-sound (e-seq cs ds)     = e-seq (inv-sound ds) (inv-sound cs)
  inv-sound (e-then es cs ft) = e-then ft (inv-sound cs) es
  inv-sound (e-else es ds ft) = e-else ft (inv-sound ds) es

  ------------------------------------------------------------------------
  -- inv is a syntactic involution.

  inv-inv : ∀ c → inv (inv c) ≡ c
  inv-inv (atom A)       = refl
  inv-inv (c ⨾ d)        = cong₂ _⨾_ (inv-inv c) (inv-inv d)
  inv-inv (cond e c d f) = cong₂ (λ x y → cond e x y f) (inv-inv c) (inv-inv d)

  ------------------------------------------------------------------------
  -- Corollary: the reverse direction (full reversibility).

  inv-complete : ∀ {c s t} → inv c ⊢ t ⇒ s → c ⊢ s ⇒ t
  inv-complete {c} {s} {t} d = subst (λ x → x ⊢ s ⇒ t) (inv-inv c) (inv-sound d)
