{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Step (2): determinism of R-WHILE execution, and the function-level
-- inverse law.
--
-- The big-step relation `_⊢_⇒_` is deterministic provided each atomic
-- operation is.  `Det⟨ c ⟩` collects exactly the per-atom determinism
-- evidence appearing in c (so the theorem applies to any concrete atoms the
-- caller can show deterministic, e.g. RWhileValStore's `rupdate`).
--
-- Combined with `inv-sound` (RWhileRevFull) this yields the function-level
-- inverse law `inv-cancels`: running `inv c` on the result of `c` returns to
-- the start — i.e. ⟦inv c⟧ ∘ ⟦c⟧ = id wherever ⟦c⟧ is defined.
------------------------------------------------------------------------

module RWhileDet where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

import RWhileRevFull

module Det (S : Set) where
  open RWhileRevFull.Core S

  -- Determinism evidence: every atom occurring in c is a deterministic relation.
  Det⟨_⟩ : Cmd → Set
  Det⟨ atom A ⟩       = ∀ {s t t'} → A s t → A s t' → t ≡ t'
  Det⟨ c ⨾ d ⟩        = Det⟨ c ⟩ × Det⟨ d ⟩
  Det⟨ cond e c d f ⟩ = Det⟨ c ⟩ × Det⟨ d ⟩
  Det⟨ loop e D L f ⟩ = Det⟨ D ⟩ × Det⟨ L ⟩

  private
    t≢f : true ≡ false → ⊥
    t≢f ()

  ------------------------------------------------------------------------
  -- Determinism (mutually with determinism of the loop's iteration chain).

  det      : ∀ {c} → Det⟨ c ⟩ → ∀ {s t t'} → c ⊢ s ⇒ t → c ⊢ s ⇒ t' → t ≡ t'
  rest-det : ∀ {e D L f} → Det⟨ D ⟩ → Det⟨ L ⟩
           → ∀ {w u u'} → Rest e D L f w u → Rest e D L f w u' → u ≡ u'

  det dc (e-atom a) (e-atom a') = dc a a'
  det (dc , dd) (e-seq cs ds) (e-seq cs' ds') with det dc cs cs'
  ... | refl = det dd ds ds'
  det (dc , dd) (e-then _ cs _) (e-then _ cs' _)  = det dc cs cs'
  det (dc , dd) (e-then es _ _) (e-else es' _ _)  = ⊥-elim (t≢f (trans (sym es) es'))
  det (dc , dd) (e-else es _ _) (e-then es' _ _)  = ⊥-elim (t≢f (trans (sym es') es))
  det (dc , dd) (e-else _ ds _) (e-else _ ds' _)  = det dd ds ds'
  det (dD , dL) (e-loop _ Dst rest) (e-loop _ Dst' rest') with det dD Dst Dst'
  ... | refl = rest-det dD dL rest rest'

  rest-det dD dL (r-exit _)   (r-exit _)            = refl
  rest-det dD dL (r-exit fw)  (r-iter fw' _ _ _ _)  = ⊥-elim (t≢f (trans (sym fw) fw'))
  rest-det dD dL (r-iter fw _ _ _ _) (r-exit fw')   = ⊥-elim (t≢f (trans (sym fw') fw))
  rest-det dD dL (r-iter _ Lwa _ Dab restb) (r-iter _ Lwa' _ Da'b' restb')
    with det dL Lwa Lwa'
  ... | refl with det dD Dab Da'b'
  ...   | refl = rest-det dD dL restb restb'

  ------------------------------------------------------------------------
  -- Function-level inverse law: running `inv c` on c's output returns to the
  -- start.  Needs only that inv c's atoms are deterministic (Det⟨ inv c ⟩),
  -- which holds when the atoms are reversible (their converses are functions).

  inv-cancels : ∀ {c s t t'} → Det⟨ inv c ⟩ → c ⊢ s ⇒ t → inv c ⊢ t ⇒ t' → t' ≡ s
  inv-cancels dInvC fwd back = det dInvC back (inv-sound fwd)

------------------------------------------------------------------------
-- Worked examples (S = Bool): a deterministic atom, determinism evidence for
-- a small program, and uniqueness of its result.  Documentation + regression.

module Examples where
  open import Data.Bool using (Bool; true; false; not)
  open import Data.Product using (_,_)
  open RWhileRevFull.Core Bool
  open Det Bool

  -- the graph of boolean negation, and its determinism.
  Neg : Rel
  Neg s t = t ≡ not s

  neg-det : ∀ {s t t'} → Neg s t → Neg s t' → t ≡ t'
  neg-det p q = trans p (sym q)

  -- a small program and its per-atom determinism evidence.
  prog : Cmd
  prog = atom Neg ⨾ atom Neg

  prog-det : Det⟨ prog ⟩
  prog-det = neg-det , neg-det

  -- the only result of prog on true is true (uniqueness via det).
  d-true : prog ⊢ true ⇒ true
  d-true = e-seq (e-atom refl) (e-atom refl)

  ex-unique : ∀ {t} → prog ⊢ true ⇒ t → t ≡ true
  ex-unique d = det prog-det d d-true
