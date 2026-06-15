------------------------------------------------------------------------
-- R-WHILE reversibility (FULL core, including the reversible loop).
--
-- Extends RWhileRev with CLoop and proves the same headline theorem:
--      c ⊢ s ⇒ t   →   inv c ⊢ t ⇒ s          (inv-sound)
-- for atomic ops, sequencing, the reversible conditional AND the
-- reversible loop, modelled exactly as in src/EvalRwhile.ml /
-- src/InvRwhile.ml:
--
--   CLoop e D L f   "from e do D loop L until f"
--     eval: assert e TRUE; run D; then repeat:
--             if f holds -> stop;
--             else run L, assert e FALSE, run D, repeat.
--     inv : CLoop f (inv D) (inv L) e   (entry/exit tests swapped).
--
-- The loop case is the crux of reversibility: inverting it requires
-- reversing the whole iteration chain, done here by an accumulator
-- induction (rev-rest).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}
module RWhileRevFull where

open import Data.Bool using (Bool; true; false)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong₂; subst)

module Core (S : Set) where

  Rel : Set₁
  Rel = S → S → Set

  conv : Rel → Rel
  conv A = λ s t → A t s

  ------------------------------------------------------------------------
  -- Syntax

  data Cmd : Set₁ where
    atom : Rel → Cmd
    _⨾_  : Cmd → Cmd → Cmd
    cond : (S → Bool) → Cmd → Cmd → (S → Bool) → Cmd
    loop : (S → Bool) → Cmd → Cmd → (S → Bool) → Cmd   -- from e do D loop L until f

  infixr 5 _⨾_

  ------------------------------------------------------------------------
  -- Syntactic inversion (mirrors src/InvRwhile.ml)

  inv : Cmd → Cmd
  inv (atom A)       = atom (conv A)
  inv (c ⨾ d)        = inv d ⨾ inv c
  inv (cond e c d f) = cond f (inv c) (inv d) e
  inv (loop e D L f) = loop f (inv D) (inv L) e

  ------------------------------------------------------------------------
  -- Big-step semantics.  The loop uses an auxiliary "rest" relation:
  --   Rest e D L f w x  :  starting just after a D, at store w, iterate the
  --   "until f" loop, ending in store x.

  infix 3 _⊢_⇒_

  data _⊢_⇒_ : Cmd → S → S → Set₁
  data Rest (e : S → Bool) (D L : Cmd) (f : S → Bool) : S → S → Set₁

  data _⊢_⇒_ where
    e-atom : ∀ {A s t} → A s t → atom A ⊢ s ⇒ t
    e-seq  : ∀ {c d s t u} → c ⊢ s ⇒ t → d ⊢ t ⇒ u → (c ⨾ d) ⊢ s ⇒ u
    e-then : ∀ {e c d f s t}
           → e s ≡ true  → c ⊢ s ⇒ t → f t ≡ true  → cond e c d f ⊢ s ⇒ t
    e-else : ∀ {e c d f s t}
           → e s ≡ false → d ⊢ s ⇒ t → f t ≡ false → cond e c d f ⊢ s ⇒ t
    e-loop : ∀ {e D L f s t u}
           → e s ≡ true → D ⊢ s ⇒ t → Rest e D L f t u → loop e D L f ⊢ s ⇒ u

  data Rest e D L f where
    -- exit: the until-test f holds, stop here
    r-exit : ∀ {w} → f w ≡ true → Rest e D L f w w
    -- iterate: f fails, run L, the entry test e must be FALSE, run D, recurse
    r-iter : ∀ {w u v x}
           → f w ≡ false → L ⊢ w ⇒ u → e u ≡ false → D ⊢ u ⇒ v
           → Rest e D L f v x → Rest e D L f w x

  ------------------------------------------------------------------------
  -- MAIN THEOREM (with loop): inversion is sound.
  -- inv-sound and the chain-reversal rev-rest are mutually recursive.

  inv-sound : ∀ {c s t} → c ⊢ s ⇒ t → inv c ⊢ t ⇒ s

  -- rev-rest reverses a forward iteration chain into the inverse loop's rest,
  -- accumulating the already-built inverse rest (from q back to s).
  rev-rest : ∀ {e D L f s t u}
           → Rest e D L f t u
           → ∀ {q} → inv D ⊢ t ⇒ q → Rest f (inv D) (inv L) e q s
           → Σ[ m ∈ S ] (f u ≡ true) × (inv D ⊢ u ⇒ m) × Rest f (inv D) (inv L) e m s

  inv-sound (e-atom a)        = e-atom a
  inv-sound (e-seq cs ds)     = e-seq (inv-sound ds) (inv-sound cs)
  inv-sound (e-then es cs ft) = e-then ft (inv-sound cs) es
  inv-sound (e-else es ds ft) = e-else ft (inv-sound ds) es
  inv-sound (e-loop {e} {D} {L} {f} {s} es Dst rest)
    with rev-rest rest (inv-sound Dst) (r-exit es)
  ... | (m , fu , invDum , revrest) = e-loop fu invDum revrest

  -- base: forward rest exits at w=u; the accumulator IS the inverse rest to s.
  rev-rest (r-exit fw) {q} invDtq acc = (q , fw , invDtq , acc)
  -- step: prepend this iteration (reversed) to the accumulator, then recurse.
  rev-rest (r-iter fw Lwu eu Duv rest1) invDtq acc =
    rev-rest rest1 (inv-sound Duv)
      (r-iter eu (inv-sound Lwu) fw invDtq acc)

  ------------------------------------------------------------------------
  -- inv is a syntactic involution.

  inv-inv : ∀ c → inv (inv c) ≡ c
  inv-inv (atom A)       = refl
  inv-inv (c ⨾ d)        = cong₂ _⨾_ (inv-inv c) (inv-inv d)
  inv-inv (cond e c d f) = cong₂ (λ x y → cond e x y f) (inv-inv c) (inv-inv d)
  inv-inv (loop e D L f) = cong₂ (λ x y → loop e x y f) (inv-inv D) (inv-inv L)

  ------------------------------------------------------------------------
  -- Corollary: full reversibility (the reverse direction).

  inv-complete : ∀ {c s t} → inv c ⊢ t ⇒ s → c ⊢ s ⇒ t
  inv-complete {c} {s} {t} d = subst (λ x → x ⊢ s ⇒ t) (inv-inv c) (inv-sound d)
