{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- THE INTERPRETER'S ANSWER IS THE ANSWER.
--
-- `RWhileSISim.si-linear` produces one run of `SI` ending in the right
-- state.  With `RWhileTimeDet.⇒-det` (the semantics is deterministic) this
-- upgrades to: EVERY terminating run of `SI` from the initial state ends in
-- exactly that state, and costs exactly as much -- so the bound is not just
-- "some run is fast", it is "the run is fast".
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIDet where

open import Data.Nat using (ℕ; _+_; _*_; _≤_)
open import Data.List using (List; []; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import RWhileTime
open import RWhileTimeDet using (⇒-det)
open import RWhileSIEnc using (⌜_⌝)
open import RWhileSIWf
open import RWhileSIStep using (embM)
open import RWhileSISim using (SI; CC; si-linear)

------------------------------------------------------------------------
-- Uniqueness: any run of SI on ⌜c⌝ agrees with the object semantics.

si-unique : ∀ {c σ τ k} → Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
          → ∀ {t j} → SI ⊢ embM (⌜ c ⌝ ∙ nil) nil σ ⇒ t ∣ j
          → t ≡ embM nil (⌜ c ⌝ ∙ nil) τ × j ≤ (CC (length σ) + 2) * k
si-unique {c} {σ} {τ} {k} wf ir d {t} {j} run =
  proj₁ agree , subst (λ i → i ≤ (CC (length σ) + 2) * k) (sym (proj₂ agree))
                      (proj₂ (proj₂ h))
  where
    h     = si-linear wf ir d
    agree = ⇒-det run (proj₁ (proj₂ h))

------------------------------------------------------------------------
-- ... and the object semantics itself is a function: the store the program
-- computes, and the number of steps it takes, are uniquely determined.

⇒-unique : ∀ {c σ τ₁ τ₂ k₁ k₂} → c ⊢ σ ⇒ τ₁ ∣ k₁ → c ⊢ σ ⇒ τ₂ ∣ k₂
         → τ₁ ≡ τ₂ × k₁ ≡ k₂
⇒-unique = ⇒-det
