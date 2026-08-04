{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- Linear-time interpretation of INVERSE programs, for free.
--
-- `RWhileTimeInv.inv-sound` says a program's inverse runs backwards at
-- exactly the forward cost, and `RWhileSISim.si-linear` says the fixed
-- R-WHILE self-interpreter `SI` simulates any object run within
-- `(CC M + 2)·k`.  Composing them: feeding `SI` the ENCODED INVERSE of a
-- program makes it undo that program's run -- still in linear time, with the
-- same constant.
--
-- This is the machine-checked form of "reversible languages come with
-- backwards execution at no asymptotic cost": one interpreter, one bound,
-- both directions.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileSIInv where

open import Data.Nat using (ℕ; _+_; _*_; _≤_)
open import Data.Nat.Properties using (+-mono-≤)
open import Data.List using (List; []; length)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import RWhileTime
open import RWhileSIEnc using (⌜_⌝; vmax)
open import RWhileSIWf
open import RWhileSIStep using (embM)
open import RWhileSISim using (SI; CC; si-linear)
open import RWhileTimeInv using (inv; inv-sound; Wf-inv; inR-inv)

private
  cast≤ : ∀ {a m n} → n ≡ m → a ≤ m → a ≤ n
  cast≤ eq le = subst (_ ≤_) (sym eq) le

------------------------------------------------------------------------
-- Interpreting the inverse program undoes the run, in the same time bound.

si-inverse-linear : ∀ {c σ τ k} → Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
  → Σ[ j ∈ ℕ ] (SI ⊢ embM (⌜ inv c ⌝ ∙ nil) nil τ ⇒ embM nil (⌜ inv c ⌝ ∙ nil) σ ∣ j
                × j ≤ (CC (length σ) + 2) * k)
si-inverse-linear {c} {σ} {τ} {k} wf ir d =
  proj₁ h , proj₁ (proj₂ h)
  , subst (λ M → proj₁ h ≤ (CC M + 2) * k) lt (proj₂ (proj₂ h))
  where
    lt : length τ ≡ length σ
    lt = ⇒-length ir d
    irτ : InR c τ
    irτ = cast≤ {vmax c} {length σ} {length τ} lt ir
    h : Σ[ j ∈ ℕ ] (SI ⊢ embM (⌜ inv c ⌝ ∙ nil) nil τ ⇒ embM nil (⌜ inv c ⌝ ∙ nil) σ ∣ j
                    × j ≤ (CC (length τ) + 2) * k)
    h = si-linear {inv c} {τ} {σ} {k} (Wf-inv wf) (inR-inv {c} {τ} irτ) (inv-sound wf ir d)

------------------------------------------------------------------------
-- Forward then backward: the same interpreter, run twice, returns the store
-- to where it started -- and the two runs together are still linear in `k`.

si-round-trip : ∀ {c σ τ k} → Wf c → InR c σ → c ⊢ σ ⇒ τ ∣ k
  → Σ[ j₁ ∈ ℕ ] Σ[ j₂ ∈ ℕ ]
      ( SI ⊢ embM (⌜ c ⌝ ∙ nil) nil σ ⇒ embM nil (⌜ c ⌝ ∙ nil) τ ∣ j₁
      × SI ⊢ embM (⌜ inv c ⌝ ∙ nil) nil τ ⇒ embM nil (⌜ inv c ⌝ ∙ nil) σ ∣ j₂
      × j₁ + j₂ ≤ (CC (length σ) + 2) * k + (CC (length σ) + 2) * k )
si-round-trip {c} {σ} {τ} {k} wf ir d =
  proj₁ fwd , proj₁ bwd
  , proj₁ (proj₂ fwd) , proj₁ (proj₂ bwd)
  , +-mono-≤ (proj₂ (proj₂ fwd)) (proj₂ (proj₂ bwd))
  where
    fwd = si-linear wf ir d
    bwd = si-inverse-linear wf ir d
