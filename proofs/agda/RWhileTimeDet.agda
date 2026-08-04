{-# OPTIONS --safe #-}
------------------------------------------------------------------------
-- DETERMINISM of the timed semantics.
--
-- `c ⊢ σ ⇒ τ ∣ k` is a relation, so on its own it says τ is *a* possible
-- result.  R-WHILE is deterministic (expression evaluation and `rupd` are
-- functions, and the rules are syntax-directed), and this module proves it:
-- the result store AND the step count are uniquely determined.
--
-- Consequence (RWhileSIDet): the self-interpreter's answer is not merely
-- permitted by the semantics -- it is THE answer, and its cost is THE cost.
--
-- --safe, no postulates, no holes.
------------------------------------------------------------------------

module RWhileTimeDet where

open import Data.Nat using (ℕ; suc; _+_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; sym; trans; cong; cong₂; subst)

open import RWhileTime

private
  -- a test cannot be both true and false
  tf : ∀ {A : Set} → (just true) ≡ (just false) → A
  tf ()

  ft : ∀ {A : Set} → (just false) ≡ (just true) → A
  ft ()

⇒-det   : ∀ {c σ τ₁ τ₂ k₁ k₂} → c ⊢ σ ⇒ τ₁ ∣ k₁ → c ⊢ σ ⇒ τ₂ ∣ k₂
        → τ₁ ≡ τ₂ × k₁ ≡ k₂
Rest-det : ∀ {e D L f σ τ₁ τ₂ n₁ n₂} → Rest e D L f σ τ₁ n₁ → Rest e D L f σ τ₂ n₂
        → τ₁ ≡ τ₂ × n₁ ≡ n₂

⇒-det e-skip e-skip = refl , refl

⇒-det {σ = σ} (e-ass {x = x} {v = v₁} {u = u₁} ev₁ ru₁) (e-ass {v = v₂} {u = u₂} ev₂ ru₂) =
  cong (set σ x) u₁≡u₂ , refl
  where
    v₁≡v₂ : v₁ ≡ v₂
    v₁≡v₂ = just-injective (trans (sym ev₁) ev₂)
    u₁≡u₂ : u₁ ≡ u₂
    u₁≡u₂ = just-injective
              (trans (sym ru₁) (trans (cong (rupd (get σ x)) v₁≡v₂) ru₂))

⇒-det (e-seq {l = l₁} d₁ d₂) (e-seq {l = l₂} d₁′ d₂′) =
  proj₁ snd , cong suc (cong₂ _+_ (proj₂ fst) (proj₂ snd))
  where
    fst = ⇒-det d₁ d₁′
    snd = ⇒-det d₂ (subst (λ t → _ ⊢ t ⇒ _ ∣ l₂) (sym (proj₁ fst)) d₂′)

⇒-det (e-then _  dc _) (e-then _  dc′ _) = proj₁ h , cong suc (proj₂ h)
  where h = ⇒-det dc dc′
⇒-det (e-then t₁ _  _) (e-else t₂ _   _) = tf (trans (sym t₁) t₂)
⇒-det (e-else t₁ _  _) (e-then t₂ _   _) = ft (trans (sym t₁) t₂)
⇒-det (e-else _  dd _) (e-else _  dd′ _) = proj₁ h , cong suc (proj₂ h)
  where h = ⇒-det dd dd′

⇒-det (e-loop {n = n₁} _ dD₁ r₁) (e-loop {n = n₂} _ dD₂ r₂) =
  proj₁ rst , cong suc (cong₂ _+_ (proj₂ dD) (proj₂ rst))
  where
    dD  = ⇒-det dD₁ dD₂
    rst = Rest-det r₁ (subst (λ t → Rest _ _ _ _ t _ n₂) (sym (proj₁ dD)) r₂)

Rest-det (r-exit _)  (r-exit _)          = refl , refl
Rest-det (r-exit t₁) (r-iter t₂ _ _ _ _) = tf (trans (sym t₁) t₂)
Rest-det (r-iter t₁ _ _ _ _) (r-exit t₂) = ft (trans (sym t₁) t₂)

Rest-det (r-iter {m = m₁} _ dL₁ _ dD₁ r₁) (r-iter {k = k₂} {m = m₂} {n = n₂} _ dL₂ _ dD₂ r₂) =
  proj₁ rst , cong₂ _+_ (cong₂ _+_ (proj₂ dL) (proj₂ dD)) (proj₂ rst)
  where
    dL  = ⇒-det dL₁ dL₂
    dD  = ⇒-det dD₁ (subst (λ t → _ ⊢ t ⇒ _ ∣ m₂) (sym (proj₁ dL)) dD₂)
    rst = Rest-det r₁ (subst (λ t → Rest _ _ _ _ t _ n₂) (sym (proj₁ dD)) r₂)
